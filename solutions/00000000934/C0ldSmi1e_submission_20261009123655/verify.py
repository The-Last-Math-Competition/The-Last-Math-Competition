#!/usr/bin/env python3
"""Rebuild, replay, and audit a frozen Lean project. Python standard library only."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
PREFIX = "TLMC-AUDIT-1\t"
TOOLCHAIN = "leanprover/lean4:v4.19.0\n"
CORE_MANIFEST_HASH = "41f401cdaea862da9247638deb6da15ded9ab350b13710ce7b71273ae8f6ff3e"
PACKAGE_PINS = {
    "mathlib": "c44e0c8ee63ca166450922a373c7409c5d26b00b",
    "plausible": "77e08eddc486491d7b9e470926b3dbe50319451a",
    "LeanSearchClient": "25078369972d295301f5a1e53c3e5850cf6d9d4c",
    "importGraph": "e6a9f0f5ee3ccf7443a0070f92b62f8db12ae82b",
    "proofwidgets": "c4919189477c3221e6a204008998b0d724f49904",
    "aesop": "5d50b08dedd7d69b3d9b3176e0d58a23af228884",
    "Qq": "fa4f7f15d97591a9cf3aa7724ba371c7fc6dda02",
    "batteries": "f5d04a9c4973d401c8c92500711518f7c656f034",
    "Cli": "02dbd02bc00ec4916e99b04b2245b30200e200d0",
}


class VerificationError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def load_json(path):
    try:
        return json.loads(Path(path).read_text())
    except (OSError, ValueError) as e:
        raise VerificationError(f"Cannot read JSON {path}: {e}") from e


def safe_file(root, relative):
    require(isinstance(relative, str) and relative, "Invalid relative file name")
    candidate = root / relative
    require(not Path(relative).is_absolute() and ".." not in Path(relative).parts,
            f"File escapes project: {relative}")
    require(candidate.is_file() and not candidate.is_symlink(), f"Missing or symlinked file: {relative}")
    require(candidate.resolve().is_relative_to(root.resolve()), f"File escapes project: {relative}")
    return candidate


def verify_hashes(root, hashes):
    require(isinstance(hashes, dict) and hashes, "Frozen file hash list is empty")
    for relative, expected in hashes.items():
        require(isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected),
                f"Invalid SHA-256 for {relative}")
        actual = hashlib.sha256(safe_file(root, relative).read_bytes()).hexdigest()
        require(actual == expected, f"Frozen file changed: {relative}")


def validate_manifest(manifest):
    require(isinstance(manifest, dict), "Dependency manifest must be an object")
    packages = manifest.get("packages")
    require(isinstance(packages, list) and len(packages) == 9, "Expected exactly nine pinned packages")
    actual = {}
    for package in packages:
        require(isinstance(package, dict), "Malformed dependency package")
        name = package.get("name")
        require(name in PACKAGE_PINS and name not in actual, f"Unexpected or duplicate dependency: {name}")
        require(package.get("type") == "git", f"Dependency {name} is not pinned to Git")
        actual[name] = package.get("rev")
    require(actual == PACKAGE_PINS, "Dependency revision pins differ from the frozen nine-package baseline")


def checkout_revision(directory):
    """Read dependency revision metadata without invoking or modifying Git."""
    gitdir = directory / ".git"
    require(gitdir.is_dir(), f"Dependency Git metadata unavailable: {directory}")
    head = (gitdir / "HEAD").read_text().strip()
    if head.startswith("ref: "):
        ref = head[5:]
        require(re.fullmatch(r"refs/[A-Za-z0-9_./-]+", ref) and ".." not in ref,
                "Invalid dependency HEAD reference")
        ref_file = gitdir / ref
        if ref_file.is_file():
            head = ref_file.read_text().strip()
        else:
            packed = (gitdir / "packed-refs").read_text().splitlines()
            matches = [line.split()[0] for line in packed if line.endswith(" " + ref)]
            require(len(matches) == 1, f"Cannot resolve dependency HEAD: {directory}")
            head = matches[0]
    require(re.fullmatch(r"[0-9a-f]{40}", head), f"Malformed dependency HEAD: {directory}")
    return head


def validate_dependencies(directory):
    paths = []
    for name, pin in PACKAGE_PINS.items():
        checkout = directory / name
        require(checkout.is_dir(), f"Missing dependency: {name}")
        require(checkout_revision(checkout) == pin, f"Installed dependency pin mismatch: {name}")
        status = subprocess.run(["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=no"],
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=120)
        require(status.returncode == 0 and not status.stdout.strip(), f"Dependency tracked source is dirty: {name}")
        compiled = checkout / ".lake" / "build" / "lib" / "lean"
        if compiled.is_dir():
            paths.append(str(compiled.resolve()))
    require((directory / "mathlib" / ".lake" / "build" / "lib" / "lean").is_dir(),
            "Mathlib compiled library is missing; install the pinned dependency cache first")
    return paths


def validate_python_runtime():
    require(sys.flags.optimize == 0 and not os.environ.get("PYTHONOPTIMIZE"),
            "Python optimization is forbidden: assertion-based frozen auxiliary checks must remain enabled")


def validate_original_audit(output, inventory, transitive_names, transitive_file):
    names = re.findall(r"(?m)^OWNED ([^\n]+)$", output)
    require(len(names) == len(set(names)) and set(names) == {x["name"] for x in inventory},
            "Frozen audit output omits or duplicates owned declarations")
    require(f"PASS: inspected {len(inventory)} owned declarations, including generated helpers" in output,
            "Frozen audit ownership summary missing")
    require(f"PASS: {len(transitive_names)} transitive declarations have no unsafe constant and only propext/Classical.choice/Quot.sound axioms" in output,
            "Frozen audit transitive summary missing")
    require("PASS: every owned declaration also passed Lean.collectAxioms independently" in output,
            "Frozen audit axiom summary missing")
    closure = transitive_file.read_text().splitlines()
    require(len(closure) == len(set(closure)) and set(closure) == set(transitive_names),
            "Frozen and independent transitive inventories differ")


def validate_version(output):
    require(re.search(r"^Lean \(version 4\.19\.0,", output) is not None,
            f"Expected Lean 4.19.0; received {output.strip()!r}")


def executable_source(text):
    """Remove nested Lean comments and string bodies, preserving token boundaries."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
            out.append(" ")
        elif quoted:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                quoted = False
                i += 1
            else:
                i += 1
            out.append(" ")
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            out.append(" ")
        elif text.startswith("--", i):
            newline = text.find("\n", i)
            i = len(text) if newline < 0 else newline
            out.append(" ")
        elif text[i] == '"':
            quoted = True
            i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    require(depth == 0 and not quoted, "Unterminated Lean comment or string")
    return "".join(out)


def source_policy(text):
    code = executable_source(text)
    banned = re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b", code)
    require(banned is None, f"Forbidden proof-source token: {banned.group(0) if banned else ''}")
    return code


def module_order(root, module_map):
    require(isinstance(module_map, dict) and module_map, "Owned module list is empty")
    imports = {}
    for module, relative in module_map.items():
        require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*", module),
                f"Invalid owned module name: {module}")
        require(relative == module.replace(".", "/") + ".lean", f"Unexpected module path: {relative}")
        code = source_policy(safe_file(root, relative).read_text())
        imports[module] = [m for line in re.findall(r"(?m)^\s*(?:public\s+|private\s+)?import\s+([^\n]+)", code)
                           for m in line.split() if m in module_map]
    ordered, pending = [], set(module_map)
    while pending:
        ready = sorted(m for m in pending if not (set(imports[m]) & pending))
        require(ready, "Cyclic owned module imports")
        ordered.extend(ready)
        pending.difference_update(ready)
    return ordered


def validate_source_inventory(root, modules, inspectors, supplemental):
    require(isinstance(supplemental, dict), "Invalid supplemental inspector registration")
    if supplemental:
        require(all(isinstance(p, str) and p.endswith(".lean") for p in supplemental),
                "Supplemental inspector is not a Lean source")
        verify_hashes(root, supplemental)
    registered = set(modules.values()) | set(inspectors) | set(supplemental)
    if (root / "lakefile.lean").is_file():
        registered.add("lakefile.lean")
    all_lean = {str(p.relative_to(root)) for p in root.rglob("*.lean")
                if not any(part.startswith(".") for part in p.relative_to(root).parts)}
    require(all_lean == registered, "Unregistered owned Lean source file")


def audit_source(modules):
    imports = "\n".join("import " + name for name in modules)
    strings = ", ".join(json.dumps(name) for name in sorted(modules))
    return imports + "\nimport Lean\n\n" + r'''
open Lean Elab Command in
run_cmd do
  let ownedModules : Array String := #[MODULE_STRINGS]
  let env ← getEnv
  let declarations := (env.constants.toList.toArray.filter fun pair =>
    match env.getModuleIdxFor? pair.1 with
    | none => false
    | some idx => ownedModules.contains (env.allImportedModuleNames[idx]!.toString))
      |>.qsort (fun a b => a.1.toString < b.1.toString)
  liftIO <| IO.println ("TLMC-AUDIT-1\t" ++ (Json.mkObj [
    ("event", toJson "begin"), ("modules", toJson ownedModules)]).compress)
  for (name, info) in declarations do
    let some idx := env.getModuleIdxFor? name | throwError "Missing defining module"
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let axioms ← liftCoreM <| Lean.collectAxioms name
    let sortedAxioms := (axioms.map Name.toString).qsort (· < ·)
    liftIO <| IO.println ("TLMC-AUDIT-1\t" ++ (Json.mkObj [
      ("event", toJson "declaration"), ("name", toJson name.toString),
      ("module", toJson env.allImportedModuleNames[idx]!.toString),
      ("kind", toJson kind), ("unsafe", toJson info.isUnsafe),
      ("axioms", toJson sortedAxioms)]).compress)
  let mut pending := declarations.map (·.1)
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let info ← getConstInfo name
    if info.isUnsafe then throwError "Unsafe transitive declaration: {name}"
    if let .axiomInfo _ := info then
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains name do
        throwError "Unapproved transitive axiom: {name}"
    for dependency in info.type.getUsedConstants do
      pending := pending.push dependency
    if let some body := info.value? (allowOpaque := true) then
      for dependency in body.getUsedConstants do
        pending := pending.push dependency
  let closure := (seen.toArray.map Name.toString).qsort (· < ·)
  liftIO <| IO.println ("TLMC-AUDIT-1\t" ++ (Json.mkObj [
    ("event", toJson "closure"), ("names", toJson closure)]).compress)
  liftIO <| IO.println ("TLMC-AUDIT-1\t" ++ (Json.mkObj [
    ("event", toJson "end"), ("count", toJson declarations.size)]).compress)
'''.replace("MODULE_STRINGS", strings).replace('\\t"', '\t"')


def parse_audit(output, modules, expected=None):
    lines = output.splitlines()
    require(len(lines) >= 4, "Missing or incomplete audit output")
    records = []
    for line in lines:
        require(line.startswith(PREFIX), "Malformed or unexpected audit output line")
        try:
            record = json.loads(line[len(PREFIX):])
        except ValueError as e:
            raise VerificationError("Malformed audit JSON") from e
        require(isinstance(record, dict), "Audit record is not an object")
        records.append(record)
    require(records[0] == {"event": "begin", "modules": sorted(modules)}, "Missing or incorrect audit header")
    require(records[-1] == {"event": "end", "count": len(records) - 3}, "Missing or incorrect audit footer")
    closure = records[-2]
    require(set(closure) == {"event", "names"} and closure["event"] == "closure", "Missing transitive closure record")
    names = closure["names"]
    require(isinstance(names, list) and names and all(isinstance(n, str) and n for n in names), "Malformed transitive closure")
    require(names == sorted(set(names)), "Duplicate or unsorted transitive closure")
    inventory = []
    seen = set()
    for record in records[1:-2]:
        require(set(record) == {"event", "name", "module", "kind", "unsafe", "axioms"}, "Malformed declaration record")
        require(record["event"] == "declaration", "Unexpected audit event")
        name = record["name"]
        require(isinstance(name, str) and name and name not in seen, "Missing or duplicate declaration name")
        seen.add(name)
        require(record["module"] in modules, "Declaration has an unowned defining module")
        require(record["kind"] in {"definition", "theorem", "opaque", "inductive", "constructor", "recursor"},
                f"Forbidden or invalid declaration kind: {name}")
        require(record["unsafe"] is False, f"Unsafe declaration: {name}")
        axioms = record["axioms"]
        require(isinstance(axioms, list) and all(isinstance(x, str) for x in axioms), "Malformed axiom list")
        require(axioms == sorted(set(axioms)), "Duplicate or unsorted axioms")
        require(set(axioms) <= ALLOWED_AXIOMS, f"Unapproved transitive axioms for {name}: {axioms}")
        inventory.append({"name": name, "module": record["module"], "kind": record["kind"]})
    require(inventory and inventory == sorted(inventory, key=lambda x: x["name"]), "Empty or unsorted declaration audit")
    require(set(x["module"] for x in inventory) == set(modules), "Owned module missing from declaration audit")
    require(seen <= set(names), "Owned declaration omitted from transitive closure")
    if expected is not None:
        require(inventory == expected, "Owned declaration inventory mismatch (missing, added, or altered helper)")
    return inventory


class Runner:
    def __init__(self, logdir):
        self.logdir = logdir
        self.index = 0
        logdir.mkdir(parents=True, exist_ok=False)

    def run(self, label, arguments, cwd, env=None):
        self.index += 1
        print(f"[{self.index}] {label}", flush=True)
        result = subprocess.run(arguments, cwd=cwd, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, timeout=1200)
        log = self.logdir / f"{self.index:03d}-{label}.log"
        log.write_text(result.stdout)
        (self.logdir / f"{self.index:03d}-{label}.command.json").write_text(json.dumps({
            "argv": list(map(str, arguments)), "cwd": str(cwd), "returncode": result.returncode,
        }, indent=2) + "\n")
        require(result.returncode == 0, f"{label} failed ({result.returncode}); see {log}")
        return result.stdout


def verify(root, lean, dependencies, logdir, discover=False, run_tests=True):
    validate_python_runtime()
    root = root.resolve()
    config = load_json(root / "verification.json")
    require(set(config) == {"schema", "core_sha256", "modules", "inspectors", "supplemental_inspectors", "auxiliary_python"}, "Unexpected verifier configuration schema")
    require(config["schema"] == 1, "Unsupported verifier schema")
    require(hashlib.sha256(safe_file(root, "CORE-SHA256SUMS.json").read_bytes()).hexdigest() == CORE_MANIFEST_HASH,
            "Frozen core manifest changed")
    original_core = load_json(root / "CORE-SHA256SUMS.json")
    require(config["core_sha256"] == {**original_core, "CORE-SHA256SUMS.json": CORE_MANIFEST_HASH},
            "Verifier hash inventory differs from the frozen core")
    verify_hashes(root, config["core_sha256"])
    require((root / "lean-toolchain").read_text() == TOOLCHAIN, "Wrong Lean toolchain pin")
    validate_manifest(load_json(root / "lake-manifest.json"))
    dependency_paths = validate_dependencies(dependencies)
    modules = config["modules"]
    owned_files = set(modules.values())
    require(owned_files <= set(config["core_sha256"]), "Owned Lean source is not frozen")
    validate_source_inventory(root, modules, config["inspectors"], config["supplemental_inspectors"])
    order = module_order(root, modules)
    expected = None if discover else load_json(root / "owned-declarations.json")
    runner = Runner(logdir)
    validate_version(runner.run("lean-version", [str(lean), "--version"], root))
    with tempfile.TemporaryDirectory(prefix="tlmc-proof-rebuild-") as temporary:
        temporary = Path(temporary)
        work = temporary / "project"
        work.mkdir()
        for relative in config["core_sha256"]:
            target = work / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root / relative, target)
        for relative in config["supplemental_inspectors"]:
            target = work / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root / relative, target)
        build = temporary / "lib"
        build.mkdir()
        env = dict(os.environ)
        env.pop("LEAN_SRC_PATH", None)
        env["LEAN_PATH"] = os.pathsep.join([str(build), *dependency_paths])
        runner.run("replay-lakefile", [str(lean), "-DwarningAsError=true", "-o", str(build / "lakefile.olean"), "lakefile.lean"], work, env)
        for module in order:
            destination = build / (module.replace(".", "/") + ".olean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            runner.run("build-" + module, [str(lean), "-DwarningAsError=true", "-o", str(destination), modules[module]], work, env)
            require(destination.is_file(), f"Compiler did not produce {module}")
        for module in order:
            runner.run("replay-" + module, [str(lean), "-DwarningAsError=true", modules[module]], work, env)
        audit = temporary / "VerifyOwnedDeclarations.lean"
        audit.write_text(audit_source(order))
        (logdir / "generated-audit-source.txt").write_text(audit.read_text())
        output = runner.run("declaration-audit", [str(lean), "-DwarningAsError=true", str(audit)], work, env)
        inventory = parse_audit(output, order, expected)
        transitive_names = json.loads(output.splitlines()[-2][len(PREFIX):])["names"]
        (logdir / "observed-declarations.json").write_text(json.dumps(inventory, indent=2) + "\n")
        for inspector in config["inspectors"]:
            inspector_output = runner.run("inspector-" + Path(inspector).stem,
                       [str(lean), "-DwarningAsError=true", "-o", str(build / (Path(inspector).stem + ".olean")), inspector], work, env)
            validate_original_audit(inspector_output, inventory, transitive_names, work / "logs" / "transitive-constants.txt")
        supplemental_outputs = {}
        (work / "review-logs").mkdir()
        for relative in sorted(config["supplemental_inspectors"]):
            source = work / relative
            destination = build / ("Supplemental" + source.stem + ".olean")
            supplemental_outputs[relative] = runner.run("supplemental-" + source.stem,
                [str(lean), "-DwarningAsError=true", "-o", str(destination), source.name], source.parent, env)
        if "independent-review/IndependentAudit.lean" in supplemental_outputs:
            independent_output = supplemental_outputs["independent-review/IndependentAudit.lean"]
            independent_owned = (work / "review-logs" / "independent-owned-constants.txt").read_text().splitlines()
            independent_transitive = (work / "review-logs" / "independent-transitive-constants.txt").read_text().splitlines()
            require(len(independent_owned) == len(set(independent_owned)) and set(independent_owned) == {x["name"] for x in inventory},
                    "Supplemental independent audit ownership inventory mismatch")
            require(len(independent_transitive) == len(set(independent_transitive)) and set(independent_transitive) == set(transitive_names),
                    "Supplemental independent audit transitive inventory mismatch")
            require(f"INDEPENDENT_PASS owned={len(inventory)} transitive={len(transitive_names)} axioms=" in independent_output,
                    "Supplemental independent audit summary missing")
            for output_file in (work / "review-logs").iterdir():
                shutil.copyfile(output_file, logdir / output_file.name)
        require(isinstance(config["auxiliary_python"], list), "Invalid auxiliary Python list")
        scripts = set(config["auxiliary_python"])
        shipped = {str(p.relative_to(root)) for p in root.rglob("*.py")
                   if not any(part.startswith(".") for part in p.relative_to(root).parts)}
        require(shipped == scripts | {"verify.py", "test_verifier.py"}, "Unregistered auxiliary Python code")
        packages = work / ".lake" / "packages"
        packages.mkdir(parents=True)
        for name in PACKAGE_PINS:
            (packages / name).symlink_to((dependencies / name).resolve(), target_is_directory=True)
        for script in sorted(scripts):
            runner.run("auxiliary-" + Path(script).stem, [sys.executable, str(safe_file(work, script))], work)
        lake = lean.with_name("lake")
        shell_env = dict(os.environ)
        shell_env["LAKE_BIN"] = str(lake)
        shell_env["PATH"] = str(lean.parent) + os.pathsep + shell_env.get("PATH", "")
        runner.run("original-verify-sh", ["bash", "verify.sh"], work, shell_env)
        require((work / "logs" / "transitive-constants.txt").is_file(), "Original audit failed to write transitive inventory")
        validate_original_audit((work / "logs" / "final-audit.log").read_text(), inventory, transitive_names,
                                work / "logs" / "transitive-constants.txt")
        shutil.copyfile(work / "logs" / "transitive-constants.txt", logdir / "original-transitive-constants.txt")
    if run_tests:
        runner.run("verifier-adversarial-tests", [sys.executable, str(safe_file(root, "test_verifier.py")),
                   "--lean", str(lean)], root)
    verify_hashes(root, config["core_sha256"])
    validate_source_inventory(root, modules, config["inspectors"], config["supplemental_inspectors"])
    if not discover:
        print(f"PASS: rebuilt and replayed {len(order)} proof modules; audited {len(inventory)} declarations; all auxiliary checks passed.")
    return inventory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--lean", type=Path, required=True, help="Lean 4.19.0 executable")
    parser.add_argument("--dependencies", type=Path, required=True, help="Directory with the nine pinned package checkouts")
    parser.add_argument("--logs", type=Path, required=True, help="New log directory; must not already exist")
    parser.add_argument("--discover", action="store_true", help="Review-only inventory discovery; does NOT certify a submission")
    args = parser.parse_args()
    try:
        verify(args.project, args.lean.resolve(), args.dependencies.resolve(), args.logs.resolve(), args.discover)
        if args.discover:
            print("DISCOVERY ONLY: review observed-declarations.json and freeze it as owned-declarations.json before certification.")
    except (VerificationError, OSError, subprocess.TimeoutExpired) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
