#!/usr/bin/env python3
"""Rebuild and audit frozen conjecture 1735 using Python's standard library.

Example: python3 verify.py --lake /path/to/lean-4.19.0/bin/lake
         --dependency-root /path/to/pinned/packages --output /new/results
The dependency root must already contain the nine pinned standard Git checkouts
and their Lean 4.19.0 build cache. This runner performs no dependency download.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PACKAGES = {"mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets",
            "aesop", "Qq", "batteries", "Cli"}
MATH_MODULES = {"Solution"}
LEAN_FILES = {"Solution.lean", "Audit.lean", "Inspect.lean"}
PROJECT_FILES = LEAN_FILES | {"lakefile.toml", "lake-manifest.json", "lean-toolchain"}
FROZEN_SOLUTION_SHA256 = "9dc02949de0879de546631832c1d55c75cb8d0f6df0222f0ec3748afc7daddb7"
INPUT_FILES = {"ORIGINAL.md", "verify.py", "test_verify.py",
               "verification/compiled-inventory.json",
               "verification/pinned-dependencies.json", "verification/author-freeze.json"} | {
                   "lean/" + name for name in PROJECT_FILES}
ROW_KEYS = {"name", "module", "kind", "unsafe", "role", "type", "transitive_axioms", "direct_constants"}
# Exact execution artifacts from the independently rebuilt frozen source. No name-pattern exemption.
COMPILER_ARTIFACTS = {'Conjecture1735.scaleSolution._cstage1', 'Conjecture1735.solutionCount._closed_1._cstage2', 'Conjecture1735.scaleSolution._cstage2', 'Conjecture1735.solutionCount._cstage1', 'Conjecture1735.solutionCount._cstage2'}
EXECUTION_AXIOMS = ALLOWED_AXIOMS | {"lcProof"}
KINDS = {"definition", "theorem", "opaque", "quotient", "constructor", "recursor", "inductive"}
FORBIDDEN = re.compile(r"\b(sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by|"
                       r"extern|run_cmd|elab|macro|initialize|declare_syntax_cat)\b")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def load_json(path):
    # Duplicate JSON object keys would otherwise silently override prior values.
    def unique_pairs(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("Duplicate JSON key: " + key)
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique_pairs)


def sorted_names(value, label):
    if not isinstance(value, list) or any(not isinstance(x, str) or not x for x in value):
        raise ValueError("Invalid " + label)
    if len(set(value)) != len(value):
        raise ValueError("Duplicate " + label)
    return sorted(value)


def normalized_inventory(rows):
    if not isinstance(rows, list) or not rows:
        raise ValueError("Expected a nonempty compiled Solution declaration inventory")
    result = {}
    for row in rows:
        if not isinstance(row, dict) or set(row) != ROW_KEYS:
            raise ValueError("Incorrect compiled declaration schema")
        name = row["name"]
        if not isinstance(name, str) or not name or name in result:
            raise ValueError("Missing or duplicate compiled declaration name")
        if row["module"] not in MATH_MODULES or row["kind"] not in KINDS:
            raise ValueError("Unexpected module, declaration kind, or authored axiom")
        execution = name in COMPILER_ARTIFACTS
        if row["unsafe"] is not execution:
            raise ValueError("Unsafe authored declaration or changed compiler safety")
        if row["role"] != ("compiler_execution" if execution else "kernel_mathematics"):
            raise ValueError("Incorrect mathematical/compiler role")
        if execution:
            if row["module"] != "Solution" or row["kind"] != "definition":
                raise ValueError("Changed compiler artifact identity")
        elif row["kind"] == "axiom":
            raise ValueError("Authored axiom declaration")
        axioms = sorted_names(row["transitive_axioms"], "transitive axiom list")
        if not set(axioms) <= (EXECUTION_AXIOMS if execution else ALLOWED_AXIOMS):
            raise ValueError("Disallowed transitive axiom dependency")
        if not isinstance(row["type"], str) or not row["type"].strip():
            raise ValueError("Missing declaration type")
        result[name] = {**row, "transitive_axioms": axioms,
                        "direct_constants": sorted_names(row["direct_constants"], "direct constants")}
    if {row["module"] for row in result.values()} != MATH_MODULES:
        raise ValueError("Missing mathematical module in compiled inventory")
    if {name for name, row in result.items() if row["unsafe"]} != COMPILER_ARTIFACTS:
        raise ValueError("Changed compiler artifact set")
    # Local graph control supplements the Lean traversal of ALL imported edges.
    seen = set()
    todo = [name for name, row in result.items() if not row["unsafe"]]
    while todo:
        name = todo.pop()
        if name in seen or name not in result:
            continue
        seen.add(name)
        row = result[name]
        if row["unsafe"]:
            raise ValueError("Unsafe proof dependency in owned declaration graph")
        todo.extend(row["direct_constants"])
    return result


def validate_closure(closure, inventory):
    rows = normalized_inventory(inventory)
    keys = {"root_names", "reachable_constant_names", "reachable_constant_count",
            "unsafe_count", "axioms", "edge_sources"}
    if not isinstance(closure, dict) or set(closure) != keys:
        raise ValueError("Incorrect proof dependency closure schema")
    roots = sorted_names(closure["root_names"], "proof dependency roots")
    reachable = sorted_names(closure["reachable_constant_names"], "reachable constants")
    if roots != sorted(name for name, row in rows.items() if not row["unsafe"]):
        raise ValueError("Missing safe mathematical proof dependency root")
    if not set(roots) <= set(reachable) or set(reachable) & COMPILER_ARTIFACTS:
        raise ValueError("Unsafe or missing proof dependency")
    if (type(closure["unsafe_count"]) is not int or closure["unsafe_count"] != 0 or
            type(closure["reachable_constant_count"]) is not int or
            closure["reachable_constant_count"] != len(reachable)):
        raise ValueError("Incorrect proof dependency closure count")
    if not set(sorted_names(closure["axioms"], "proof foundations")) <= ALLOWED_AXIOMS:
        raise ValueError("Forbidden proof foundation")
    if closure["edge_sources"] != ["types", "values_including_theorem_proofs"]:
        raise ValueError("Incomplete proof dependency edge coverage")


def validate_inventory(actual, expected):
    if normalized_inventory(actual) != normalized_inventory(expected):
        raise ValueError("Compiled declarations differ from the frozen inventory")


def scan_source(source):
    match = FORBIDDEN.search(source)
    if match:
        raise ValueError("Forbidden source token: " + match.group())


def validate_pins(pins, manifest):
    rows = pins.get("packages")
    if not isinstance(rows, list) or len(rows) != 9:
        raise ValueError("Expected nine pinned dependencies")
    if {r.get("name") for r in rows} != PACKAGES:
        raise ValueError("Unexpected or duplicate dependency")
    if pins != manifest:
        raise ValueError("Pinned dependency manifests disagree")
    for row in rows:
        if row.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", row.get("rev", "")):
            raise ValueError("Expected exact Git dependency revision")
    return rows


def validate_inputs(base, frozen):
    inputs = frozen["source_sha256"]
    if set(inputs) != INPUT_FILES:
        raise ValueError("Unexpected source-manifest file set")
    for name, digest in inputs.items():
        if sha(base / name) != digest:
            raise ValueError("Frozen input identity mismatch: " + name)
    if {str(p.relative_to(base / "lean")) for p in (base / "lean").rglob("*.lean")
        if ".lake" not in p.relative_to(base / "lean").parts} != LEAN_FILES:
        raise ValueError("Unexpected or missing authored Lean source")
    if (base / "lean/lean-toolchain").read_text().strip() != "leanprover/lean4:v4.19.0":
        raise ValueError("Lean 4.19.0 toolchain required")
    scan_source((base / "lean/Solution.lean").read_text())
    scan_source((base / "lean/Inspect.lean").read_text())
    author = load_json(base / "verification/author-freeze.json")
    if frozen.get("candidate") != "00000001735" or author.get("candidate") != "00000001735":
        raise ValueError("Unexpected conjecture identity")
    if sha(base / "lean/Solution.lean") != FROZEN_SOLUTION_SHA256:
        raise ValueError("Frozen mathematical source identity mismatch")
    for name in ["Solution.lean", "Inspect.lean"]:
        if sha(base / "lean" / name) != author["sha256"][name]:
            raise ValueError("Author-frozen mathematical input mismatch: " + name)
    return inputs


class Recorder:
    def __init__(self, out, project, env):
        self.out, self.project, self.env = out, project, env
        self.records = []

    def run(self, label, argv):
        dest = self.out / label
        dest.mkdir()
        record = {"label": label, "argv": argv, "cwd": str(self.project),
                  "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
        stdout, stderr = b"", b""
        try:
            proc = subprocess.run(argv, cwd=self.project, env=self.env, capture_output=True)
            stdout, stderr = proc.stdout, proc.stderr
            record["exit_code"] = proc.returncode
        except OSError as error:
            record.update({"exit_code": None, "launch_error": str(error)})
        record.update({"completed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                       "stdout": stdout.decode(errors="replace"),
                       "stderr": stderr.decode(errors="replace")})
        self.records.append(record)
        write_json(dest / "command.json", record)
        (dest / "stdout.txt").write_bytes(stdout)
        (dest / "stderr.txt").write_bytes(stderr)
        print(label, "PASS" if record["exit_code"] == 0 else "FAIL", flush=True)
        if record["exit_code"] != 0:
            raise RuntimeError("Command failed: " + label + "; see " + str(dest))
        return record["stdout"]


def check_pins(stage, pins, project, recorder):
    evidence = []
    for pin in pins:
        path = project / ".lake/packages" / pin["name"]
        rev = recorder.run(stage + "-revision-" + pin["name"],
                           ["git", "-C", str(path), "rev-parse", "HEAD"]).strip()
        dirty = recorder.run(stage + "-tracked-" + pin["name"],
                             ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"])
        if rev != pin["rev"] or dirty:
            raise ValueError("Wrong revision or modified dependency: " + pin["name"])
        evidence.append({"name": pin["name"], "revision": rev, "tracked_clean": True})
    write_json(recorder.out / ("dependencies-" + stage + ".json"), evidence)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="New directory for all execution records")
    parser.add_argument("--lake", default="lake", help="Lake executable for Lean 4.19.0")
    parser.add_argument("--dependency-root", type=Path, help="Directory containing the nine standard checkouts")
    args = parser.parse_args(argv)
    base = Path(__file__).resolve().parent
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="tlmc1735-verification-"))
    if args.output:
        out.mkdir(parents=True, exist_ok=False)
    print("Execution records:", out, flush=True)
    project = out / "fresh-project"
    project.mkdir()
    env = os.environ.copy()
    removed = sorted(k for k in env if k.startswith(("LEAN_", "LAKE_")) or k == "ELAN_TOOLCHAIN")
    for key in removed:
        env.pop(key)
    # Avoid optional Git index writes and Python startup-path/assertion overrides.
    for key in list(env):
        if key.startswith("PYTHON"):
            env.pop(key)
            removed.append(key)
    env["GIT_OPTIONAL_LOCKS"] = "0"
    recorder = Recorder(out, project, env)
    report = {"result": "FAIL", "candidate": "00000001735", "records": recorder.records,
              "removed_environment_variable_names": sorted(removed), "errors": [],
              "maintainer_acceptance": False}
    pins = None
    frozen = None
    dependencies_checked_before = False
    source_manifest_sha = None
    try:
        frozen = load_json(base / "verification/source-manifest.json")
        source_manifest_sha = sha(base / "verification/source-manifest.json")
        inputs = validate_inputs(base, frozen)
        report["source_sha256"] = inputs
        pins = validate_pins(load_json(base / "verification/pinned-dependencies.json"),
                             load_json(base / "lean/lake-manifest.json"))
        expected = load_json(base / "verification/compiled-inventory.json")
        normalized_inventory(expected)
        for name in PROJECT_FILES:
            shutil.copyfile(base / "lean" / name, project / name)
        (project / ".lake/packages").mkdir(parents=True)
        (project / "logs").mkdir()
        root = (args.dependency_root or base / "lean/.lake/packages").resolve(strict=True)
        for pin in pins:
            dependency = (root / pin["name"]).resolve(strict=True)
            (project / ".lake/packages" / pin["name"]).symlink_to(dependency, target_is_directory=True)
        report["dependency_root"] = str(root)
        check_pins("before", pins, project, recorder)
        dependencies_checked_before = True
        version = recorder.run("lean-version", [args.lake, "env", "lean", "--version"])
        if "version 4.19.0," not in version:
            raise ValueError("Lean 4.19.0 required")
        recorder.run("fresh-full-build", [args.lake, "build"])
        for module in ["Solution", "Inspect", "Audit"]:
            recorder.run("strict-" + module, [args.lake, "env", "lean", "-DwarningAsError=true", module + ".lean"])
        actual = load_json(project / "logs/declarations.json")
        validate_inventory(actual, expected)
        write_json(out / "compiled-inventory.json", actual)
        closure = load_json(project / "logs/proof-dependency-closure.json")
        validate_closure(closure, actual)
        write_json(out / "proof-dependency-closure.json", closure)
        report.update({"fresh_authored_build": True, "compiled_declaration_count": len(actual),
                       "safe_mathematical_declaration_count": sum(not r["unsafe"] for r in actual),
                       "compiler_execution_artifact_count": sum(r["unsafe"] for r in actual),
                       "compiler_unsafe_placeholder_count": sum(r["unsafe"] and r["kind"] == "axiom" for r in actual),
                       "proof_dependency_closure_count": closure["reachable_constant_count"],
                       "unsafe_proof_dependencies": closure["unsafe_count"],
                       "proof_dependency_edge_sources": closure["edge_sources"], "all_types_and_direct_constants_match": True,
                       "allowed_transitive_axioms": sorted(ALLOWED_AXIOMS),
                       "strict_modules": ["Solution", "Inspect", "Audit"]})
    except Exception as error:
        report["errors"].append(type(error).__name__ + ": " + str(error))
    finally:
        if dependencies_checked_before:
            try:
                check_pins("after", pins, project, recorder)
                report["pins_clean_before_and_after"] = True
            except Exception as error:
                report["errors"].append("Postcheck: " + type(error).__name__ + ": " + str(error))
        if frozen is not None:
            try:
                validate_inputs(base, frozen)
                if sha(base / "verification/source-manifest.json") != source_manifest_sha:
                    raise ValueError("Source manifest changed during verification")
                for name in PROJECT_FILES:
                    if (project / name).exists() and sha(project / name) != frozen["source_sha256"]["lean/" + name]:
                        raise ValueError("Fresh-project input changed: " + name)
                report["inputs_unchanged"] = True
            except Exception as error:
                report["errors"].append("Postcheck: " + type(error).__name__ + ": " + str(error))
        if not report["errors"]:
            report["result"] = "PASS"
        write_json(out / "result.json", report)
        shutil.copyfile(Path(__file__), out / "verify.py")
        files = {str(p.relative_to(out)): sha(p) for p in out.rglob("*")
                 if p.is_file() and ".lake" not in p.relative_to(out).parts and p.name != "SHA256SUMS.json"}
        write_json(out / "SHA256SUMS.json", files)
    print(report["result"] + ": " + ("fresh build, strict replay, complete declaration audit, and pinned dependencies"
                                     if not report["errors"] else "; ".join(report["errors"])), flush=True)
    return 0 if report["result"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
