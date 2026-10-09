#!/usr/bin/env python3
"""Offline verification of this standalone Lean project; never edits dependencies."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
LOGS = ROOT / "validation"
SOURCE_FILES = [
    "Conjecture7788/HullMeasurable.lean",
    "Conjecture7788/GenericRate.lean",
    "Conjecture7788.lean",
    "Audit.lean",
]
EXPECTED_PINS = {
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
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COMMANDS = []


def demand(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(label, args):
    completed = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    (LOGS / f"{label}.stdout").write_text(completed.stdout)
    (LOGS / f"{label}.stderr").write_text(completed.stderr)
    COMMANDS.append({"label": label, "args": args, "cwd": str(ROOT),
                     "returncode": completed.returncode})
    (LOGS / "commands.json").write_text(json.dumps(COMMANDS, indent=2) + "\n")
    demand(completed.returncode == 0, f"Command failed: {label}; see validation logs")
    return completed.stdout


def check_hashes():
    manifest = json.loads((ROOT / "SOURCE_HASHES.json").read_text())
    for relative, expected in manifest.items():
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        demand(actual == expected, f"Source hash mismatch: {relative}")
    return manifest


def main():
    LOGS.mkdir(exist_ok=True)
    demand(shutil.which("lake") is not None, "Put Lean 4.19.0 lake/lean on PATH first")
    frozen = check_hashes()
    demand((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.19.0",
           "Unexpected Lean toolchain")
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    demand({p["name"]: p["rev"] for p in packages} == EXPECTED_PINS,
           "Dependency manifest is not the exact nine-pin manifest")
    for package in packages:
        name = package["name"]
        directory = ROOT / ".lake" / "packages" / name
        demand(directory.is_dir(), f"Missing dependency {name}; prepare pinned dependencies first")
        head = run(f"dependency-{name}-head", ["git", "-C", str(directory), "rev-parse", "HEAD"])
        status = run(f"dependency-{name}-status", ["git", "-C", str(directory), "status",
                                                 "--porcelain", "--untracked-files=all"])
        demand(head.strip() == EXPECTED_PINS[name], f"Wrong dependency revision: {name}")
        demand(status == "", f"Dirty dependency checkout: {name}")
    version = run("lean-version", ["lake", "env", "lean", "--version"])
    demand("version 4.19.0" in version, "Unexpected Lean executable version")
    names = []
    for relative in SOURCE_FILES[:-1]:
        source = (ROOT / relative).read_text()
        namespace = "GenericRate" if relative.endswith("GenericRate.lean") else "Conjecture7788"
        demand(not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", source),
               f"Prohibited proof placeholder or bypass in {relative}")
        names.extend(f"{namespace}.{m.group(1)}" for m in re.finditer(
            r"^(?:noncomputable )?(?:lemma|theorem|instance|def|abbrev) ([A-Za-z0-9_]+)", source, re.M))
    demand(names == (ROOT / "DECLARATIONS.txt").read_text().splitlines(),
           "Declaration inventory mismatch")
    audit = (ROOT / "Audit.lean").read_text()
    demand(re.findall(r"^#check (\S+)$", audit, re.M) == names, "Type audit inventory mismatch")
    demand(re.findall(r"^#print axioms (\S+)$", audit, re.M) == names,
           "Axiom audit inventory mismatch")
    # Remove only this project's generated build products; never traverse package links.
    build = ROOT / ".lake" / "build"
    demand(not build.is_symlink(), "Refusing to remove symlinked build directory")
    if build.exists():
        shutil.rmtree(build)
    run("clean-build", ["lake", "build"])
    audit_output = ""
    for index, relative in enumerate(SOURCE_FILES):
        output = run(f"warning-replay-{index + 1}",
                     ["lake", "env", "lean", "-DwarningAsError=true", relative])
        if relative == "Audit.lean":
            audit_output = output
    audited = {}
    for name, axiom_text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit_output):
        audited[name] = {a.strip() for a in axiom_text.split(",") if a.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", audit_output):
        audited[name] = set()
    demand(set(audited) == set(names), "Axiom output does not cover every named declaration")
    for name, axioms in audited.items():
        demand(axioms <= ALLOWED_AXIOMS, f"Non-whitelisted axiom in {name}: {axioms}")
    demand(check_hashes() == frozen, "Source manifest changed during verification")
    summary = {
        "result": "PASS", "named_declarations": len(names), "authored_lean_sources": SOURCE_FILES,
        "dependency_pins": EXPECTED_PINS,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "axioms_by_declaration": {n: sorted(audited[n]) for n in names},
        "source_hashes": frozen,
        "auxiliary_computation": "None. All mathematical assertions are proved symbolically in Lean.",
    }
    (LOGS / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"PASS: clean build, four warning-as-error replays, {len(names)} declaration audits, nine clean pinned dependencies.")


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
