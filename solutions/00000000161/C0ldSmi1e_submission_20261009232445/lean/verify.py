#!/usr/bin/env python3
"""Cleanly rebuild and audit this Lean project using its pinned dependencies.

Requires Python 3 and the pinned Lean/Lake on PATH. Dependencies must already
be present in .lake/packages (for a fresh online checkout: lake exe cache get).
Only this project's generated .lake/build directory is removed.
"""

from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
LOG = ROOT / "verification.log"
SOURCES = ["Conjecture161/Arithmetic.lean", "Conjecture161.lean"]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.19.0"
EXPECTED_MANIFEST_SHA256 = "56f7aa9722d120b38ffe868179164054411be9398660939609cb8a0c55e48637"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(command, log):
    log.write("$ " + " ".join(command) + "\n")
    log.flush()
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write(result.stdout)
    log.flush()
    require(result.returncode == 0,
            "Command failed; see verification.log: " + " ".join(command))
    return result.stdout


def main():
    require((ROOT / "lean-toolchain").read_text().strip() == EXPECTED_TOOLCHAIN,
            "Unexpected Lean toolchain pin")
    manifest_bytes = (ROOT / "lake-manifest.json").read_bytes()
    require(hashlib.sha256(manifest_bytes).hexdigest() == EXPECTED_MANIFEST_SHA256,
            "Pinned dependency manifest was changed")
    manifest = json.loads(manifest_bytes)
    theorem_names = []
    for source in SOURCES:
        content = (ROOT / source).read_text()
        require(not re.search(r"\b(sorry|admit|native_decide|axiom|unsafe)\b", content),
                "Forbidden proof construct in " + source)
        theorem_names.extend("Conjecture161." + name
                             for name in re.findall(r"^theorem\s+(\w+)", content, re.M))
    audit = (ROOT / "Audit.lean").read_text()
    for directive in ("#check", "#print axioms"):
        covered = re.findall(r"^" + directive + r"\s+(\S+)\s*$", audit, re.M)
        require(sorted(covered) == sorted(theorem_names),
                "Audit does not cover exactly every submitted theorem: " + directive)

    with LOG.open("w") as log:
        version = run(["lean", "--version"], log)
        require("version 4.19.0," in version, "Wrong Lean binary on PATH")
        for package in manifest["packages"]:
            path = ROOT / ".lake" / "packages" / package["name"]
            require(path.exists(), "Missing dependency: " + package["name"])
            revision = run(["git", "-C", str(path), "rev-parse", "HEAD"], log).strip()
            require(revision == package["rev"], "Wrong dependency revision: " + package["name"])
            run(["git", "-C", str(path), "diff", "--quiet", "HEAD", "--"], log)
        build = ROOT / ".lake" / "build"
        require(not build.is_symlink(), "Refusing to clean a symlinked build directory")
        if build.exists():
            shutil.rmtree(build)
        log.write("Removed only this project's .lake/build for a clean project rebuild.\n")
        run(["lake", "build"], log)
        for source in ["lakefile.lean", *SOURCES]:
            run(["lake", "env", "lean", "-DwarningAsError=true", source], log)
        output = run(["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"], log)
        audited = set()
        for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
            dependencies = {item.strip() for item in axioms.split(",") if item.strip()}
            require(dependencies <= ALLOWED_AXIOMS,
                    "Disallowed axiom dependency of " + name + ": " + str(dependencies))
            audited.add(name)
        audited.update(re.findall(r"'([^']+)' does not depend on any axioms", output))
        require(audited == set(theorem_names), "Missing theorem axiom-audit results")
        log.write("PASS: clean build, every source strict, all 14 theorem types and axiom dependencies.\n")
    print("PASS: clean build; strict source checks; all 14 theorem types and axiom dependencies.")
    print("Detailed evidence: " + str(LOG))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print("FAIL: " + str(error), file=sys.stderr)
        sys.exit(1)
