#!/usr/bin/env python3
"""Reproduce the exact statement obstruction for conjecture00000007842."""
from __future__ import annotations
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
LEAN = ROOT / "lean4"
MATHLIB_URL = "https://github.com/leanprover-community/mathlib4.git"
MATHLIB_REV = "0df444a360eaa60ab8c11dca51a86af692955474"
NS = "Conjecture00000007842"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


def read_json(file: Path) -> dict:
    return json.loads(file.read_text(encoding="utf-8"))


def sanitized_environment() -> dict[str, str]:
    env = os.environ.copy()
    for key in ("GH_TOKEN", "GITHUB_TOKEN", "LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(key, None)
    env.update(MATHLIB_NO_CACHE_ON_UPDATE="1", PYTHONUTF8="1")
    return env


def run(command: list[str], cwd: Path = LEAN, timeout: int = 180) -> str:
    print("[RUN] " + subprocess.list2cmdline(command), flush=True)
    proc = subprocess.run(command, cwd=cwd, env=sanitized_environment(),
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, encoding="utf-8", errors="replace", timeout=timeout)
    require(proc.returncode == 0, f"Command failed with exit{proc.returncode}:\n{proc.stdout}")
    return proc.stdout


def preflight(repo: Path) -> tuple[dict, list[str]]:
    manifest = read_json(ROOT / "submission.json")
    data = (ROOT / "source.md").read_bytes().replace(b"\r\n", b"\n")
    require(hashlib.sha256(data).hexdigest() == manifest["source_sha256"], "Frozen SHA mismatch")
    require(hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest() == manifest["source_git_blob"],
            "Frozen Git-blob mismatch")
    current = repo / "conjectures" / "00000007842.md"
    require(current.read_bytes().replace(b"\r\n", b"\n") == data, "Current bilingual statement changed")
    require(run(["git", "-C", str(repo), "cat-file", "-t", manifest["source_git_blob"]], ROOT).strip() == "blob",
            "Frozen object absent or not a blob")
    require((LEAN / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1", "Wrong Lean pin")
    lakefile = (LEAN / "lakefile.lean").read_text(encoding="utf-8")
    require(MATHLIB_REV in lakefile and MATHLIB_URL in lakefile and "from path" not in lakefile,
            "Lake dependency is not the pinned Git Mathlib package")
    packages = read_json(LEAN / "lake-manifest.json")
    specs = packages.get("packages", [])
    require(specs and all(p.get("type") == "git" for p in specs), "Only fixed Git dependencies accepted")
    require(len({p["name"] for p in specs}) == len(specs), "Duplicate package names")
    mathlib = next((p for p in specs if p["name"] == "mathlib"), {})
    for key, value in {"type": "git", "url": MATHLIB_URL, "rev": MATHLIB_REV, "inputRev": MATHLIB_REV}.items():
        require(mathlib.get(key) == value, "Mathlib pin differs in field " + key)
    source = (LEAN / "Main.lean").read_text(encoding="utf-8")
    names = [NS + "." + n for n in re.findall(r"^theorem\s+(\w+)", source, re.M)]
    require(re.findall(r"^namespace\s+(\w+)", source, re.M) == [NS], "Unexpected namespace")
    require(names and len(set(names)) == len(names) and names == manifest["theorems"],
            "Public theorem inventory is incomplete/duplicated")
    commands = re.findall(r"^#print axioms ([\w.]+)\s*$", (LEAN / "Check.lean").read_text(encoding="utf-8"), re.M)
    require(commands == names, "Full public-theorem audit inventory mismatch")
    for file in (LEAN / "Main.lean", LEAN / "Check.lean"):
        require(not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_tac|elab|macro)\b",
                              file.read_text(encoding="utf-8")), "Forbidden source construct")
    print(f"[PASS] Exact bilingual blob, source hash, dependency pin, {len(names)} public theorem inventory")
    return packages, names


def materialized_dependencies(manifest: dict) -> None:
    for spec in manifest["packages"]:
        name, rev, url = spec["name"], spec["rev"], spec["url"]
        require(re.fullmatch(r"[\w-]+", name) is not None and re.fullmatch(r"[0-9a-f]{40}", rev) is not None,
                "Invalid fixed dependency specification")
        checkout = LEAN / ".lake" / "packages" / name
        require(run(["git", "-C", str(checkout), "rev-parse", "HEAD"], ROOT).strip() == rev,
                "Dependency HEAD mismatch for " + name)
        require(run(["git", "-C", str(checkout), "remote", "get-url", "origin"], ROOT).strip() == url,
                "Dependency origin mismatch for " + name)
        require(not run(["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=no"], ROOT).strip(),
                "Modified tracked dependency source for " + name)
    print("[PASS] Every materialized Git dependency has the exact revision, origin and clean tracked source")


def regression() -> None:
    # These numbers are NOT purported measurements of blanket time on any graph.
    with localcontext() as ctx:
        ctx.prec = 50
        limits = [Decimal(3).ln() / 2, (Decimal(3) / 2).ln()]
        require(all(a <= 1 for a in limits), "Logarithm numerical sanity check failed")
        values = [Fraction(4, 3), Fraction(7, 5), Fraction(2), Fraction(4)]
        for x in values:
            for a in limits:
                dx = Decimal(x.numerator) / Decimal(x.denominator)
                require(abs(dx - a) > Decimal(1) / 6, "Empty-neighborhood sample sanity check failed")
        print("[PASS]10 finite numerical sanity checks (NOT graph data or the infinite proof)")


def clean_project_build() -> None:
    # Remove only this project's generated build cache, never shared package caches.
    build = LEAN / ".lake" / "build"
    if build.exists():
        resolved = build.resolve()
        require(resolved == build.absolute() and resolved.is_relative_to(LEAN.resolve()),
                "Refuse recursive cache removal through a junction/symlink or outside this project")
        require(build.is_dir(), "Build-cache target is not a directory")
        shutil.rmtree(resolved)


def lean_checks(lake: str, names: list[str]) -> None:
    version = run([lake, "env", "lean", "--version"])
    require(re.search(r"\bversion4\.33\.1(?:[,)]|$)", version.replace(" ", "")) is not None,
            "Installed Lean must match exact release4.33.1")
    clean_project_build()
    print(run([lake, "build", "Main"]), end="", flush=True)
    print(run([lake, "env", "lean", "-DwarningAsError=true", "Main.lean"]), end="", flush=True)
    audit = run([lake, "env", "lean", "-DwarningAsError=true", "Check.lean"])
    print(audit, end="", flush=True)
    for name in names:
        empty = re.findall(r"^'" + re.escape(name) + r"' does not depend on any axioms\s*$", audit, re.M)
        footprint = re.findall(r"^'" + re.escape(name) + r"' depends on axioms:\s*\[([^]]*)\]", audit, re.M)
        require(len(empty) + len(footprint) == 1, "Missing/duplicate/malformed audit for " + name)
        if footprint:
            require({a.strip() for a in footprint[0].split(",") if a.strip()} <= ALLOWED,
                    "Unapproved transitive dependency in " + name)
    print(f"[PASS] Clean project build, warning-as-error replay, all{len(names)} transitive theorem audits")


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="backslashreplace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--skip-update", action="store_true")
    args = parser.parse_args()
    try:
        lake = shutil.which(args.lake)
        require(lake is not None, "Lake executable not found")
        manifest, names = preflight(args.repo.resolve())
        regression()
        if not args.skip_update:
            print(run([lake, "update"]), end="", flush=True)
        materialized_dependencies(manifest)
        lean_checks(lake, names)
        materialized_dependencies(manifest)
        print("[PASS] Complete local reproduction; no publication or organizer acceptance is asserted")
        return 0
    except (RuntimeError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print("[FAIL] " + str(error), file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
