#!/usr/bin/env python3
"""Reproduce the Lean evidence for TLMC conjecture 00000000154.

Python standard library only. The program reads this package's known sources;
it validates the frozen organizer source through local Git, verifies the pinned
Lean/Mathlib configuration, builds and replays the Lean source, and audits its
advertised theorems. It does not build LaTeX, create a PDF, write Git history,
or perform any GitHub operation.
"""
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

ROOT = Path(__file__).resolve().parent
LEAN_DIR = ROOT / "lean4"
CID = "00000000154"
SOURCE_COMMIT = "95acb520ec5607c826b8a997b1ef2fc82d6f7c57"
SOURCE_PATH = f"conjectures/{CID}.md"
SOURCE_BLOB = "5d2fb2e814a4c521d2ace36034863cc8ec6fe836"
SOURCE_SHA256 = "694c389d34ad78b41caae8ad4e1f414fa0541e6b19b81aeab432466039dc87c1"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
MATHLIB_URL = "https://github.com/leanprover-community/mathlib4.git"
MATHLIB_TAG = "v4.33.1"
MATHLIB_REV = "0df444a360eaa60ab8c11dca51a86af692955474"
THEOREMS = [
    "TLMC154.numDerangements_pos_add_two",
    "TLMC154.numDerangements_even_ge_two_not_prime",
    "TLMC154.numDerangements_even_not_prime",
    "TLMC154.fin_even_derangements_card_not_prime",
    "TLMC154.fin_all_even_derangements_card_not_prime",
    "TLMC154.evenPrimeDerangementIndices_eq_empty",
    "TLMC154.evenPrimeDerangementIndices_not_infinite",
]
AXIOMS = {
    "TLMC154.numDerangements_pos_add_two": "[propext, Quot.sound]",
    "TLMC154.numDerangements_even_ge_two_not_prime": "[propext, Quot.sound]",
    "TLMC154.numDerangements_even_not_prime": "[propext, Quot.sound]",
    "TLMC154.fin_even_derangements_card_not_prime": "[propext, Classical.choice, Quot.sound]",
    "TLMC154.fin_all_even_derangements_card_not_prime": "[propext, Classical.choice, Quot.sound]",
    "TLMC154.evenPrimeDerangementIndices_eq_empty": "[propext, Classical.choice, Quot.sound]",
    "TLMC154.evenPrimeDerangementIndices_not_infinite": "[propext, Classical.choice, Quot.sound]",
}


def need(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def run(command: list[str], *, cwd: Path | None = None, env: dict[str, str] | None = None,
        timeout: int = 900) -> str:
    print("[RUN] " + subprocess.list2cmdline(command), flush=True)
    result = subprocess.run(command, cwd=str(cwd) if cwd else None, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            encoding="utf-8", errors="replace", timeout=timeout, check=False)
    if result.stdout:
        print(result.stdout, end="" if result.stdout.endswith("\n") else "\n", flush=True)
    print(f"[EXIT] {result.returncode}", flush=True)
    need(result.returncode == 0, f"Command failed with exit code {result.returncode}.")
    return result.stdout


def checkout(default: Path | None) -> Path:
    if default is not None:
        return default.resolve()
    for candidate in (ROOT, *ROOT.parents):
        if (candidate / ".git").exists():
            return candidate
    raise RuntimeError("No Git checkout ancestor found; pass --repo explicitly.")


def manifest() -> dict:
    return json.loads((LEAN_DIR / "lake-manifest.json").read_text(encoding="utf-8"))


def static_preflight() -> None:
    for relative in ["README.md", "main.tex", "reproduce.py", "submission.json",
                     "lean4/lakefile.lean", "lean4/lean-toolchain", "lean4/lake-manifest.json",
                     "lean4/Main.lean", "lean4/Check.lean"]:
        need((ROOT / relative).is_file(), f"Missing required file: {relative}")
    need((LEAN_DIR / "lean-toolchain").read_text(encoding="utf-8").strip() == TOOLCHAIN,
         "lean-toolchain is not pinned to Lean 4.33.1.")
    lakefile = (LEAN_DIR / "lakefile.lean").read_text(encoding="utf-8")
    need(MATHLIB_URL in lakefile and f'@ "{MATHLIB_TAG}"' in lakefile,
         "lakefile.lean does not request the pinned Mathlib tag.")
    submission = json.loads((ROOT / "submission.json").read_text(encoding="utf-8"))
    need(submission.get("id") == CID, "submission id mismatch.")
    need(submission.get("source_commit") == SOURCE_COMMIT, "source commit mismatch.")
    need(submission.get("source_git_blob") == SOURCE_BLOB, "source Git blob mismatch.")
    need(submission.get("source_sha256") == SOURCE_SHA256, "source SHA-256 mismatch.")
    need(submission.get("theorems") == THEOREMS, "theorem list must match this audit.")
    check = (LEAN_DIR / "Check.lean").read_text(encoding="utf-8")
    prints = re.findall(r"^#print axioms ([A-Za-z0-9_.]+)\s*$", check, re.MULTILINE)
    need(prints == THEOREMS, "Check.lean must audit every advertised theorem, in order.")
    main = (LEAN_DIR / "Main.lean").read_text(encoding="utf-8")
    forbidden = {"sorry": r"^\s*sorry\b", "admit": r"^\s*admit\b",
                 "custom axiom": r"^\s*axiom\b", "native_decide": r"\bnative_decide\b",
                 "unsafe": r"\bunsafe\b"}
    for label, pattern in forbidden.items():
        need(re.search(pattern, main, re.MULTILINE) is None,
             f"Forbidden construct detected by static preflight: {label}.")
    data = manifest()
    entries = [p for p in data.get("packages", []) if p.get("name") == "mathlib"]
    need(data.get("name") == "tlmc154Submission" and len(entries) == 1,
         "Lake manifest lacks the expected package/Mathlib entry.")
    mathlib = entries[0]
    need(mathlib.get("url") == MATHLIB_URL and mathlib.get("inputRev") == MATHLIB_TAG
         and mathlib.get("rev") == MATHLIB_REV, "Mathlib manifest pin mismatch.")
    print("[PASS] static package, source-map, dependency, and audit preflight", flush=True)


def source_preflight(repo: Path, timeout: int) -> None:
    need((repo / ".git").exists(), "--repo is not a Git checkout.")
    blob = run(["git", "-C", str(repo), "show", f"{SOURCE_COMMIT}:{SOURCE_PATH}"], timeout=timeout)
    # Git text output is decoded only after the bytes below have been fingerprinted.
    raw = subprocess.run(["git", "-C", str(repo), "show", f"{SOURCE_COMMIT}:{SOURCE_PATH}"],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout, check=True).stdout
    need(hashlib.sha256(raw).hexdigest() == SOURCE_SHA256, "frozen source SHA-256 mismatch.")
    actual_blob = run(["git", "-C", str(repo), "rev-parse", f"{SOURCE_COMMIT}:{SOURCE_PATH}"],
                      timeout=timeout).strip()
    need(actual_blob == SOURCE_BLOB, "frozen source Git blob mismatch.")
    working = (repo / SOURCE_PATH).read_bytes().replace(b"\r\n", b"\n")
    need(hashlib.sha256(working).hexdigest() == SOURCE_SHA256,
         "working-tree source differs from the frozen text after CRLF normalization.")
    need("Prime values of derangement numbers" in blob, "unexpected frozen source content.")
    print("[PASS] frozen source commit, blob, and SHA-256", flush=True)


def resolve_lake(value: str) -> str:
    candidate = Path(value)
    if candidate.is_file():
        return str(candidate.resolve())
    found = shutil.which(value)
    need(found is not None, "Lake not found; pass --lake from Lean 4.33.1.")
    return str(Path(found).resolve())


def verify_mathlib_checkout(timeout: int) -> None:
    directory = LEAN_DIR / ".lake" / "packages" / "mathlib"
    need(directory.is_dir(), "Mathlib dependency is not materialized.")
    actual = run(["git", "-C", str(directory), "rev-parse", "HEAD"], timeout=timeout).strip()
    need(actual == MATHLIB_REV, "materialized Mathlib commit does not match the manifest pin.")


def lean_preflight_and_build(lake: str, timeout: int, do_update: bool) -> None:
    env = os.environ.copy()
    env["PATH"] = str(Path(lake).parent) + os.pathsep + env.get("PATH", "")
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    # Avoid making verification depend on Mathlib's optional automatic cache-fetch hook.
    # With no prebuilt cache, Lake can source-build the pinned dependencies instead.
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    run([lake, "--version"], cwd=LEAN_DIR, env=env, timeout=timeout)
    version = run([lake, "env", "lean", "--version"], cwd=LEAN_DIR, env=env, timeout=timeout)
    need(re.search(r"\bversion 4\.33\.1(?:[,\)\s]|$)", version) is not None,
         "Detected Lean is not version 4.33.1.")
    if do_update:
        run([lake, "update"], cwd=LEAN_DIR, env=env, timeout=timeout)
    static_preflight()
    verify_mathlib_checkout(timeout)
    run([lake, "build"], cwd=LEAN_DIR, env=env, timeout=timeout)
    run([lake, "env", "lean", "-DwarningAsError=true", "Main.lean"], cwd=LEAN_DIR, env=env, timeout=timeout)
    audit = run([lake, "env", "lean", "-DwarningAsError=true", "Check.lean"], cwd=LEAN_DIR, env=env, timeout=timeout)
    need("sorryAx" not in audit, "axiom audit contains sorryAx.")
    for theorem in THEOREMS:
        expected = f"'{theorem}' depends on axioms: {AXIOMS[theorem]}"
        need(expected in audit.splitlines(), f"missing or unexpected audit for {theorem}.")
    print("[PASS] Lake build, direct replay, and expected standard-axiom audit", flush=True)


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="backslashreplace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=None, help="checkout containing the frozen organizer source")
    parser.add_argument("--lake", default="lake", help="Lake executable or absolute path")
    parser.add_argument("--timeout", type=int, default=900, help="per-command timeout in seconds")
    parser.add_argument("--skip-update", action="store_true", help="use only already materialized exact dependencies")
    args = parser.parse_args()
    try:
        need(args.timeout > 0, "timeout must be positive.")
        static_preflight()
        source_preflight(checkout(args.repo), args.timeout)
        lean_preflight_and_build(resolve_lake(args.lake), args.timeout, not args.skip_update)
        print("[PASS] COMPLETE: static, source, build, replay, and axiom checks", flush=True)
        print("[NOTE] No PDF, independent review, commit, GitHub publication, or organizer acceptance is asserted.", flush=True)
        return 0
    except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired, subprocess.CalledProcessError) as error:
        print(f"[FAIL] {error}", file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
