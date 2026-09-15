#!/usr/bin/env python3
"""Finite regression checks followed by Lean's proof and dependency checks.

Requires Python 3.11+ and the pinned Lean 4.33.1 toolchain. No Python packages,
network requests, PDF generation, Git operations, or manifest edits are performed
by this script. Lake may create/update its own files under lean4/.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tomllib

BASE = Path(__file__).resolve().parent
LEAN_DIR = BASE / "lean4"
LEAN_VERSION = "4.33.1"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
NAMESPACE = "Conjecture00000000116"
THEOREMS = (
    "absDiff_piecewise", "absDiff_self", "prime_two", "identity_solution",
    "swap_one", "swap_three", "swap_zero", "swap_fixed", "swap_involutive",
    "swap_bijection", "swap_allowed", "swap_nonidentity", "swap_positive",
    "nonidentity_strengthening", "original_conjecture",
    "positiveSwap_involutive", "positive_naturals_solution",
)


def require(condition: bool, message: str) -> None:
    # Unlike assert, this check is not disabled by python -O.
    if not condition:
        raise RuntimeError(message)


def prime_by_positive_divisors(p: int) -> bool:
    """The mathematical definition used by Lean; evaluated only on small inputs."""
    return p >= 2 and all(p % d != 0 or d in (1, p) for d in range(1, p + 1))


def abs_diff(a: int, b: int) -> int:
    return max(a - b, 0) + max(b - a, 0)


def swap_one_three(n: int) -> int:
    return 3 if n == 1 else 1 if n == 3 else n


def finite_regression(bound: int) -> None:
    require(bound >= 3, "The finite regression bound must include 1 and 3.")
    for p, expected in ((0, False), (1, False), (2, True), (3, True),
                        (4, False), (9, False), (97, True)):
        require(prime_by_positive_divisors(p) == expected,
                f"Prime definition regression failed at {p}.")
    for a in range(65):
        for b in range(65):
            require(abs_diff(a, b) == abs(a - b),
                    f"Absolute difference mismatch at {(a, b)}.")
    images = set()
    for n in range(bound + 1):
        image = swap_one_three(n)
        delta = abs_diff(image, n)
        require(swap_one_three(image) == n, f"Involution failed at {n}.")
        require(delta == (2 if n in (1, 3) else 0),
                f"Displacement formula failed at {n}.")
        require(delta == 0 or prime_by_positive_divisors(delta),
                f"Allowed displacement failed at {n}.")
        require(abs_diff(n, n) == 0, f"Identity regression failed at {n}.")
        require(n == 0 or image > 0, f"Positive naturals regression failed at {n}.")
        images.add(image)
    require(images == set(range(bound + 1)),
            "Bijection regression on the finite interval failed.")
    require(swap_one_three(0) == 0, "Zero must be fixed.")
    require(swap_one_three(1) == 3 and swap_one_three(3) == 1,
            "The nonidentity witness is incorrect.")
    for n in (2**64, 2**256, 10**100):
        require(swap_one_three(n) == n, "Large-integer fixed point regression failed.")
    print(f"[PASS] Finite regression: n = 0..{bound} ({bound + 1} values), "
          "65 x 65 absolute differences, and three large integer samples.", flush=True)
    print("[NOTE] These finite checks are regressions, NOT a proof for all natural numbers.",
          flush=True)


def source_preflight() -> None:
    pin = (LEAN_DIR / "lean-toolchain").read_text(encoding="utf-8").strip()
    require(pin == TOOLCHAIN, f"Unexpected toolchain pin: {pin!r}")
    with (LEAN_DIR / "lakefile.toml").open("rb") as handle:
        config = tomllib.load(handle)
    require("Main" in config.get("defaultTargets", []), "Main must be a default Lake target.")
    require(any(lib.get("name") == "Main" for lib in config.get("lean_lib", [])),
            "The Main Lean library is missing.")
    require(not config.get("require"), "This solution must not have external Lake dependencies.")
    forbidden = re.compile(r"\b(?:sorry|admit|axiom|native_decide|unsafe|run_tac|elab)\b")
    for name in ("Main.lean", "Check.lean"):
        text = (LEAN_DIR / name).read_text(encoding="utf-8")
        require(not forbidden.search(text), f"Prohibited proof construct found in {name}.")
    checker = (LEAN_DIR / "Check.lean").read_text(encoding="utf-8")
    commands = re.findall(r"^#print axioms ([A-Za-z0-9_.]+)\s*$", checker, re.MULTILINE)
    require(commands == [f"{NAMESPACE}.{name}" for name in THEOREMS],
            "Check.lean must audit exactly the advertised public theorems, in order.")
    print("[PASS] Source preflight: pinned version, default target, no external packages, "
          "and expected audit commands.", flush=True)
    print("[NOTE] Text scanning is a preflight only, not a substitute for kernel checking.",
          flush=True)


def run(command: list[str], env: dict[str, str], timeout: int) -> str:
    print("[RUN] " + subprocess.list2cmdline(command), flush=True)
    completed = subprocess.run(command, cwd=LEAN_DIR, env=env,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               encoding="utf-8", errors="replace", timeout=timeout,
                               check=False)
    if completed.stdout:
        print(completed.stdout, end="" if completed.stdout.endswith("\n") else "\n",
              flush=True)
    print(f"[EXIT] {completed.returncode}", flush=True)
    require(completed.returncode == 0, f"Command failed with exit code {completed.returncode}.")
    return completed.stdout


def lean_verification(lake_argument: str, timeout: int) -> None:
    lake_found = shutil.which(lake_argument)
    require(lake_found is not None,
            "Lake was not found. Install Lean 4.33.1 and put lake on PATH, "
            "or pass --lake /absolute/path/to/lake. "
            "Use --regression-only only if deliberately skipping the proof checks.")
    lake = str(Path(lake_found).resolve())
    env = os.environ.copy()
    env["PATH"] = str(Path(lake).parent) + os.pathsep + env.get("PATH", "")
    # Avoid silently importing search paths from another Lean project.
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    run([lake, "--version"], env, timeout)
    version = run([lake, "env", "lean", "--version"], env, timeout)
    require(re.search(r"\bversion 4\.33\.1(?:[,)\s]|$)", version) is not None,
            f"This submission requires Lean {LEAN_VERSION}, not the detected version.")
    run([lake, "build"], env, timeout)
    # Explicitly replay the source in addition to Lake's incremental build.
    run([lake, "env", "lean", "-DwarningAsError=true", "Main.lean"], env, timeout)
    audit = run([lake, "env", "lean", "-DwarningAsError=true", "Check.lean"], env, timeout)
    for name in THEOREMS:
        expected = f"'{NAMESPACE}.{name}' does not depend on any axioms"
        require(expected in audit.splitlines(),
                f"Missing or nonempty transitive dependency audit for {name}.")
    manifest_path = LEAN_DIR / "lake-manifest.json"
    require(manifest_path.is_file(), "Lake did not produce its dependency manifest.")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    require(manifest.get("packages") == [], "Unexpected external Lake packages in the manifest.")
    print(f"[PASS] Lean source replay and all {len(THEOREMS)} public theorem audits; "
          "each audit has an empty axiom list.", flush=True)


def main() -> int:
    # Make piped Windows output deterministic even under a legacy code page.
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="backslashreplace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake executable or absolute executable path.")
    parser.add_argument("--bound", type=int, default=10000,
                        help="Inclusive finite regression bound, at least 3 (default: 10000).")
    parser.add_argument("--timeout", type=int, default=300,
                        help="Timeout in seconds for each Lean command (default: 300).")
    parser.add_argument("--regression-only", action="store_true",
                        help="Run only finite checks and preflight; explicitly NOT full verification.")
    args = parser.parse_args()
    try:
        require(args.timeout > 0, "The command timeout must be positive.")
        source_preflight()
        finite_regression(args.bound)
        if args.regression_only:
            print("[PARTIAL] Lean was NOT run. No infinite theorem verification is claimed.", flush=True)
            return 0
        lean_verification(args.lake, args.timeout)
        print("[PASS] COMPLETE: finite regressions, Lean build, direct source replay, "
              "and transitive dependency audits.", flush=True)
        print("[NOTE] No PDF, independent review, publication, or upstream acceptance "
              "is asserted by this script.", flush=True)
        return 0
    except (RuntimeError, OSError, subprocess.TimeoutExpired, ValueError) as error:
        print(f"[FAIL] {error}", file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
