#!/usr/bin/env python3
"""Bounded #23 reproduction, not final review or a general Lean sandbox.

Python 3.10+; --skip-update uses only existing exact physical Git checkouts.
Only this project's .lake/build is cleared. Dependency build caches and the
installed compiler remain trust inputs, not a clean-machine bootstrap claim.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import time

CID = "00000000023"
PIN = "leanprover/lean4:v4.33.1"
SOURCE_COMMIT = "1e3f7c25616e84b611350a412febceabad75b56a"
SOURCE_BLOB = "2b3cb80e9b667ae812887a8cdaa9a803384fb6d1"
SOURCE_SHA256 = "c7287fb5d7e985e8015f4344c9460edbe53fbfcb026e761ed40b467debc7d754"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAME = r"[A-Za-z_][A-Za-z_0-9]*"
QUALIFIED = NAME + r"(?:\." + NAME + r")*"
MODULES = {
    "CoprimePairs": "CoprimePairs",
    "RatBridge": "SUnit23",
    "PrimeBound": "SUnitPrimeBound",
    "Final": "SUnit23",
    "GeneratedUnits": "SUnit23",
}
ROOTS = (*MODULES, "Main", "Check")
THEOREMS = tuple("CoprimePairs." + n for n in (
    "mem_squarePairs", "mem_coprimePairs", "squarePairs_card", "partition_card",
    "divisorPairs_card", "badPairs_subset_divisor_union", "badPairs_card_le_sum",
    "reciprocal_square_step", "reciprocalSquareSum_sharp", "reciprocalSquareSum_le",
    "division_square_le", "badPairs_card_rat_le", "coprimePairs_card_lower_bound",
    "all_positive_square_coprime_pairs",
)) + tuple("SUnit23." + n for n in (
    "reduced_num", "reduced_den", "small_integer_support", "actual_sunit_solutions",
    "fraction_injective",
)) + tuple("SUnitPrimeBound." + n for n in (
    "small_card_bound", "partition_card", "large_product_lower", "large_product_upper",
    "large_card_bound", "small_weight_bound", "cardinal_bound", "N_positive",
)) + tuple("SUnit23." + n for n in (
    "witness_card", "witnesses_are_actual_solutions", "witness_lower_bound",
    "every_constant_is_exceeded", "no_uniform_quadratic_bound",
    "bounded_integer_in_unit_group", "fractions_in_generated_group",
    "witness_generated_solutions", "no_generated_unit_quadratic_bound",
))
DEPENDENCIES = (
    ("mathlib", "https://github.com/leanprover-community/mathlib4.git", MATHLIB, MATHLIB, "", "lakefile.lean"),
    ("plausible", "https://github.com/leanprover-community/plausible", "b7eb3304aeae834b12dda98993a37f6a41f6f0bb", "main", "leanprover-community", "lakefile.toml"),
    ("LeanSearchClient", "https://github.com/leanprover-community/LeanSearchClient", "5f4d51b81cbd3f6b32b156bfad9056621a040404", "main", "leanprover-community", "lakefile.toml"),
    ("importGraph", "https://github.com/leanprover-community/import-graph", "16f02aa7642864af59f1ff0e384a015994db9118", "main", "leanprover-community", "lakefile.toml"),
    ("proofwidgets", "https://github.com/leanprover-community/ProofWidgets4", "4be2e3d5087eeb272cf5a8853b8f9dd025ef5957", "main", "leanprover-community", "lakefile.lean"),
    ("aesop", "https://github.com/leanprover-community/aesop", "3448c0bcc5ce01b2d1546e483ec3620e32df3d0e", "master", "leanprover-community", "lakefile.toml"),
    ("Qq", "https://github.com/leanprover-community/quote4", "92c15be17b7caf78c2ad767ec40f89052d908d81", "master", "leanprover-community", "lakefile.toml"),
    ("batteries", "https://github.com/leanprover-community/batteries", "4488d40d070b9700d4d5a6aa342f0d40c31b2a2d", "main", "leanprover-community", "lakefile.toml"),
    ("Cli", "https://github.com/leanprover/lean4-cli", "6130a47896ce867c6a4a55373441e59e565bad0f", "v4.33.0", "leanprover", "lakefile.toml"),
)
LAKEFILE = '''import Lake
open Lake DSL

package tlmc23 where
  srcDir := "."

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib TLMC23 where
  roots := #[`CoprimePairs, `RatBridge, `PrimeBound, `Final, `GeneratedUnits, `Main, `Check]
  moreLeanArgs := #["-DwarningAsError=true"]'''
LAKE_BIN: Path | None = None
WINDOWS_LINKTEXT = {
    "mathlib": {
        b"scripts/bench/build/fake-root/bin/lean.py": b"819298943e1a8c331413fb55e2c4bbc98d05e562",
        b"scripts/bench/size/run.py": b"e5224d533ef27b001224859a9b36696846a7e7fe",
    },
    "batteries": {b"docs/README.md": b"32d46ee883b58d6a383eed06eb98f33aa6530ded"},
}


class ReproductionError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ReproductionError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_path(path: Path, checked_parents: set[Path] | None = None) -> Path:
    """Check lexical ancestors before resolution; Windows junctions are reparse points."""
    absolute = Path(os.path.abspath(path))
    part, cached_parent = absolute, False
    while True:
        # Only ancestors can be cached within one pass; always lstat the entry itself.
        if part != absolute and checked_parents is not None and part in checked_parents:
            cached_parent = True
            break
        if os.path.lexists(part):
            info = part.lstat()
            require(not stat.S_ISLNK(info.st_mode) and not
                    (getattr(info, "st_file_attributes", 0) & 0x400),
                    "Symlink/reparse path rejected: " + str(part))
            if checked_parents is not None:
                checked_parents.add(part)
        if part.parent == part:
            break
        part = part.parent
    if not cached_parent:
        require(absolute.resolve() == absolute, "Path resolution changed the checked boundary")
    return absolute


def child_env() -> dict[str, str]:
    # Filter names before reading values; never inspect or log credential values.
    env = {key: os.environ[key] for key in os.environ
           if not key.upper().startswith(("GH_", "GITHUB_", "GIT_", "GCM_", "SSH_", "LEAN_"))
           and not any(word in key.upper() for word in ("TOKEN", "SECRET", "PASSWORD", "CREDENTIAL", "API_KEY"))}
    env.update(PYTHONUTF8="1", PYTHONIOENCODING="utf-8", PYTHONDONTWRITEBYTECODE="1",
               LANG="C.UTF-8", LC_ALL="C.UTF-8", NO_COLOR="1", GIT_TERMINAL_PROMPT="0",
               GCM_INTERACTIVE="Never", GCM_GUI_PROMPT="Never", GIT_NO_LAZY_FETCH="1",
               GIT_OPTIONAL_LOCKS="0", GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_CONFIG_COUNT="2", GIT_CONFIG_KEY_0="credential.helper", GIT_CONFIG_VALUE_0="",
               GIT_CONFIG_KEY_1="core.fsmonitor", GIT_CONFIG_VALUE_1="false",
               MATHLIB_NO_CACHE_ON_UPDATE="1")
    if LAKE_BIN is not None:
        env["PATH"] = str(LAKE_BIN) + os.pathsep + env.get("PATH", "")
    return env


def run(args: list[str], cwd: Path, timeout: int = 120, show_output: bool = False) -> bytes:
    try:
        result = subprocess.run(args, cwd=cwd, env=child_env(), stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ReproductionError("Local tool failed or timed out: " + Path(args[0]).name) from exc
    if show_output:
        print((result.stdout + result.stderr).decode("utf-8", errors="replace"), flush=True)
    require(result.returncode == 0, "Local command failed (exit " + str(result.returncode) +
            "): " + Path(args[0]).name)
    return result.stdout


def git(repo: Path, *args: str) -> bytes:
    return run(["git", "--no-pager", "-c", "credential.helper=", "-c", "core.fsmonitor=false",
                "-C", str(repo), *args], repo)


def validate_source(package: Path, repo: Path, m: dict) -> dict:
    for key, expected in (("source_commit", SOURCE_COMMIT), ("source_git_blob", SOURCE_BLOB),
                          ("source_sha256", SOURCE_SHA256)):
        require(m.get(key) == expected, "Frozen source manifest mismatch: " + key)
    source_name = "conjectures/" + CID + ".md"
    require(git(repo, "cat-file", "-t", SOURCE_COMMIT).strip() == b"commit", "Source object is not a commit")
    require(git(repo, "rev-parse", SOURCE_COMMIT + ":" + source_name).strip().decode() == SOURCE_BLOB,
            "Source commit does not bind the advertised blob")
    require(git(repo, "cat-file", "-t", SOURCE_BLOB).strip() == b"blob", "Source object is not a blob")
    raw = git(repo, "cat-file", "blob", SOURCE_BLOB)
    require(sha256(raw) == SOURCE_SHA256, "Raw source SHA-256 mismatch")
    require(hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() == SOURCE_BLOB,
            "Raw source Git-blob hash mismatch")
    require(safe_path(package / "source.md").read_bytes() == raw, "Frozen source differs from raw Git blob")
    current = safe_path(repo / source_name).read_bytes()
    require(current.replace(b"\r\n", b"\n") == raw.replace(b"\r\n", b"\n"),
            "Current bilingual source differs (CRLF-to-LF comparison)")
    raw.decode("utf-8", errors="strict")
    return {"commit": SOURCE_COMMIT, "blob": SOURCE_BLOB, "raw_sha256": SOURCE_SHA256}


def expected_lock() -> dict:
    return {"version": "1.2.0", "packagesDir": ".lake/packages", "name": "tlmc23",
            "lakeDir": ".lake", "fixedToolchain": False, "packages": [
                {"name": name, "type": "git", "url": url, "rev": rev, "inputRev": input_rev,
                 "subDir": None, "scope": scope, "manifestFile": "lake-manifest.json",
                 "inherited": name != "mathlib", "configFile": config}
                for name, url, rev, input_rev, scope, config in DEPENDENCIES]}


def validate_config(lean: Path) -> dict:
    require(safe_path(lean / "lean-toolchain").read_text(encoding="utf-8").strip() == PIN,
            "Exact Lean toolchain pin required")
    require(not os.path.lexists(lean / "lakefile.toml"), "Unexpected alternate Lake configuration")
    require(safe_path(lean / "lakefile.lean").read_text(encoding="utf-8").strip() == LAKEFILE,
            "Declarative Lake configuration/roots changed")
    lock = json.loads(safe_path(lean / "lake-manifest.json").read_text(encoding="utf-8"))
    require(lock == expected_lock(), "Exact nine-package Lake lock/configuration mismatch")
    return lock


def dependency_mode_allowed(name: str, mode: bytes, relative: bytes) -> bool:
    # Three fixed inert Git links must be exact ordinary Windows link-text files,
    # never physical symlinks/reparse points; benchmark scripts are not executed.
    return mode in {b"100644", b"100755"} or (
        os.name == "nt" and mode == b"120000" and relative in WINDOWS_LINKTEXT.get(name, set()))


def materialized_dependencies(lean: Path, lock: dict) -> dict:
    require(lock == expected_lock(), "Refuse non-frozen dependency specifications")
    reports = {}
    checked_parents: set[Path] = set()
    for spec in lock["packages"]:
        name = spec["name"]
        checkout = safe_path(lean / ".lake" / "packages" / name, checked_parents)
        require(checkout.is_dir(), "Missing physical dependency checkout: " + name)
        git_dir = safe_path(checkout / ".git", checked_parents)
        require(git_dir.is_dir(), "Dependency must own a physical .git directory: " + name)
        for root, dirs, files in os.walk(checkout, followlinks=False):
            for entry in dirs + files:
                safe_path(Path(root) / entry, checked_parents)
        require(safe_path(Path(git(checkout, "rev-parse", "--show-toplevel").decode().strip())) == checkout,
                "Dependency inherited/redirected a parent Git checkout: " + name)
        require(safe_path(Path(git(checkout, "rev-parse", "--absolute-git-dir").decode().strip())) == git_dir,
                "Dependency Git metadata redirected: " + name)
        require(git(checkout, "rev-parse", "HEAD").decode().strip() == spec["rev"], "Dependency HEAD mismatch: " + name)
        require(git(checkout, "remote", "get-url", "origin").decode().strip() == spec["url"],
                "Dependency origin mismatch: " + name)
        require(not git(checkout, "status", "--porcelain=v1", "-z", "--untracked-files=no",
                        "--ignore-submodules=none").strip(), "Modified tracked dependency source: " + name)
        tracked = git(checkout, "ls-files", "--stage", "-z").split(b"\0")
        require(any(tracked), "Empty tracked dependency inventory: " + name)
        tree = {}
        for record in git(checkout, "ls-tree", "-r", "-z", "--full-tree", "HEAD").split(b"\0"):
            if record:
                header, relative = record.split(b"\t", 1)
                mode, kind, oid = header.split()
                require(kind == b"blob" and dependency_mode_allowed(name, mode, relative),
                        "Non-regular dependency Git tree: " + name)
                if mode == b"120000":
                    require(oid == WINDOWS_LINKTEXT[name][relative], "Fixed inert-link Git blob mismatch")
                tree[relative] = (mode, oid)
        indexed = {}
        count = 0
        for record in tracked:
            if not record:
                continue
            header, relative = record.split(b"\t", 1)
            mode, oid, stage = header.split()
            require(dependency_mode_allowed(name, mode, relative) and stage == b"0",
                    "Symlink/submodule/unmerged tracked dependency source: " + name)
            if mode == b"120000":
                require(oid == WINDOWS_LINKTEXT[name][relative], "Fixed inert-link index blob mismatch")
            require(relative not in indexed, "Duplicate tracked dependency file: " + name)
            indexed[relative] = (mode, oid)
            path = safe_path(checkout / relative.decode("utf-8", errors="strict"), checked_parents)
            require(path.is_relative_to(checkout) and stat.S_ISREG(path.lstat().st_mode),
                    "Unsafe/missing tracked dependency file: " + name)
            data = path.read_bytes()
            def blob_hash(raw: bytes) -> bytes:
                return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest().encode()
            if blob_hash(data) != oid:
                require(mode != b"120000", "Inert link-text placeholder changed: " + name)
                # Permit ordinary UTF-8 text checkout EOL conversion, never binary normalization.
                require(b"\0" not in data, "Tracked binary dependency source changed: " + name)
                data.decode("utf-8", errors="strict")
                require(blob_hash(data.replace(b"\r\n", b"\n")) == oid,
                        "Tracked dependency bytes changed despite Git status: " + name)
            count += 1
        require(indexed == tree, "Dependency index differs from the fixed HEAD tree: " + name)
        reports[name] = {"head": spec["rev"], "origin": spec["url"], "clean_tracked_files": count}
    return reports


def scrub_comments(text: str) -> str:
    """Bounded comment lexer; strings are not accepted in authored math/Check."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - i))
            i = end
        else:
            require(text[i] != '"', "String outside bounded authored Lean dialect")
            out.append(text[i])
            i += 1
    require(depth == 0, "Unterminated Lean comment")
    return "".join(out)


def theorem_names(m: dict) -> list[str]:
    names = m.get("theorems")
    require(isinstance(names, list) and all(isinstance(n, str) for n in names)
            and Counter(names) == Counter(THEOREMS), "Manifest must contain the exact 36 public theorems")
    return names


def validate_lean(lean: Path, names: list[str]) -> dict:
    require(Counter(names) == Counter(THEOREMS), "Wrong theorem inventory")
    authored = []
    for root, dirs, files in os.walk(lean, followlinks=False):
        parent = Path(root)
        for directory in dirs:
            safe_path(parent / directory)
        if parent == lean:
            dirs[:] = [d for d in dirs if d != ".lake"]
        authored.extend(safe_path(parent / n).relative_to(lean).as_posix() for n in files if n.endswith(".lean"))
    require(set(authored) == {n + ".lean" for n in ROOTS} | {"lakefile.lean"},
            "Unexpected/missing authored Lean module")
    actual, inventories = [], {}
    forbidden = r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_tac|run_elab|elab|macro|syntax|initialize|builtin_initialize|IO|System|private|protected|section|attribute|opaque)\b"
    for module, namespace in MODULES.items():
        code = scrub_comments((lean / (module + ".lean")).read_text(encoding="utf-8"))
        require(re.search(forbidden, code) is None, "Prohibited authored Lean token: " + module)
        require(re.findall(r"^namespace (" + QUALIFIED + r")\s*$", code, re.M) == [namespace]
                and re.findall(r"^end (" + QUALIFIED + r")\s*$", code, re.M) == [namespace]
                and len(re.findall(r"\bnamespace\b", code)) == 1 and len(re.findall(r"\bend\b", code)) == 1,
                "Unsupported namespace layout: " + module)
        opening = re.search(r"^namespace " + namespace + r"\s*$", code, re.M)
        closing = re.search(r"^end " + namespace + r"\s*$", code, re.M)
        declarations = list(re.finditer(r"^(def|theorem|lemma) (" + NAME + r")\b", code, re.M))
        require(len(declarations) == len(re.findall(r"\b(?:def|theorem|lemma)\b", code)),
                "Unparsed public declaration: " + module)
        assert opening is not None and closing is not None
        require(all(opening.end() <= d.start() < closing.start() for d in declarations),
                "Declaration outside module namespace: " + module)
        public = [namespace + "." + d[2] for d in declarations if d[1] != "def"]
        symbols = {d[2] for d in declarations} | {namespace + "." + d[2] for d in declarations}
        inventories[module] = public
        actual.extend(public)
        imports = re.findall(r"^import (" + QUALIFIED + r")\s*$", code, re.M)
        require(len(imports) == len(re.findall(r"\bimport\b", code)) and all(
            n.startswith("Mathlib.") or n in MODULES for n in imports), "Unsupported import: " + module)
        options = re.findall(r"^set_option (.+)$", code, re.M)
        require(len(options) == len(re.findall(r"\bset_option\b", code))
                and all(o.strip() == "autoImplicit false" for o in options), "Unsupported source option: " + module)
        for line in code.splitlines():
            if not line.strip():
                continue
            if line.lstrip().startswith("#"):
                match = re.fullmatch(r"#(?:check|print(?: axioms)?) (" + QUALIFIED + r")", line.strip())
                require(match is not None and match[1] in symbols, "Unsafe authored diagnostic: " + module)
            elif not line[0].isspace():
                require(line.split()[0] in {"import", "namespace", "end", "set_option", "def", "theorem", "lemma"},
                        "Unsupported top-level authored command: " + module)
        require(code.count("#") == sum(line.lstrip().startswith("#") for line in code.splitlines()),
                "Hidden authored diagnostic: " + module)
    require(Counter(actual) == Counter(names), "All five modules/public theorem exact-set mismatch")
    require(scrub_comments((lean / "Main.lean").read_text(encoding="utf-8")).strip() == "import GeneratedUnits",
            "Main must only import GeneratedUnits")
    checks, prints, imports = [], [], 0
    lines = [line.strip() for line in scrub_comments((lean / "Check.lean").read_text(encoding="utf-8")).splitlines() if line.strip()]
    require(bool(lines) and lines[0] == "import Main", "Check must start with import Main")
    for line in lines:
        if line == "import Main":
            imports += 1
        elif match := re.fullmatch(r"#check (" + QUALIFIED + r")", line):
            checks.append(match[1])
        elif match := re.fullmatch(r"#print axioms (" + QUALIFIED + r")", line):
            prints.append(match[1])
        else:
            match = re.fullmatch(r"#print (" + QUALIFIED + r")", line)
            require(match is not None and match[1] in names, "Unsafe Check command")
    require(imports == 1 and Counter(checks) == Counter(names) and Counter(prints) == Counter(names),
            "Check/check/axiom inventory must each exactly match all 36 theorems")
    return {"count": len(names), "names": names, "modules": inventories}


def frozen_files(package: Path) -> dict[str, str]:
    checked_parents: set[Path] = set()
    package = safe_path(package, checked_parents)
    files = {}
    for root, dirs, names in os.walk(package, followlinks=False):
        parent = Path(root)
        for directory in dirs:
            safe_path(parent / directory, checked_parents)
        dirs[:] = [d for d in dirs if d != "__pycache__" and not (parent == package / "lean4" and d == ".lake")]
        for name in names:
            path = safe_path(parent / name, checked_parents)
            require(stat.S_ISREG(path.stat().st_mode), "Non-regular authored package file")
            files[path.relative_to(package).as_posix()] = sha256(path.read_bytes())
    return files


def clean_project_build(lean: Path, target: Path | None = None) -> None:
    lean = safe_path(lean)
    expected = lean / ".lake" / "build"
    target = safe_path(expected if target is None else target)
    require(target == expected and target.is_relative_to(lean), "Unsafe project cache deletion boundary")
    if not target.exists():
        return
    require(target.is_dir(), "Project build cache is not a directory")
    checked_parents: set[Path] = set()
    safe_path(target, checked_parents)
    for root, dirs, files in os.walk(target, followlinks=False):
        for name in dirs + files:
            safe_path(Path(root) / name, checked_parents)
    require(safe_path(target) == expected, "Deletion boundary changed")
    shutil.rmtree(target)


def prime_support(n: int) -> set[int]:
    n = abs(n)
    require(n > 0, "Zero has no finite multiplicative prime support")
    primes, d = set(), 2
    while d * d <= n:
        if n % d == 0:
            primes.add(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        primes.add(n)
    return primes


def is_sunit(support: set[int], value: Fraction) -> bool:
    return value != 0 and prime_support(value.numerator) <= support and prime_support(value.denominator) <= support


def regression() -> dict:
    samples = []
    for n in sorted(set(range(33)) | {2 ** (2 * m) for m in range(4)}):
        square = {(a, b) for a in range(1, n + 1) for b in range(1, n + 1)}
        coprime = {(a, b) for a, b in square if math.gcd(a, b) == 1}
        bad = square - coprime
        primes = {p for p in range(2, 2 * n + 1) if all(p % d for d in range(2, math.isqrt(p) + 1))}
        image = {}
        for a, b in coprime:
            x, y = Fraction(a, a + b), Fraction(b, a + b)
            require(x + y == 1 and x != 0 and y != 0, "Exact rational equation failed")
            require((x.numerator, x.denominator, y.numerator, y.denominator) == (a, a + b, b, a + b),
                    "Reduced rational numerator/denominator bridge failed")
            require(is_sunit(primes, x) and is_sunit(primes, y), "Actual rational prime support failed")
            require((x, y) not in image, "Rational witness map is not injective on coprime pairs")
            image[x, y] = (a, b)
        phi_count = 0 if n == 0 else 2 * sum(sum(math.gcd(a, b) == 1 for a in range(1, b + 1))
                                             for b in range(1, n + 1)) - 1
        require(len(square) == n ** 2 and len(coprime) + len(bad) == n ** 2,
                "Square/partition count failed")
        require(len(image) == len(coprime) == phi_count and n ** 2 <= 4 * len(image),
                "Independent totient/witness/cardinality lower bound failed")
        union, divisor_sum = set(), 0
        for d in range(2, n + 1):
            pairs = {(a, b) for a, b in square if a % d == 0 and b % d == 0}
            require(len(pairs) == (n // d) ** 2, "Exact divisor-pair count failed")
            union |= pairs
            divisor_sum += len(pairs)
        reciprocal = sum((Fraction(1, d ** 2) for d in range(2, n + 1)), Fraction(0))
        require(bad <= union and len(bad) <= divisor_sum <= n ** 2 * reciprocal <= Fraction(3, 4) * n ** 2,
                "Exact coprime counting/reciprocal bounds failed")
        if n >= 2:
            require(reciprocal <= Fraction(3, 4) - Fraction(1, n), "Sharp reciprocal bound failed")
        for k in range(1, 2 * n + 1):
            require(prime_support(k) <= primes, "Bounded integer prime support failed")
        samples.append({"N": n, "coprime_pairs": len(coprime), "rational_witnesses": len(image),
                        "prime_count": len(primes), "reciprocal_sum": str(reciprocal)})
    prime_samples = []
    for m in range(4):
        n = 2 ** (2 * m)
        primes = {p for p in range(2, 2 * n + 1) if all(p % d for d in range(2, math.isqrt(p) + 1))}
        small, large = {p for p in primes if p <= 2 ** m}, {p for p in primes if p > 2 ** m}
        product = math.prod(large)
        require(len(primes) == len(small) + len(large) and len(small) <= 2 ** m + 1,
                "Prime partition/small count failed")
        require(2 ** (m * len(large)) <= product <= 2 ** (4 * n), "Exact prime-product bounds failed")
        require(m * len(large) <= 4 * n and m * len(small) <= 2 * n and m * len(primes) <= 6 * n,
                "Prime-support cardinal bound failed")
        prime_samples.append({"m": m, "N": n, "prime_count": len(primes)})
    return {"scope": "bounded exact integer/Fraction samples, not the universal negation proof",
            "samples": samples, "prime_bound_samples": prime_samples}


def audit_axioms(output: str, names: list[str]) -> dict:
    audits = {}
    pattern = r"^'(" + QUALIFIED + r")' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$"
    for match in re.finditer(pattern, output, re.M):
        name, footprint = match[1], match[2]
        require(name in names and name not in audits, "Unexpected/duplicate actual axiom audit")
        used = [] if footprint is None else [a.strip() for a in footprint.split(",")]
        require(set(used) <= ALLOWED_AXIOMS, "Nonstandard axiom footprint: " + name)
        audits[name] = sorted(used)
    require(set(audits) == set(names), "Missing/malformed actual axiom audit")
    return audits


def preflight(package: Path, repo: Path) -> dict:
    package, repo = safe_path(package), safe_path(repo)
    frozen = frozen_files(package)
    m = json.loads((package / "submission.json").read_text(encoding="utf-8-sig"))
    require(m.get("id") == CID and m.get("solver") == "idealistichacker", "Submission identity mismatch")
    source = validate_source(package, repo, m)
    lock = validate_config(package / "lean4")
    names = theorem_names(m)
    inventory = validate_lean(package / "lean4", names)
    require(frozen_files(package) == frozen, "Frozen package changed during preflight")
    return {"source": source, "lock": lock, "theorems": inventory, "files": frozen}


def reproduce(package: Path, repo: Path, lake: str, skip_update: bool) -> dict:
    global LAKE_BIN
    package, repo = safe_path(package), safe_path(repo)
    before = preflight(package, repo)
    lean = package / "lean4"
    dependencies = None
    try:
        dependencies = materialized_dependencies(lean, before["lock"]) if skip_update else None
        report = {"id": CID, "source": before["source"], "theorems": before["theorems"],
                  "regression": regression(), "skip_update": skip_update}
        executable = shutil.which(lake)
        require(executable is not None, "Local Lake executable not found")
        lake_path = safe_path(Path(executable))
        require(not (lake_path.parent.name == "bin" and lake_path.parent.parent.name == ".elan"),
                "Use installed toolchain Lake, not an auto-installing elan shim")
        LAKE_BIN = lake_path.parent
        version = run([str(lake_path), "--version"], lean).decode("utf-8")
        require(re.fullmatch(r"Lake version 5\.0\.0-src(?:\+[0-9a-f]+)? \(Lean version 4\.33\.1\)\s*", version) is not None,
                "Exact Lake/Lean release mismatch")
        if not skip_update:
            # Source/config/lock are validated before any explicitly requested update.
            run([str(lake_path), "update"], lean, 900)
        require(preflight(package, repo) == before, "Frozen inputs changed before project cache cleanup")
        if dependencies is None:
            dependencies = materialized_dependencies(lean, before["lock"])
        version = run([str(lake_path), "--offline", "env", "lean", "--version"], lean).decode("utf-8")
        require(re.search(r"\bversion\s+4\.33\.1(?=,|\s|\)|$)", version) is not None, "Exact Lean version mismatch")
        clean_project_build(lean)
        print("[RUN] Clean project Main build (offline, warnings are errors)", flush=True)
        run([str(lake_path), "--offline", "--wfail", "build", "Main"], lean, 900, show_output=True)
        for module in (*MODULES, "Main"):
            print("[RUN] Source replay: " + module, flush=True)
            run([str(lake_path), "--offline", "env", "lean", "-DwarningAsError=true", module + ".lean"], lean, 900, show_output=True)
        print("[RUN] Exact 36-theorem Check axiom audit", flush=True)
        output = run([str(lake_path), "--offline", "env", "lean", "-DwarningAsError=true", "Check.lean"], lean, 900, show_output=True).decode("utf-8")
        report["axioms"] = audit_axioms(output, before["theorems"]["names"])
        report["status"] = "PASS"
        report["build"] = "clean own-project Main + five mathematical modules/Main source replay; warningAsError"
    finally:
        require(preflight(package, repo) == before, "Frozen authored files/manifest/source changed during reproduction")
        if dependencies is not None:
            require(materialized_dependencies(lean, before["lock"]) == dependencies, "Exact dependency state changed during reproduction")
    report["dependencies"] = dependencies
    report["windows_linktext_exception"] = {
        "scope": "Only three fixed inert Git-link blobs as exact ordinary Windows files (two Mathlib benchmarks, one batteries document); never execute these scripts; real links remain BLOCKED, including on Linux",
        "blobs": {name: {path.decode(): oid.decode() for path, oid in entries.items()}
                  for name, entries in WINDOWS_LINKTEXT.items()},
    }
    report["frozen_files"] = before["files"]
    report["boundaries"] = "Local reproduction only; no final review, PDF recompile, full dependency clean or empty-machine bootstrap"
    return report


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="backslashreplace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", required=True)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--skip-update", action="store_true", help="Offline exact dependency audit; never update/fetch/cache-download")
    args = parser.parse_args()
    started = time.monotonic_ns()
    try:
        report = reproduce(Path(__file__).absolute().parent, args.repo, args.lake, args.skip_update)
        report["duration_ms"] = (time.monotonic_ns() - started) // 1_000_000
        print(json.dumps(report, ensure_ascii=True, indent=2))
        return 0
    except (ReproductionError, OSError, ValueError, subprocess.SubprocessError) as exc:
        print("BLOCKED: " + str(exc), file=sys.stderr, flush=True)
        print("duration_ms: " + str((time.monotonic_ns() - started) // 1_000_000), file=sys.stderr, flush=True)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
