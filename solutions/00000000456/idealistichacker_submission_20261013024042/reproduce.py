#!/usr/bin/env python3
"""Bounded offline core-Lean reproduction, not a general parser or sandbox.

Python 3.11+; --repo holds the original conjecture and Git objects. --skip-update
is compatible with the coordinator: this Std-only package never updates. PDF
and mathematical statement review remain separate requirements.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tomllib
from collections import Counter
from typing import Any

CID = "00000000456"
NAMESPACE = "Conjecture456"
PIN = "leanprover/lean4:v4.33.1"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAME = r"[A-Za-z_][A-Za-z_0-9]*"
QUALIFIED = NAMESPACE + r"\." + NAME


class ReproductionError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ReproductionError(message)


def safe_path(path: Path) -> Path:
    """Check lexical ancestors before resolution, including Windows junctions."""
    absolute = Path(os.path.abspath(path))
    for part in reversed((absolute, *absolute.parents)):
        if not os.path.lexists(part):
            continue
        info = part.lstat()
        require(not stat.S_ISLNK(info.st_mode) and not
                (getattr(info, "st_file_attributes", 0) & 0x400),
                "Symlink/reparse path rejected: " + str(part))
    resolved = absolute.resolve()
    require(resolved == absolute, "Path resolution changed the checked boundary")
    return resolved


def child_env() -> dict[str, str]:
    env = {k: v for k, v in os.environ.items()
           if not k.upper().startswith(("GH_", "GITHUB_"))
           and k.upper() not in {"LEAN_PATH", "LEAN_SRC_PATH"}}
    env.update(PYTHONUTF8="1", PYTHONIOENCODING="utf-8",
               LANG="C.UTF-8", LC_ALL="C.UTF-8", GIT_TERMINAL_PROMPT="0",
               GCM_INTERACTIVE="never", GIT_NO_LAZY_FETCH="1", NO_COLOR="1")
    return env


def run(args: list[str], cwd: Path, timeout: int = 120) -> bytes:
    try:
        result = subprocess.run(args, cwd=cwd, env=child_env(), stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ReproductionError("Local tool failed or timed out: " + Path(args[0]).name) from exc
    # Never echo child stderr, commands, or environment into a secret-bearing log.
    require(result.returncode == 0, "Local command failed (exit " +
            str(result.returncode) + "): " + Path(args[0]).name)
    return result.stdout


def git(repo: Path, *args: str) -> bytes:
    return run(["git", "--no-pager", "-c", "credential.helper=", "-C", str(repo), *args], repo)


def validate_source(package: Path, repo: Path, manifest: dict[str, Any]) -> dict[str, str]:
    commit = manifest.get("source_commit", "")
    blob = manifest.get("source_git_blob", "")
    digest = manifest.get("source_sha256", "")
    require(isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit) is not None,
            "Full source_commit required")
    require(isinstance(blob, str) and re.fullmatch(r"[0-9a-f]{40}", blob) is not None,
            "Full source_git_blob required")
    require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest) is not None,
            "Raw source_sha256 required")
    source_name = "conjectures/" + CID + ".md"
    require(git(repo, "cat-file", "-t", commit).strip() == b"commit", "source_commit is not a Git commit")
    require(git(repo, "rev-parse", commit + ":" + source_name).decode().strip() == blob,
            "source_commit does not contain the declared source blob")
    require(git(repo, "cat-file", "-t", blob).strip() == b"blob", "Source object is not a Git blob")
    raw = git(repo, "cat-file", "blob", blob)
    require(hashlib.sha256(raw).hexdigest() == digest, "Raw Git blob SHA-256 mismatch")
    require(safe_path(package / "source.md").read_bytes() == raw, "source.md differs from raw Git blob")
    current = safe_path(repo / source_name).read_bytes()
    require(current.replace(b"\r\n", b"\n") == raw.replace(b"\r\n", b"\n"),
            "Current repository conjecture differs (LF comparison)")
    raw.decode("utf-8", errors="strict")
    return {"commit": commit, "blob": blob, "raw_sha256": digest}


def scrub_comments(text: str) -> str:
    """Nested comments only, preserving lines for the bounded source gates."""
    out: list[str] = []
    i, depth = 0, 0
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
        elif text[i] == '"':
            raise ReproductionError("String literals outside bounded Main/Check dialect")
        else:
            out.append(text[i])
            i += 1
    require(depth == 0, "Unterminated Lean comment")
    return "".join(out)


def validate_lean(main: str, check: str, manifest: dict[str, Any]) -> list[str]:
    names = manifest.get("theorems")
    require(isinstance(names, list) and bool(names) and all(
        isinstance(n, str) and re.fullmatch(QUALIFIED, n) for n in names),
        "Explicit Conjecture456 theorem list required")
    require(len(set(names)) == len(names), "Duplicate manifest theorem")
    code = scrub_comments(main)
    forbidden = r"\b(sorry|admit|axiom|opaque|unsafe|native_decide|run_tac|run_elab|elab|macro|syntax|initialize|builtin_initialize|extern|IO|System|private|protected|section|attribute)\b|[@#]"
    require(re.search(forbidden, code) is None, "Main outside bounded safe core dialect")
    require(re.findall(r"^import\s+(.+)$", code, re.M) == ["Std"], "Main must import only Std")
    require(len(re.findall(r"\bimport\b", code)) == 1, "Unsupported indented import")
    require(re.findall(r"\bnamespace\s+(\S+)", code) == [NAMESPACE] and
            re.findall(r"^end\s+(\S+)\s*$", code, re.M) == [NAMESPACE],
            "Exactly one Conjecture456 namespace required")
    require(len(re.findall(r"\bend\b", code)) == 1, "Nested sections/namespaces unsupported")
    options = re.findall(r"^set_option\s+(.+)$", code, re.M)
    require(len(options) == len(re.findall(r"\bset_option\b", code)), "Unsupported local source option")
    for option in options:
        require(re.fullmatch(r"(?:maxRecDepth|maxHeartbeats) [0-9]+", option) is not None,
                "Unsupported Main option")
    actual = [NAMESPACE + "." + n for n in re.findall(r"^theorem\s+(" + NAME + r")\b", code, re.M)]
    require(len(actual) == len(re.findall(r"\btheorem\b", code)), "Unsupported theorem declaration")
    require(Counter(actual) == Counter(names), "Manifest/actual public theorem mismatch")
    opening = re.search(r"^namespace Conjecture456\s*$", code, re.M)
    closing = re.search(r"^end Conjecture456\s*$", code, re.M)
    require(opening is not None and closing is not None and opening.end() < closing.start(),
            "Unsupported namespace layout")
    assert opening is not None and closing is not None
    for declaration in re.finditer(r"^(?:abbrev|inductive|def|instance|theorem)\b", code, re.M):
        require(opening.end() <= declaration.start() < closing.start(), "Declaration outside Conjecture456")
    allowed_heads = {"import", "set_option", "namespace", "end", "abbrev", "inductive",
                     "open", "def", "instance", "theorem"}
    for line in code.splitlines():
        if line and not line[0].isspace():
            require(line.split()[0] in allowed_heads, "Unsupported top-level Lean command")
    checks: list[str] = []
    imports = 0
    for line in scrub_comments(check).splitlines():
        line = line.strip()
        if not line:
            continue
        if line == "import Main":
            imports += 1
        elif match := re.fullmatch(r"#print axioms (" + QUALIFIED + r")", line):
            checks.append(match[1])
        else:
            require(re.fullmatch(r"#(?:check|print) " + QUALIFIED, line) is not None,
                    "Check permits only import Main, axiom prints, checks and definition prints")
    require(imports == 1 and Counter(checks) == Counter(names), "Check/manifest axiom print mismatch")
    return names


def validate_config(lean: Path) -> None:
    require((lean / "lean-toolchain").read_text(encoding="utf-8").strip() == PIN,
            "Exact Lean 4.33.1 pin required")
    toml, lakelean = lean / "lakefile.toml", lean / "lakefile.lean"
    require(toml.is_file() != lakelean.is_file(), "Exactly one Lake configuration required")
    if toml.is_file():
        config = tomllib.loads(toml.read_text(encoding="utf-8"))
        require(set(config) <= {"name", "version", "defaultTargets", "lean_lib", "moreLeanArgs"},
                "Unsupported Lake TOML key (no dependencies or executable targets)")
        libs = config.get("lean_lib", [])
        require(isinstance(libs, list) and len(libs) == 1 and isinstance(libs[0], dict)
                and libs[0].get("name") == "Main" and set(libs[0]) <= {"name", "moreLeanArgs"},
                "Only lean_lib Main is supported")
        for args in (config.get("moreLeanArgs", []), libs[0].get("moreLeanArgs", [])):
            require(args in ([], ["-DwarningAsError=true"]), "Unsupported Lake Lean arguments")
    else:
        # A declarative Lake DSL whitelist, not execution of arbitrary lakefile Lean.
        config = lakelean.read_text(encoding="utf-8")
        pattern = (r'\s*import Lake\s+open Lake DSL\s+package ' + NAME +
                   r'(?:\s+where\s+moreLeanArgs\s*:=\s*#\["-DwarningAsError=true"\])?'
                   r'\s+(?:@\[default_target\]\s+)?lean_lib Main'
                   r'(?:\s+where\s+moreLeanArgs\s*:=\s*#\["-DwarningAsError=true"\])?\s*')
        require(re.fullmatch(pattern, config) is not None, "Only declarative dependency-free Lake DSL supported")
    lock = json.loads((lean / "lake-manifest.json").read_text(encoding="utf-8"))
    require(lock.get("packages") == [], "lake-manifest packages must be exactly []")
    require(lock.get("lakeDir", ".lake") == ".lake" and
            lock.get("packagesDir", ".lake/packages") == ".lake/packages",
            "Lake manifest cache paths must stay in project .lake")


def frozen_files(package: Path) -> dict[str, str]:
    package = safe_path(package)
    files: dict[str, str] = {}
    for root, dirs, names in os.walk(package, followlinks=False):
        parent = Path(root)
        for directory in dirs:
            safe_path(parent / directory)
        # Only generated project cache is omitted, not source or manifest files.
        if parent == package / "lean4":
            dirs[:] = [d for d in dirs if d != ".lake"]
        for name in names:
            path = safe_path(parent / name)
            require(path.is_file(), "Non-regular package file")
            files[path.relative_to(package).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return files


def preflight(package: Path, repo: Path) -> dict[str, Any]:
    package, repo = safe_path(package), safe_path(repo)
    frozen = frozen_files(package)
    manifest = json.loads((package / "submission.json").read_text(encoding="utf-8"))
    require(manifest.get("id") == CID, "Wrong submission id")
    source = validate_source(package, repo, manifest)
    lean = package / "lean4"
    validate_config(lean)
    require({name.removeprefix("lean4/") for name in frozen
             if name.startswith("lean4/") and name.endswith(".lean")}
            <= {"Main.lean", "Check.lean", "lakefile.lean"}, "Unexpected local Lean module")
    theorems = validate_lean((lean / "Main.lean").read_text(encoding="utf-8"),
                             (lean / "Check.lean").read_text(encoding="utf-8"), manifest)
    require(frozen_files(package) == frozen, "Package changed during preflight")
    return {"source": source, "theorems": theorems, "files": frozen}


def clean_project_cache(package: Path, target: Path | None = None) -> None:
    package = safe_path(package)
    expected = package / "lean4" / ".lake" / "build"
    target = safe_path(expected if target is None else target)
    require(target == expected and target.is_relative_to(package), "Unsafe cache deletion boundary")
    if not target.exists():
        return
    require(target.is_dir(), "Build cache is not a directory")
    for root, dirs, files in os.walk(target, followlinks=False):
        for name in dirs + files:
            safe_path(Path(root) / name)
    # Validate the entire existing deletion tree before deleting any file.
    require(safe_path(target) == expected, "Cache deletion boundary changed")
    shutil.rmtree(target)


def enumerate_objects() -> dict[str, Any]:
    objects: list[tuple[str, tuple[int, ...], tuple[int, ...]]] = []
    words: list[str] = []
    for steps in itertools.product("NE", repeat=5):
        if steps.count("N") != 3 or steps.count("E") != 2:
            continue
        x = y = 0
        columns: list[int] = []
        good = True
        for step in steps:
            if step == "N":
                columns.append(x)
                y += 1
            else:
                x += 1
            if 3 * x > 2 * y:
                good = False
                break
        if not good:
            continue
        word = "".join(steps)
        words.append(word)
        for labels in itertools.permutations(range(3)):
            if all(columns[i] != columns[j] or labels[i] < labels[j]
                   for i in range(3) for j in range(i + 1, 3)):
                objects.append((word, tuple(columns), labels))
    preferences = [tuple(cols[labels.index(j)] for j in range(3)) for _, cols, labels in objects]
    require(words == ["NNNEE", "NNENE"], "Unexpected raw path enumeration")
    require(len(objects) == 4 and len(set(preferences)) == 4, "Actual labelled-object count mismatch")
    require(set(preferences) == {(0, 0, 0), (0, 0, 1), (0, 1, 0), (1, 0, 0)}, "Preference image mismatch")
    numerator, denominator = math.factorial(3 + 2 - 1), math.factorial(3 - 1)
    require((numerator, denominator, numerator // denominator) == (24, 2, 12), "Height-first formula mismatch")
    return {"scope": "bounded actual objects at height-first (m,n)=(3,2); not an object-bridge proof",
            "words": words, "objects": objects, "preferences": preferences, "actual_count": len(objects),
            "formula_numerator": numerator, "formula_denominator": denominator, "formula_value": 12}


def audit_axioms(output: str, names: list[str]) -> dict[str, list[str]]:
    found: dict[str, list[str]] = {}
    pattern = r"^'(" + QUALIFIED + r")' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$"
    for match in re.finditer(pattern, output, re.M):
        name, footprint = match[1], match[2]
        require(name in names and name not in found, "Unexpected/duplicate actual axiom audit")
        axioms = [] if not footprint else [a.strip() for a in footprint.split(",")]
        require(set(axioms) <= ALLOWED_AXIOMS, "Prohibited axiom footprint for " + name)
        found[name] = axioms
    require(set(found) == set(names), "Missing actual theorem axiom audit")
    return found


def reproduce(package: Path, repo: Path, lake: str, preflight_only: bool = False) -> dict[str, Any]:
    before = preflight(package, repo)
    report: dict[str, Any] = {"source": before["source"], "theorems": before["theorems"],
                              "enumeration": enumerate_objects(), "dependency_update": "not needed; never run",
                              "lean_executed": False}
    if preflight_only:
        require(preflight(package, repo) == before, "Preflight inputs changed")
        return report
    executable = shutil.which(lake)
    require(executable is not None, "Local Lake executable not found")
    lake_path = safe_path(Path(executable))
    require(not (lake_path.parent.name == "bin" and lake_path.parent.parent.name == ".elan"),
            "Use installed toolchain Lake, not an auto-installing elan shim")
    lean = package / "lean4"
    lake_version = run([str(lake_path), "--version"], lean).decode("utf-8")
    require(re.fullmatch(r"Lake version 5\.0\.0-src(?:\+[0-9a-f]+)? \(Lean version 4\.33\.1\)\s*", lake_version)
            is not None, "Exact Lake/Lean release version mismatch")
    lean_version = run([str(lake_path), "--offline", "env", "lean", "--version"], lean).decode("utf-8")
    require(re.search(r"\bversion\s+4\.33\.1(?=,|\s|\)|$)", lean_version) is not None,
            "Exact Lean tool version mismatch")
    require(preflight(package, repo) == before, "Inputs changed before cache cleanup")
    clean_project_cache(package)
    try:
        run([str(lake_path), "--offline", "--wfail", "build", "Main"], lean, 600)
        run([str(lake_path), "--offline", "env", "lean", "-DwarningAsError=true", "Main.lean"], lean, 600)
        output = run([str(lake_path), "--offline", "env", "lean", "-DwarningAsError=true", "Check.lean"], lean, 600)
        report["axioms"] = audit_axioms(output.decode("utf-8"), before["theorems"])
        report["lean_executed"] = True
    finally:
        require(preflight(package, repo) == before, "Frozen package/source changed during reproduction")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--skip-update", action="store_true", help="Compatibility flag; core never updates dependencies")
    parser.add_argument("--preflight-only", action="store_true", help="No tool versions, cache deletion, or Lean execution")
    args = parser.parse_args()
    try:
        report = reproduce(safe_path(Path(__file__).absolute().parent), safe_path(args.repo), args.lake, args.preflight_only)
        print(json.dumps(report, ensure_ascii=True, indent=2))
        return 0
    except (ReproductionError, OSError, ValueError) as exc:
        print("Reproduction failed: " + str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
