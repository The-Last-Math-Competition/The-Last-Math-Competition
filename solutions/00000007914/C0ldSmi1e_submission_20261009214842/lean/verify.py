#!/usr/bin/env python3
"""Independently reproduce the pinned Lean proof and audit, using only Python's standard library."""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
LOGS = ROOT / ".lake" / "verification"
EXPECTED_HASHES = {
    "CovolumeSpectrum.lean": "0bf9a035b94cb234d993036532fa30ec755dfbf52e6eeb125e1f8eb4557867d8",
    "Audit.lean": "d4ff2bec20fc148b79fed0bca32bdab8f921411a7f22ebf9ae28e35b5b8a890c",
    "lakefile.toml": "1150c806b1420243820a8dccba1ca717dbd64600168c9b2c00097a05250e7131",
    "lake-manifest.json": "8d8e5829ddacd806e26f35f980d0c15b8c6dfc477a2e5d611869b2293afa9deb",
    "lean-toolchain": "55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea",
}
THEOREMS = (
    "scale_tendsto_zero",
    "asymptotic_iff_ratio",
    "rank_strictMono",
    "no_rankedAsymptotic",
    "limit_spectrum_nonnegative",
    "limit_nonnegative",
    "no_numericalConjecture",
    "no_full_conjunction",
    "finiteMeasureValues_nonnegative",
    "no_measure_spectrum_conjunction",
    "finite_liminf_nonnegative",
    "no_liminf_spectrum_conjunction",
)
EXPECTED_AXIOMS = "".join(
    f"'CovolumeSpectrum.{name}' depends on axioms: "
    "[propext, Classical.choice, Quot.sound]\n"
    for name in THEOREMS
)
EXPECTED_TYPES = "CovolumeSpectrum.scale_tendsto_zero : ∀ (c : Real),\n  Filter.Tendsto.{0, 0} (CovolumeSpectrum.scale c) Filter.atTop.{0} (nhds.{0} 0)\n@CovolumeSpectrum.asymptotic_iff_ratio : ∀ {v : Nat → Real} {c : Real},\n  Ne.{1} c 0 →\n    Iff (Asymptotics.IsEquivalent.{0, 0} Filter.atTop.{0} v (CovolumeSpectrum.scale c))\n      (Filter.Tendsto.{0, 0} (fun k => HDiv.hDiv.{0, 0, 0} (v k) (CovolumeSpectrum.scale c k)) Filter.atTop.{0}\n        (nhds.{0} 1))\n@CovolumeSpectrum.rank_strictMono : ∀ {S : Set.{0} Real} {v : Nat → Real},\n  (∀ (n : Nat), CovolumeSpectrum.HasRank S n (v n)) → StrictMono.{0, 0} v\n@CovolumeSpectrum.no_rankedAsymptotic : ∀ {S : Set.{0} Real},\n  HasSubset.Subset.{0} S (Set.Ici.{0} 0) → Not (CovolumeSpectrum.RankedAsymptotic S)\n@CovolumeSpectrum.limit_spectrum_nonnegative : ∀ {C S : Set.{0} Real},\n  HasSubset.Subset.{0} C (Set.Ici.{0} 0) →\n    HasSubset.Subset.{0} S (closure.{0} C) → HasSubset.Subset.{0} S (Set.Ici.{0} 0)\n@CovolumeSpectrum.limit_nonnegative.{u_1} : ∀ {ι : Type u_1} {l : Filter.{u_1} ι} [inst : Filter.NeBot.{u_1} l]\n  {f : ι → Real} {x : Real},\n  (∀ᶠ (i : ι) in l, LE.le.{0} 0 (f i)) → Filter.Tendsto.{u_1, 0} f l (nhds.{0} x) → LE.le.{0} 0 x\n@CovolumeSpectrum.no_numericalConjecture : ∀ {S : Set.{0} Real},\n  HasSubset.Subset.{0} S (Set.Ici.{0} 0) → Not (CovolumeSpectrum.NumericalConjecture S)\n@CovolumeSpectrum.no_full_conjunction : ∀ {C S : Set.{0} Real},\n  HasSubset.Subset.{0} C (Set.Ici.{0} 0) →\n    HasSubset.Subset.{0} S (closure.{0} C) → ∀ (rest : Prop), Not (And (CovolumeSpectrum.NumericalConjecture S) rest)\n@CovolumeSpectrum.finiteMeasureValues_nonnegative.{u_1,\n    u_2} : ∀ {ι : Type u_1} {X : ι → Type u_2} [inst : (i : ι) → MeasurableSpace.{u_2} (X i)]\n  (μ : (i : ι) → MeasureTheory.Measure.{u_2} (X i)),\n  HasSubset.Subset.{0} (CovolumeSpectrum.finiteMeasureValues.{u_1, u_2} μ) (Set.Ici.{0} 0)\n@CovolumeSpectrum.no_measure_spectrum_conjunction.{u_1,\n    u_2} : ∀ {ι : Type u_1} {X : ι → Type u_2} [inst : (i : ι) → MeasurableSpace.{u_2} (X i)]\n  (μ : (i : ι) → MeasureTheory.Measure.{u_2} (X i)) {S : Set.{0} Real},\n  HasSubset.Subset.{0} S (closure.{0} (CovolumeSpectrum.finiteMeasureValues.{u_1, u_2} μ)) →\n    ∀ (rest : Prop), Not (And (CovolumeSpectrum.NumericalConjecture S) rest)\n@CovolumeSpectrum.finite_liminf_nonnegative.{u_1} : ∀ {ι : Type u_1} {l : Filter.{u_1} ι} {f : ι → Real} {x : Real},\n  (∀ᶠ (i : ι) in l, LE.le.{0} 0 (f i)) → Eq.{1} (Filter.liminf.{0, u_1} (fun i => ↑(f i)) l) ↑x → LE.le.{0} 0 x\n@CovolumeSpectrum.no_liminf_spectrum_conjunction : ∀ {C S : Set.{0} Real},\n  HasSubset.Subset.{0} C (Set.Ici.{0} 0) →\n    (∀ (x : Real),\n        Membership.mem.{0, 0} S x →\n          ∃ f,\n            And (∀ (n : Nat), Membership.mem.{0, 0} C (f n))\n              (Eq.{1} (Filter.liminf.{0, 0} (fun n => ↑(f n)) Filter.atTop.{0}) ↑x)) →\n      ∀ (rest : Prop), Not (And (CovolumeSpectrum.NumericalConjecture S) rest)\n"
TYPE_AUDIT = (
    "import CovolumeSpectrum\n\n"
    "set_option pp.universes true\n"
    "set_option pp.fullNames true\n"
    "set_option format.width 120\n\n"
    + "".join(f"#check @CovolumeSpectrum.{name}\n" for name in THEOREMS)
)
ENV = os.environ.copy()
# Let Lake construct its own import path from the pinned package graph.
for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
    ENV.pop(name, None)
COMMANDS = []


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(label, args):
    print(f"Running {label} ...", flush=True)
    result = subprocess.run(
        args, cwd=ROOT, env=ENV, text=True, encoding="utf-8",
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    (LOGS / f"{label}.log").write_text(result.stdout, encoding="utf-8")
    COMMANDS.append({"label": label, "command": args, "exit_code": result.returncode})
    require(result.returncode == 0, f"{label} failed; see .lake/verification/{label}.log")
    return result.stdout


def lean_code_only(text):
    """Blank nested comments and string literals, retaining line positions."""
    result = list(text)
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                result[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                result[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    result[i] = " "
                i += 1
        elif in_string:
            if text[i] == "\\":
                result[i] = " "
                i += 1
                if i < len(text):
                    if text[i] != "\n":
                        result[i] = " "
                    i += 1
            elif text[i] == '"':
                result[i] = " "
                in_string = False
                i += 1
            else:
                if text[i] != "\n":
                    result[i] = " "
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            result[i:end] = " " * (end - i)
            i = end
        elif text.startswith("/-", i):
            result[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text[i] == '"':
            result[i] = " "
            in_string = True
            i += 1
        else:
            i += 1
    require(not depth and not in_string, "Unterminated Lean comment/string")
    return "".join(result)


def check_sources():
    for filename, expected in EXPECTED_HASHES.items():
        path = ROOT / filename
        require(path.is_file() and not path.is_symlink(), f"Missing/nonregular source: {filename}")
        require(digest(path.read_bytes()) == expected, f"Source integrity mismatch: {filename}")
    authored = {
        str(path.relative_to(ROOT)).replace(os.sep, "/")
        for path in ROOT.rglob("*.lean")
        if ".lake" not in path.relative_to(ROOT).parts
    }
    require(authored == {"CovolumeSpectrum.lean", "Audit.lean"},
            f"Unexpected project Lean source inventory: {sorted(authored)}")
    forbidden = re.compile(
        r"\b(sorry|admit|sorryAx|axiom|unsafe|native_decide|native_decide_eq_true|"
        r"ofReduceBool|ofReduceNat|trustCompiler|skipKernelTC|implemented_by|extern|"
        r"run_tac|run_elab|run_io|initialize|builtin_initialize|elab|macro|syntax)\b"
        r"|#\s*(eval|reduce)\b"
    )
    scan = {}
    for filename in sorted(authored):
        code = lean_code_only((ROOT / filename).read_text(encoding="utf-8"))
        match = forbidden.search(code)
        require(match is None, f"Prohibited proof construct in {filename}: "
                + (match.group(0) if match else ""))
        scan[filename] = {"sha256": EXPECTED_HASHES[filename], "prohibited_constructs": []}
    declarations = re.findall(
        r"^\s*theorem\s+([A-Za-z_][A-Za-z0-9_']*)",
        lean_code_only((ROOT / "CovolumeSpectrum.lean").read_text(encoding="utf-8")), re.M,
    )
    require(len(declarations) == len(THEOREMS) and set(declarations) == set(THEOREMS),
            "The expected audit does not cover every theorem declaration")
    (LOGS / "source-integrity.json").write_text(
        json.dumps({"sha256": EXPECTED_HASHES, "scan": scan,
                    "all_theorems_audited": sorted(declarations)}, indent=2) + "\n",
        encoding="utf-8",
    )


def check_dependencies(phase):
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    require(manifest["packagesDir"] == ".lake/packages", "Unexpected package directory")
    records = []
    for package in manifest["packages"]:
        require(package["type"] == "git", "Only the pinned stock git dependencies are permitted")
        name = package["name"]
        path = ROOT / ".lake" / "packages" / name
        require(path.is_dir(), f"Missing dependency {name}; first run: lake exe cache get")
        head = run(f"{phase}-{name}-revision",
                   ["git", "-C", str(path), "rev-parse", "HEAD"]).strip()
        status = run(f"{phase}-{name}-tracked-status",
                     ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"])
        require(head == package["rev"], f"Wrong dependency revision: {name}")
        require(not status.strip(), f"Modified tracked stock source: {name}")
        records.append({"name": name, "revision": head, "tracked_status": "clean"})
    require(len(records) == 9, "Expected mathlib plus its eight pinned dependencies")
    (LOGS / f"dependencies-{phase}.json").write_text(
        json.dumps(records, indent=2) + "\n", encoding="utf-8",
    )


def main():
    require(shutil.which("lake"), "lake must be on PATH (the project pins Lean 4.19.0)")
    require(shutil.which("git"), "git must be on PATH")
    require(not (ROOT / ".lake").is_symlink(), "Project .lake must not be a symlink")
    require(not LOGS.is_symlink(), "Verification log directory must not be a symlink")
    LOGS.mkdir(parents=True, exist_ok=True)
    # Never leave a previous PASS record in place when the current run fails.
    (LOGS / "result.json").write_text(
        json.dumps({"verdict": "RUNNING"}, indent=2) + "\n", encoding="utf-8",
    )
    check_sources()
    check_dependencies("before")
    version = run("lean-version", ["lake", "env", "lean", "--version"])
    require(re.search(r"\bversion 4\.19\.0\b", version) is not None,
            "Expected Lean 4.19.0")
    require("commit 6caaee842e94" in version, "Unexpected Lean 4.19.0 compiler commit")
    run("lake-version", ["lake", "--version"])

    # Rebuild only this project's generated artifacts. Stock dependency caches
    # are retained; no author-produced project .olean file is accepted.
    build = ROOT / ".lake" / "build"
    require(not build.is_symlink(), "Project .lake/build must not be a symlink")
    if build.exists():
        require(build.is_dir(), "Project .lake/build is not a directory")
        shutil.rmtree(build)
    run("build", ["lake", "build"])
    proof = run("strict-proof", [
        "lake", "env", "lean", "-DwarningAsError=true", "CovolumeSpectrum.lean",
    ])
    require(not proof.strip(), "Unexpected proof replay output")
    axioms = run("axioms", [
        "lake", "env", "lean", "-DwarningAsError=true", "Audit.lean",
    ])
    require(axioms == EXPECTED_AXIOMS,
            "Incomplete, duplicate, reordered, unexpected, or nonstandard axiom output")
    # Check the full printed types, including all quantified hypotheses and
    # universes. The fixed source hashes and the kernel replay remain decisive.
    (LOGS / "TypeAudit.lean").write_text(TYPE_AUDIT, encoding="utf-8")
    types = run("types", [
        "lake", "env", "lean", "-DwarningAsError=true",
        ".lake/verification/TypeAudit.lean",
    ])
    require(types == EXPECTED_TYPES, "The complete expected theorem types did not match")
    check_sources()
    check_dependencies("after")
    result = {
        "verdict": "PASS",
        "proof_source_sha256": EXPECTED_HASHES["CovolumeSpectrum.lean"],
        "lean_version": version.strip(),
        "clean_project_build": True,
        "stock_packages_checked": 9,
        "theorem_types_checked": len(THEOREMS),
        "axiom_dependency_outputs_checked": len(THEOREMS),
        "axioms": ["propext", "Classical.choice", "Quot.sound"],
        "scope": "Engineering and kernel verification; semantic applicability is a separate review.",
        "commands": COMMANDS,
    }
    (LOGS / "result.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8",
    )
    print("PASS: clean build; strict source replays; all 12 theorem types and axiom outputs; "
          "source integrity and 9 clean pinned dependencies.", flush=True)
    print("Full logs: .lake/verification/")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, RuntimeError) as error:
        if LOGS.is_dir() and not LOGS.is_symlink():
            (LOGS / "result.json").write_text(
                json.dumps({"verdict": "FAIL", "error": str(error), "commands": COMMANDS},
                           indent=2) + "\n", encoding="utf-8",
            )
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)

