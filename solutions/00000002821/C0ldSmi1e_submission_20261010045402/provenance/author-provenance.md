# Author provenance: conjecture 00000002821

The authored project is `/private/tmp/tlmc2821-proof`. The exact frozen
source inventory and SHA-256 values are in `SOURCE_HASHES.json`; report.tex
is part of that freeze. No further authored-source changes are planned.

## Clean input

The only conjecture input was `/private/tmp/tlmc2821-clean-author-input`:
ORIGINAL.md, RULES.en.md, RULES.zh-CN.md, lean-toolchain, lake-manifest.json,
manifest.json and SHA256SUMS.json. All seven were read. All claimed hashes
were checked, including the SHA256SUMS.json hash
`67647a5e3e405c079ce8f515bc45528a29bb3be717027254d86acadf4b5eeb3f`.
`INPUT_HASHES.json` records actual hashes and `input/` preserves exact bytes.

No repository solutions, Git/PR/history, other conjectures, selector outputs,
private eligibility/review records, other scratch proof projects, agent
rosters, other threads, or internet were inspected. Parent messages supplied
scope/checklist guidance only. No previous mathematical argument was supplied.

## Allowed stock input and compiler

All mathematical library input came from the read-only stock tree
`/private/tmp/tlmc-standard-library-419/mathlib`, pinned to Mathlib v4.19.0,
revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`, including that tree's
stock dependency build outputs under `.lake/packages`.
`STOCK_SOURCE_TREE_HASHES.json` freezes all Mathlib .lean source files as a
conservative provenance superset of source searches and actual text reads.
Source searches/reads concerned the absence of an LDP definition, Dirac and
probability measures, measure operations, ENNReal logs and inverses, EReal
coercions, semicontinuity, finite sets and liminf/limsup convergence.
Lean compilation consumed the standard transitive .olean dependency closure.

The Lean executable was exclusively
`/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin/lean` (4.19.0),
with hash in `LEAN_BINARY_HASH.json`. Its standard runtime libraries are
compiler input. No nonstock file in the parent runtime was inspected.

Only missing stock module `Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog`
was compiled privately. The exact stock source was compiled unchanged:
SHA-256 `51f9f2f6ddf46412980fa52adc4493ab0c6b1c588f4bb6d57bc2d81afe48bf8e`.
Private output is under `stock-olean/`; that overlay also contains symlinks
to read-only stock build outputs. The compiler never targeted a stock path.
`stock-compiled.jsonl` records the first failed dependency-resolution attempt
and the successful replay, with distinct original logs and source hashes.

## Current-task helper

A fresh helper was given the exact same clean-input/library boundary and
only the author's independently developed two-atom construction. Its sole
mathematical subtask was the normalized extended-logarithm limit. The source
`/private/tmp/tlmc2821-limit-helper/Limits.lean` was inspected, copied verbatim
to `Conjecture2821/Limits.lean`, and independently compiled again in the
author's private overlay. Its source hash is
`75de72486986ddb28dcc66f94f2b77f456653270b11a5237191706382b8726c8`.
`helper-evidence/` copies the helper's provenance, hashes and strict-replay
evidence. The helper's first two failed-log files were overwritten during
its initial iterations. The helper preserved transcript copies and fresh
reproductions, explicitly labeled as such. Those are not original raw
captures. This limitation is also disclosed in report.tex.

## Compilation and audit status

Every authored Lean file compiled successfully, then all four were replayed
with `-DwarningAsError=true`. The successful strict-replay logs are:

- `logs/Basic-1791607879478155000.log`
- `logs/Limits-1791607881019923000.log`
- `logs/LDP-1791607882727042000.log`
- `logs/Conjecture2821-1791607886609105000.log`

All printed axiom lists contain exactly propext, Classical.choice and
Quot.sound. Main-author logs use unique filenames from the first attempt
onward; failures remain untouched and separate from successful records.
`build_local.py` is only an environment-specific compiler orchestrator and
was executed; it is not mathematical evidence beyond the captured Lean runs.
There are no mathematical auxiliary computations or scripts.

The portable project includes a pinned lakefile, toolchain, full transitive
manifest, README and `verify.sh`. Only the manifest's project name was changed
from the supplied neutral name; all dependency pins are unchanged. The author
performed direct Lean source compilation, not a fresh full Lake package build.
The parent is responsible for independent full Lake engineering validation,
fresh semantic review, native LaTeX compilation/export and PDF visual QA.
No report PDF is claimed as produced by this author.

The theorem/definition source inventory is exactly:
`Conjecture2821/Basic.lean`, `Conjecture2821/Limits.lean`,
`Conjecture2821/LDP.lean`, and root `Conjecture2821.lean`.
The first defines the actual measure/rate; the second proves logarithm
limits; the third states/proves the standard LDP and universal refutation;
the root imports everything and prints axiom dependencies.
