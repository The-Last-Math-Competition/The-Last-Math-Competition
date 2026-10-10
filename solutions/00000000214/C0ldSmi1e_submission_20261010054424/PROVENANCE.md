# Author provenance and verification

The independent author received only the exact bilingual statement, the English and Chinese submission rules, a toolchain/manifest and an input provenance manifest in `/private/tmp/tlmc214-clean-author-input`. The supplied input bundle hash and every supplied file hash were verified; see `evidence/input-hash-verification.json`.

The author derived the elementary sequence obstruction, actual-partition encoding, hook-partition lower bound and logarithmic estimates afresh. A child agent proved the generic real-sequence theorem using only the same clean input, the parent's newly developed mathematical idea, and stock Lean/Mathlib. Its complete development and audit are retained in `evidence/sequence-development/`.

No repository checkout, Git history, prior submission, prior candidate proof, external mathematical proof, or earlier scratch directory was read. No Git operation or external publication/message was performed. The only library context was pinned stock Mathlib and the specified Lean runtime. Root-level eligibility and independent review work was kept outside the author's mathematical context; the author received no mathematical proof hint from it.

## Mathematical artifacts

The canonical source files are under `TLMC214/`, with umbrella import `TLMC214.lean`. The final concrete theorem has no assumptions. The generic lemma's assumptions are all proved for `Real.log (Fintype.card (Nat.Partition n) : ℝ)`. The scope, exact difference convention, full eventual quantifier and undefined layer wording are addressed in `report.tex`.

## Retained attempts and receipts

- `evidence/author-development/run-0001` through `run-0008` retain every author-side Lean attempt, its exact source snapshot, stdout, stderr, exit status, command, source hash and runtime path.
- Attempts 1–4 failed during import/API development; attempt 5 established the partition upper bound; attempt 6 added the actual-object lower bound; attempt 7 was a successful library-signature probe; attempt 8 proved all needed logarithmic growth facts.
- The sequence child's failed and successful attempts, inspection outputs, commands and receipts are separately preserved.
- `evidence/check-0001` is the first integrated fresh build, which succeeded but reported an out-of-date-manifest warning because the copied manifest's `inputRev` used the tag while the project declaration used the exact commit. The `inputRev` was aligned to the same pinned commit without changing the dependency revision.
- The first integrated build directory was moved aside, and `check-0002` is a fresh build of all submission modules with the corrected manifest, exit 0 and no warning.
- `check-0003` through `check-0007` directly replay each canonical Lean source with `-DwarningAsError=true`, all exit 0 and empty stdout/stderr.
- `check-0008` directly replays `CheckAxioms.lean`, exit 0. All three capstones list only `propext`, `Classical.choice` and `Quot.sound`.
- `native-latex-compile.json` records the native standalone LaTeX compiler's success and the exact source hash. PDF export and visual inspection are the parent review's remaining artifact check at handoff.

Read-only initial file and library inspections, file creation operations, and the native editor calls also have their tool-call receipts in the conversation record. No failed compiler run or compiler log was overwritten. Archived exploratory Lean sources use the `.lean.txt` extension so they are clearly records, not build targets. Their original contents are unchanged. The preserved exploratory snapshots can contain compiler-generated diagnostics mentioning incomplete declarations; they are historical failed attempts, not imports or proof dependencies of the delivered project.

## Dependency handling

Local testing used private copy-on-write copies of the stock pinned Mathlib tree and its dependency packages inside this project's disposable `.lake/packages`. No stock runtime, source, cache or dependency was modified. The local copy supplies cached stock imports while all project modules were built from their current source. No absolute local path is present in `lakefile.lean`, `lake-manifest.json` or `lean-toolchain`; normal reproduction uses the pinned Git dependency.

At author handoff, `SHA256SUMS.json` hashed the delivered source, report source, configuration and evidence, excluding itself, the disposable `.lake` directory, and later parent-generated artifacts. That original manifest is preserved as `parent-verification/author-SHA256SUMS.json`, and the original report as `parent-verification/author-report.tex`. The final top-level manifest covers the assembled submission. The author makes no claim about publication eligibility or maintainer acceptance.

## Parent completion

The parent obtained a separate full semantic review, an independent fresh build, direct source replays with warnings treated as errors, and a full originating-module declaration/dependency audit. The independent review is included under `independent-review/`; the parent's source and engineering checks are under `parent-verification/`.

The initial PDF export found one overflowing display. The parent split its two unchanged definitions into aligned lines, compiled the revised source successfully with both the native editor compiler and Tectonic, and visually inspected all four pages. The initial warning and source are preserved, and the final export has no warnings. No mathematical source changed during this step.
