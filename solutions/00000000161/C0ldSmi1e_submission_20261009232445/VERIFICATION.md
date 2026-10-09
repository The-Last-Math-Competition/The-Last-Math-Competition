# Verification record

The result is a disproof of conjecture 00000000161. It concerns actual uniformly counted invertible matrices and actual multiplicative orders. For dimension four, every positive constant denominator gives an empty success event for all sufficiently large primes. No numerical experiment is used as proof.

## Formal verification

The frozen author files were checked with Lean 4.19.0 and Mathlib v4.19.0 (commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`). A separate engineering reviewer extracted them into a fresh project and successfully ran the submitted verifier, a clean project build, and warnings-as-errors replays of the Lake configuration and every submitted Lean source. The exact nine dependency revisions and all 7,507 tracked dependency files were unchanged before and after.

Pristine cached stock dependency objects were reused. One missing unmodified stock cardinality module was compiled in a separate source-identical library copy. This is not a claim that the entire Lean toolchain or Mathlib was rebuilt from source.

The submitted audit prints all 14 named theorem types and axiom dependencies. The independent extended audit covers all 29 logical declarations, including generated proof/equation helpers, and their 19,737-constant type/value dependency closure. The closure uses only `propext`, `Classical.choice`, and `Quot.sound`, with no unsafe or partial logical dependency. Two generated compiler runtime stages are separately inventoried and excluded from logical roots; they do not occur in that closure. There are no admitted proofs, custom axioms, or `native_decide` in the proof.

`verification/engineering/README.txt` documents exact replay commands, successful receipts, and two repaired reviewer-helper attempts. Both final portable helper files and `replay_extended.py` were actually executed successfully. The complete closure output is preserved losslessly as `kernel_closure.stdout.gz`, with compressed and uncompressed hashes. The author log remains unchanged in `lean/verification.log`; an independent replay of that verifier is preserved separately. No auxiliary numerical computation is necessary.

## Mathematical and report review

A fresh semantic reviewer read both original language versions and the rules, then reviewed every proof declaration, the required stock-library bridges, the complete LaTeX report, and both rendered PDF pages. The review passed without requested mathematical corrections. The primary agent separately read the proof and audit sources, inspected the types and raw engineering receipts, and recomputed the recorded hashes and closure assertions. These latter evidence checks are not described as another compilation.

The final report compiled successfully in the built-in LaTeX compiler and was exported with Tectonic. Both PDF pages were visually inspected by the primary agent and independently rendered and inspected by the semantic reviewer. The exported source/PDF and their hashes match the final review records. The report is two pages; its final export has no warnings.

## Contribution scope and provenance

The author received only the original conjecture, both rule sections, fixed version pins, and pristine stock dependencies. The author independently developed the argument and used a fresh helper for its generic arithmetic formalization; `lean/AUTHOR_NOTES.txt` records that division of work. Reviewers had separate roles. These are internal pre-submission checks, not a maintainer review or acceptance.

The source, operative rules, official unsolved status, public claim metadata, and visible submission history were checked before publication. The compact eligibility summary records separate observation cutoffs and binds the locally retained full evidence. Public history checks cover 2,100 observed tips, not private or undisclosed work or future activity. Eighteen textual search hits were inspected and distinguished from this conjecture; the numeric PR number 161 refers to a different conjecture.

Only this personal submission directory is added. The original conjecture is preserved as a copy, while repository source descriptions, metadata, leaderboard, and root README files are unchanged. `SHA256SUMS.json` inventories every other file in this submission. Verification summaries and log records preserve their original local paths as provenance; those paths are not required for the portable replay commands.
