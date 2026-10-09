# Conjecture 00000009755

One fixed theorem is attempted by a fixed generator that returns its genuine Lean proof with probability 1/2 and otherwise returns failure. Four independent fair bits give exact pass-at-1, pass-at-2, and pass-at-4 probabilities 1/2, 3/4, and 15/16. Any affine log-log law would require (15/16)(1/2)=(3/4)^2, which is false.

## Scope and formal correspondence

The fixed theorem, generator, and deterministic acceptance rule are identical for every sampling count, so there is no movement between difficulty strata or mixture of tasks. Every real slope and intercept are excluded, without assuming a numeric definition of difficulty. The disproof concerns the universal exact law, not approximate empirical fits for a specified prover.

The Lean project constructs the actual 16-point probability measure for four independent fair binary choices, proves total mass one and joint pattern probabilities, and uses Option (PLift True) for a successful actual proof or failure. The pass event is at least one proof among the first k attempts. Kernel-checked event cardinalities are 8, 12, and 15; their measure values determine passRate. Real.log identities and injectivity then rule out all affine log-log laws at 1, 2, and 4 and throughout the allowed sampling range.

## Files and reproduction

- `main.tex` and `main.pdf`: full disproof and Lean correspondence.
- `SOURCE.md`: unchanged bilingual conjecture, byte for byte.
- `lean/`: complete portable project pinned to Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
- `verification/`: actual build logs, theorem axioms, hashes, native compiler result, source provenance and reviews.

Inside `lean/`, run `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. A new machine can retrieve the official dependency artifacts with `lake exe cache get`. All transitive revisions are pinned in the manifest; there are no private dependencies or local paths. Run `tectonic main.tex` from the submission directory to export the PDF. No auxiliary numerical computation is needed.

The submission's own artifacts are freshly rebuilt without a reused `.lake` directory; only verified official dependency caches are reused. The native desktop LaTeX compiler succeeded on the recorded source. Tectonic produces the distributed PDF, and every rendered page is visually checked. Author self-review and parent-agent review are distinct records; no external independent review is claimed.
