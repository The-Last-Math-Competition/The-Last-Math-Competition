# Conjecture 00000007847

For the binary one-variable program max x subject to x <= 1 and x <= 2, the unique relaxed optimum and the integer optimum are both 1. Standard independent Bernoulli rounding therefore returns 1 almost surely. Its actual expected profit-to-optimum ratio is 1, whereas the claimed two-row expression is 3/4.

## Scope and formal correspondence

The refuted clause is the exact instance-wise expectation asserted for r(A). The two rows are distinct inequalities; the source imposes no irredundancy condition. The relaxed optimizer is unique, the integer optimum is positive, and every rounded outcome is feasible. Normalizing by either the LP or IP optimum gives the same ratio. This does not dispute a lower bound or a worst-case guarantee for a separately restricted problem family.

The Lean project defines the real matrix constraints, the linear objective, LP feasibility, and binary feasibility on Fin 1 and Fin 2. It proves the unique LP maximizer and the integer optimum. The rounding distribution is Mathlib PMF.bernoulli 1, whose coordinate expectation is checked. A Bochner integral computes the actual normalized objective expectation and proves that it differs from 1-(1-1/2)^2.

## Files and reproduction

- `main.tex` and `main.pdf`: full disproof and Lean correspondence.
- `SOURCE.md`: unchanged bilingual conjecture, byte for byte.
- `lean/`: complete portable project pinned to Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
- `verification/`: actual build logs, theorem axioms, hashes, native compiler result, source provenance and reviews.

Inside `lean/`, run `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. A new machine can retrieve the official dependency artifacts with `lake exe cache get`. All transitive revisions are pinned in the manifest; there are no private dependencies or local paths. Run `tectonic main.tex` from the submission directory to export the PDF. No auxiliary numerical computation is needed.

The submission's own artifacts are freshly rebuilt without a reused `.lake` directory; only verified official dependency caches are reused. The native desktop LaTeX compiler succeeded on the recorded source. Tectonic produces the distributed PDF, and every rendered page is visually checked. Author self-review and parent-agent review are distinct records; no external independent review is claimed.
