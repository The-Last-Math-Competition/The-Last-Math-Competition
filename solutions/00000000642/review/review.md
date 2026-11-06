# Solution Review — Conjecture 00000000642 (PR 1133)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023032034`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000642; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says the image of the LKB representation is Markov-invariant at the determinant level, yielding the Jones value, and has zero-dimensional kernel. The submission reads 'Markov-invariant at the determinant level' literally as invariance of the ordinary unnormalized determinant, and refutes it on the standard positive elementary Markov stabilization B2→B3, β↦βσ2.

**Decisive results.** Lean works over K=Q(q,t), uses the standard Krammer/LKB fraction-field matrix model, constructs actual homomorphisms ρ2:B2→GL1(K) and ρ3:B3→GL3(K) from the Artin presentations, and proves det ρ2(1)=1 while det ρ3(σ2)=tq³. It proves tq³≠1 in K (by injectivity and evaluating the polynomial identity at 0), so `raw_determinant_changes` holds; `not_positive_markov_invariant` negates determinant invariance for all positive stabilizations, and `determinant_changes_in_any_bases` shows the discrepancy survives every change of basis. This directly negates the explicit determinant-level Markov invariance clause on a genuine Markov move.

**Report correspondence.** The report/PDF state the same standard matrices, the same B2/B3 presentations, the same positive stabilization, and the same determinant comparison; the Lean theorems match. The report explicitly confines itself to the unnormalized determinant and makes no independent Jones/kernel claim; it discloses that the homological identification is cited from Bigelow rather than reconstructed in Lean.

## Disposition

APPROVED — merged as PR 1133. The submission gives a complete, formalised disproof of conjecture 00000000642.
