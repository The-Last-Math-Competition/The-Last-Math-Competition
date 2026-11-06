# Solution Review — Conjecture 00000007534 (PR 1172)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261023195500`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007534; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says the invariant subspace of cohomology is computed by an idempotent projection of the group ring, and that its rank is the representation multiplicity. The submission reads this over the coefficient field F2, for X=Spec C over R with geometric base change two points and Galois group C2 acting by swap on F2².

**Decisive results.** The geometric H⁰ is the permutation module F2²; its invariants are the diagonal. In F2[C2], every element is a+bσ and squares to (a+b)·1, so the only idempotents are 0 and 1, whose images are 0 and the whole module, not the diagonal. Hence no group-ring idempotent has image the invariants. The conclusion is the negation of the idempotent-projection clause. The finite cochain/quotient model is constructed and the actions are induced on it.

**Report correspondence.** Report and Lean agree on the F2 calculation and the obstruction. The report explicitly says the scheme, real/complex fields and étale-cohomology identification are prose, not Lean, and makes no claim against a Q_l reformulation. No stronger formal claim is made.

## Disposition

APPROVED — merged as PR 1172. The submission gives a complete, formalised disproof of conjecture 00000007534.
