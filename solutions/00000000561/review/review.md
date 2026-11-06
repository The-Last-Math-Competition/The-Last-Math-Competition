# Solution Review — Conjecture 00000000561 (PR 1194)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024195756`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000561; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: for an N-Koszul algebra, the Hilbert series of E=Ext_R^*(k,k) is rational with denominator ∏(1−t^{d_i}), where d_i is the N-Koszul degree sequence. The submission reads the denominator as a finite polynomial product with positive integer exponents and allows any such finite family.

**Decisive results.** The example A=Q⊕Q² (square-zero) is proved to be connected quadratic 2-Koszul via a full linear minimal projective resolution. The theorem proves dim Ext^n=2^n and H(t)=1/(1−2t). For any finite positive d_i, D(t)H(t)=P(t) would force (1−2t)P(t)=D(t); evaluating at t=1/2 gives 0=D(1/2)=∏(1−2^{-d_i})≠0, contradiction. Thus the printed denominator clause fails. The hypotheses are satisfiable and the conclusion is the negation of the clause.

**Report correspondence.** The report theorem matches Lean: the algebra presentation, Koszul resolution, Ext dimensions, Hilbert identity, and finite-denominator obstruction are all formalized. The report explicitly limits the claim to the finite polynomial denominator reading.

## Disposition

APPROVED — merged as PR 1194. The submission gives a complete, formalised disproof of conjecture 00000000561.
