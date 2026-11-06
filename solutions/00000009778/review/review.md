# Solution Review — Conjecture 00000009778 (PR 1112)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022115051`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009778; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** The Volterra operator on L2(0,1) has kernel 1_{0<=t<=x}. The source claims its singular values have leading term 1/(pi n) with only odd inverse-power corrections, each coefficient a Bernoulli combination. The submission computes the actual singular values s_n=1/(pi(n-1/2)) and refutes the odd-only correction clause.

**Decisive results.** The paper proves V*V has eigenvalues 1/(pi^2(n-1/2)^2), so s_n=1/[pi(n-1/2)]. Then n^2(s_n-1/(pi n)) = n/[pi(2n-1)] -> 1/(2 pi) != 0. Any expansion s_n=1/(pi n)+c/n^3+o(n^{-3}) containing only odd powers forces the same scaled difference to tend to 0; contradiction. Lean proves the asymptotic core for every nonnegative sequence satisfying the Gram formula and every integer reindexing. The spectral identification is a standard paper bridge, not assumed inside Lean. Thus the odd-only clause is false, so the filed conjunction is false.

**Report correspondence.** The report gives the actual L2 operator/adjoint/spectral proof, the formula s_n=1/[pi(n-1/2)], the nonzero limit 1/(2 pi), and the odd-expansion contradiction. It explicitly labels the L2 spectral identification as a substantive bridge outside Lean; Lean proves the conditional asymptotic core and the report claims no stronger formal result.

## Disposition

APPROVED — merged as PR 1112. The submission gives a complete, formalised disproof of conjecture 00000009778.
