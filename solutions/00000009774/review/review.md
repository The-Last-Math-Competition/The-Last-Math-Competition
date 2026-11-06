# Solution Review — Conjecture 00000009774 (PR 1101)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022112228`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009774; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement is Szego's strong limit theorem: log D_n = n L + (secondary term) + o(1), with the secondary coefficient supposedly determined by corner angles and vanishing on smooth boundaries. I read the 'secondary term' as the constant term after the leading nL term, i.e. log D_n - nL; the unit circle is a smooth boundary with no corners, and f(theta)=5/4+cos(theta) is a positive real-analytic symbol on it.

**Decisive results.** Lean defines the actual finite-section Toeplitz matrices with coefficients c_0=5/4, c_{±1}=1/2, proves the tridiagonal determinant formula D_n=(4/3)(1-4^{-(n+1)}) for every n, and proves log D_n -> log(4/3)>0 and log D_n/n -> 0. For a=1/2 the formal leading limit is L=0, so the centered secondary term tends to log(4/3), not 0. `conjecture9774_false` negates the universal smooth-vanishing subclause. The example is a smooth positive symbol on the unit circle, so it satisfies the smooth-case hypotheses. This is a counterexample to the claimed vanishing of the smooth secondary term and to the absence of a global correction.

**Report correspondence.** The report and Lean agree on the symbol, the Toeplitz matrix, the determinant formula, both limits, and the negation of the smooth-vanishing subclause. The report explicitly lists the paper-only Fourier-coefficient, Hardy-space, circle-geometry, and mean-log bridges; Lean independently proves the leading limit is 0, which is the value needed for the formal contradiction.

## Disposition

APPROVED — merged as PR 1101. The submission gives a complete, formalised disproof of conjecture 00000009774.
