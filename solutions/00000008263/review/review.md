# Solution Review — Conjecture 00000008263 (PR 1090)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022105135`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008263; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: systematic resampling halves the variance relative to multinomial resampling (a variance-halving law). The submission tests the usual conditional variance of the equally weighted empirical mean of a fixed observable, for the standard systematic inverse-CDF algorithm with the given particle ordering, and formalizes the universal halving assertion over all rational observables on a fixed positive four-particle population.

**Decisive results.** For weights (1/8,3/8,1/8,3/8) and observable (1,0,1,0), the actual inverse-CDF systematic scheme has two equiprobable phases with estimator 1/2 and 0, so variance 1/16; the genuine 4^4 multinomial product law gives variance 3/64. Both means are 1/4, so systematic variance is strictly larger, refuting Var_sys ≤ Var_mult/2. The weight vector and observable are legal positive data, so the hypotheses are satisfiable and the conclusion is the negation of the halving claim.

**Report correspondence.** The report's variance values, phase selection table and multinomial calculation match the Lean declarations exactly. The report discloses that the continuous-uniform-to-two-stratum identification is paper-only and that no random permutation or special ordering is assumed; the Lean formalizes every offset in [0,1/4) and the finite probability laws.

## Disposition

APPROVED — merged as PR 1090. The submission gives a complete, formalised disproof of conjecture 00000008263.
