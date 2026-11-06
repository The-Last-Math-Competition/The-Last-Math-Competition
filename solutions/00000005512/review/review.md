# Solution Review — Conjecture 00000005512 (PR 1088)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022104324`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005512; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: at the supermarket mean-field fixed point the survival tail is an explicit hyperbolic-type power law in the selection count, with the queue-length exponent doubled and the power-tail exponent diverging linearly in the sampling count. The submission reads this as a genuine power-law tail in queue length (at d=2) and in selection count (at fixed k=2), defining a power tail via the necessary condition of a positive eventual polynomial lower envelope.

**Decisive results.** At load 1/2 and d=2 the unique FixedPoint is q_k = 2^{-(2^k-1)}, which decays faster than every polynomial, so no finite power-law exponent exists in queue length. For every d≥1 the sequence q^(d)_0=1, q^(d)_{k+1}=(1/2)(q^(d)_k)^d is a fixed point of the actual d-choice drift, is the survival tail of a normalized probability law, and has q^(d)_2=2^{-(d+1)}, so no power-law tail in d either. The hypotheses (0<ρ<1, q0=1, nonneg, decreasing, q→0, all drift equations) are satisfiable and the example satisfies them. The conclusion negates the power-tail conjuncts, so the conjunction is false.

**Report correspondence.** Report Theorems 1-2 match the Lean declarations exactly: uniqueness, closed form, survival-tail normalization, weighted tail limits, the d-choice fixed-point family, and the two negation theorems. The report explicitly says the alternative d-th-power recursion reading of the source is correct and is not refuted. No stronger prose claim than the formalized results.

## Disposition

APPROVED — merged as PR 1088. The submission gives a complete, formalised disproof of conjecture 00000005512.
