# Solution Review — Conjecture 00000008262 (PR 1085)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022103738`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008262; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says the spectral condition number ric_cond of the steady Riccati covariance P∞ is at most (σ_obs/σ_sys)^2, and adds transient-decay and robustness-radius clauses. The submission refutes the first conjunct with A=diag(3/4,−3/4), H=I, equal unit isotropic noises, and P=diag(2,1/2).

**Decisive results.** Lean proves P is positive definite, satisfies the full algebraic Riccati equation with σ_sys=σ_obs=1, the closed-loop matrix is −(5/4)I and Hurwitz, the real spectrum of P is exactly {2,1/2}, and the spectral condition number is 4. The claimed bound is (1/1)^2=1, so 4≤1 fails. The example uses strictly positive, nondegenerate isotropic noises; the anisotropy is in the allowed dynamics A, which the source does not exclude. The counterexample satisfies every literal hypothesis of the first conjunct and falsifies its universal upper bound.

**Report correspondence.** The report and Lean agree on the Riccati equation, positive definiteness, closed-loop stability, exact spectrum, condition number 4, and the negation of the claimed bound. The report also gives an explicit time-dependent covariance trajectory and the Brownian filtering interpretation; it explicitly labels those as paper-only. No stronger prose claim than that labeling.

## Disposition

APPROVED — merged as PR 1085. The submission gives a complete, formalised disproof of conjecture 00000008262.
