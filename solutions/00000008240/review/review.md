# Solution Review — Conjecture 00000008240 (PR 1092)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022105459`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008240; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: folk_delta, the critical discount for cooperation, equals the raw ratio (one-period defection payoff)/(cooperative payoff). The submission reads the critical discount as the infimum over discounts admitting a pure history-dependent cooperative SPE, and reads the ratio as T/R for the standard stage game T=3,R=2,P=1,S=0.

**Decisive results.** The Lean defines the actual stage game, arbitrary pure history-dependent profiles, recursive deviation trajectories, convergent discounted payoffs, compliance, cooperation and SPE. It proves grim trigger is an SPE at δ=1/2, cooperates forever from the empty history, and hence critical ≤ 1/2. Since T/R=3/2, the equality critical=T/R is false. The game satisfies the standard PD ordering T>R>P>S and the hypotheses are satisfiable; the conclusion is the negation of the first conjunct.

**Report correspondence.** The report's Theorem, payoff table, Bellman inequalities and critical-value argument match the Lean. The report explicitly says it does not interpret 'defection payoff' as a normalized payoff difference and that the standard (T-R)/(T-P) formula is a different assertion; no stronger claim than the Lean is made.

## Disposition

APPROVED — merged as PR 1092. The submission gives a complete, formalised disproof of conjecture 00000008240.
