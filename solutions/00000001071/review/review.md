# Solution Review — Conjecture 00000001071 (PR 1111)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022114815`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001071; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source names a quadratic-residue graph QR(p) with 'adjacency by ±1' and claims the deviation of its smallest eigenvalue from -2*sqrt(p) is at most p^(-1/4+epsilon), with a uniform spectral gap. The submission treats both natural readings: the standard Paley graph on F_p for p=1 mod 4 (adjacency by square differences), and the literal difference-±1 cycle C_p. Deviation is read as |lambda_min + 2*sqrt(p)|.

**Decisive results.** For the Paley graph A=(J-I+Q)/2 with Q_ab=chi(a-b), Lean proves Q^2=pI-J and column sums (p-1)/2, hence every adjacency eigenvalue lambda satisfies lambda >= -(1+sqrt(p))/2. The discrepancy is therefore at least (3 sqrt(p)-1)/2, which is unbounded along primes p=1 mod 4. For the literal cycle, maximum degree two gives |lambda|<=2 and discrepancy at least 2 sqrt(p)-2, also unbounded. Both SpectralClaim definitions are universally quantified over epsilon>0, a constant C and a cutoff N; the theorems refute them using epsilon=1/8 and arbitrary C,N. The hypotheses are satisfiable and the conclusion is the negation of the claimed error bound.

**Report correspondence.** The report states both readings, the Paley eigenvalue lower bound, the cycle degree bound, the unboundedness quantifiers and the failure at epsilon=1/8. Lean proves exactly those theorems; the report explicitly does not claim the separate uniform spectral-gap clause, which is not needed because the deviation clause is already false.

## Disposition

APPROVED — merged as PR 1111. The submission gives a complete, formalised disproof of conjecture 00000001071.
