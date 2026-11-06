# Solution Review — Conjecture 00000007730 (PR 1191)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024171917`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007730; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal all-moment rate clause: for centered self-adjoint tuples free over B with bounded fourth moments, the moment convergence rate is O(n^{-1}); no symmetry or vanishing third moment is assumed. Take B = C and one-entry tuples.

**Decisive results.** The theorem constructs the countable free product of C3 factors, its regular representation on ℓ²(G), the vacuum trace, and full freeness of the factor star-subalgebras. The variables Y_i = X_i/√2 have mean 0, variance 1, fourth moment 3/2, and identical polynomial laws. The actual normalized sum S_n has τ(S_n^3) = 1/√(2n), while the standard semicircle has third moment 0; the error is 1/√(2n), which is not O(1/n). The quantified arbitrarily-large-n failure and the IsBigO negation are exactly the failure of the printed rate. The hypotheses are satisfiable and the conclusion is the negation of the universal rate clause.

**Report correspondence.** The report's theorem, free-product construction, moment computations, semicircle measure and quantified rate failure match the Lean. The report explicitly scopes out even-moment-only and later cumulant/Motzkin clauses; Lean and report agree.

## Disposition

APPROVED — merged as PR 1191. The submission gives a complete, formalised disproof of conjecture 00000007730.
