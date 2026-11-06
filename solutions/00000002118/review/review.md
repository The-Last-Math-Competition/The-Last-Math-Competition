# Solution Review — Conjecture 00000002118 (PR 1214)

**Submission:** LibertychaserUS — `LibertychaserUS_submission_20261027064839`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002118; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `check.py` exited 0.

## Semantic audit

**Conjecture as filed.** The filed statement says the third cumulant of the Quicksort comparison count satisfies κ₃(n) = 2n − 6log n + C for an explicit constant C, and that the linear main coefficient is 2. The submission reads this as an exact identity for all n ≥ 2, with the natural logarithm (and also covers every base b > 0, b ≠ 1).

**Decisive results.** The theorem negates the exact universal identity. The formal kappa3 is defined from the standard Quicksort comparison recursion C_n = (n-1) + C_J + C'_{n-1-J} with J uniform on {0,...,n-1}; kappa3 is the third central moment, which equals the third cumulant. Lean computes kappa3 2 = 0 and kappa3 3 = -2/27 exactly. The claimed identities at n=2 and n=3 force 6(log 3 − log 2) = 56/27, i.e. log(3/2) = 28/81 ≈ 0.3457; Lean proves log(3/2) > 0.39 from the alternating-series bound, a contradiction. The any-base theorem additionally uses n=4 and log 2 < 0.6931471808 to rule out every base. The counterexample n=2,3 lies squarely in the filed domain; the conclusion is the negation of the exact claim, not a special case outside the regime.

**Report correspondence.** The report's main theorems are exactly the two Lean theorems. The report's small values, hand checks at n=2,3,4, and logarithm inequalities match the Lean lemmas. The report explicitly states that the asymptotic reading κ₃(n)=2n−6log n+C+o(1) is not refuted by the formal argument; this is an honest limitation, and the filed formula is written as an exact identity.

## Disposition

APPROVED — merged as PR 1214. The submission gives a complete, formalised disproof of conjecture 00000002118.
