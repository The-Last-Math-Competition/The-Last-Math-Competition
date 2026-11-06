# Solution Review — Conjecture 00000001082 (PR 1184)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024100725`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001082; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** For fixed (m,n,k), the number of equivalence classes of MRD codes has main term q^{(k-1)(n-k+1)}(1 + O(q^{-1})); take the literal boundary case (m,n,k) = (3,2,2), with q ranging over primes.

**Decisive results.** The theorem computes the complete [2,2] MRD code universe over F_{q^3}: every 2-dimensional subspace is the full space, so there is exactly one code and one equivalence class. Its minimum rank distance is 1 and its size q^6 attains the rank-metric Singleton bound. The printed main term is q, so the relative error is 1/q - 1, which is not O(1/q). The quantified arbitrarily-large-prime failure and the IsBigO negation are exactly the failure of the printed asymptotic. The hypotheses (m = 3, n = 2, k = 2; q prime) are satisfiable and lie inside the literal unrestricted statement.

**Report correspondence.** The report states the same boundary computation, the same count 1, the same predicted term q, and the same quantified relative-error failure. It does not claim the cell-decomposition clause or any interior parameter variant.

## Disposition

APPROVED — merged as PR 1184. The submission gives a complete, formalised disproof of conjecture 00000001082.
