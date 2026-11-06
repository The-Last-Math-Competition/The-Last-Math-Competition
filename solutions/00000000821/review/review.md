# Solution Review — Conjecture 00000000821 (PR 1118)

**Submission:** lizaixi01 — `lizaixi01_submission_20261022225627`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000821; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says max|∇φ_λ|/(λ max|φ_λ|) ≥ c > 0 for all eigenfunctions. The submission reads λ as the positive Laplace eigenvalue (-Δφ_λ=λφ_λ) on the flat circle R/(2πZ).

**Decisive results.** For f_m=sin(mθ), λ_m=m^2, max|f_m|=1 and max|∇f_m|=m, so the ratio is 1/m→0. no_uniform_positive_bound proves there is no c>0 that works for all eigenpairs on the flat circle. This is a direct negation of the universal lower bound, and the hypotheses are satisfiable (the sine eigenpairs). The conclusion is the negation of the claimed existence of a positive constant.

**Report correspondence.** The report states the same positive-Laplacian convention, the sine family, the maxima, and the conclusion; the Lean theorem matches. The report explicitly does not claim the frequency reading.

## Disposition

APPROVED — merged as PR 1118. The submission gives a complete, formalised disproof of conjecture 00000000821.
