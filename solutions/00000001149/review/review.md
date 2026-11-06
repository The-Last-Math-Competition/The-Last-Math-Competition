# Solution Review — Conjecture 00000001149 (PR 1123)

**Submission:** lizaixi01 — `lizaixi01_submission_20261022234111`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001149; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says the m-th term is a q-binomial coefficient of p-adic absolute value p^{-m/2}, for coprime minimal-model parameters p,q. The submission takes p=2,q=5 and reads q as the integer model parameter, with the standard Gaussian coefficient at q=5.

**Decisive results.** Standard Gaussian coefficients at q=5 are rational. Every nonzero x∈Q_2 has ‖x‖=2^{-v} with v∈Z, so its norm cannot be 2^{-1/2}; no_half_integral_norm proves this, and gaussianAlgCl_ne_half_norm transfers it to the algebraic closure. no_requested_gaussian_series quantifies over all index sequences n(m),k(m) and rules out the required norm law, so no such series exists. The hypotheses are satisfiable (p=2,q=5 coprime).

**Report correspondence.** The report states the same norm obstruction and the same scope; the Lean theorem matches. The report explicitly notes that q is read as the integer model parameter and not as an independent nome.

## Disposition

APPROVED — merged as PR 1123. The submission gives a complete, formalised disproof of conjecture 00000001149.
