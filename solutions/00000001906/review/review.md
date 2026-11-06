# Solution Review — Conjecture 00000001906 (PR 1195)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024205224`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001906; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the Rubio de Francia arbitrary-interval square-function constant C_p satisfies C_p ~ c p^{1/2} as p→∞. The submission reads the standard unweighted real-line rough square function with the usual Fourier normalization and tests the singleton interval family [0,1].

**Decisive results.** For every admissible C and p≥2, the Lean theorem derives C(p) ≥ p/(8πe) by applying the singleton inequality to f_R=1_{[-R,R]}, R=e^p. The projection has imaginary part ≥(p−1)/(2π) on [R+1,R+2], while ||f_R||_p≤2e, so C(p) is at least linear. Hence C is not O(√p) and C(p)/√p has no finite limit; this negates the printed p^{1/2} asymptotic. The hypotheses are satisfiable (the optimal constant is admissible).

**Report correspondence.** The report theorem matches the Lean `no_sqrt_bigO` and `no_finite_sqrt_coefficient`; the report states the real-line unweighted rough model and the singleton reduction. No stronger claim about the optimal constant.

## Disposition

APPROVED — merged as PR 1195. The submission gives a complete, formalised disproof of conjecture 00000001906.
