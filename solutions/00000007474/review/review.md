# Solution Review — Conjecture 00000007474 (PR 1204)

**Submission:** lizaixi01 — `lizaixi01_submission_20261025065001`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007474; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the spectrum of a multiparameter quadratic operator family is a real algebraic curve whose genus is the pencil rank. The submission reads the affine parameter spectrum (parameters where the operator is not invertible) and takes the 3-parameter family T(s,t,u)=(s+t+u)² I on R.

**Decisive results.** The family is genuinely quadratic (total degree 2, nonconstant) and self-adjoint. The parameter spectrum is exactly the plane s+t+u=0; its coordinate ring is isomorphic to R[Y0,Y1], with Krull dimension 2, not 1. Hence the spectrum is not a real algebraic curve, negating the printed curve clause. The hypotheses (multiparameter, quadratic) are satisfiable.

**Report correspondence.** The report theorem matches the Lean `affine_parameter_spectrum_counterexample`; the report explicitly limits the claim to the affine parameter-spectrum reading and does not address the projective version or compute genus/rank.

## Disposition

APPROVED — merged as PR 1204. The submission gives a complete, formalised disproof of conjecture 00000007474.
