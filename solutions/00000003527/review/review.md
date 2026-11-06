# Solution Review — Conjecture 00000003527 (PR 1115)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022121412`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000003527; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** For every normal ordinal function f (strictly increasing and continuous at nonzero limits), the fixed points are closed and unbounded, the standard increasing enumeration d=deriv f is normal with range exactly the fixed points, d(ω)=sup_n d(n), and separately the least fixed point above any a is nfp f a=sup_n f^[n](a). The source's 'ω-th term ... transfinite iteration limit' is read as the derivative's ω-th value; the submission also proves the iteration formula.

**Decisive results.** Lean proves closure as the equalizer of the continuous maps f and id, unboundedness from Mathlib's fixed-point theorem, the exact range and normality of Ordinal.deriv, its zero/successor/limit recursion, the omega limit, and the finite-iteration/least-fixed-point formula for every starting ordinal. FixedPointClaim universally quantifies every normal f and includes all these conclusions. The hypotheses are satisfiable (id is normal, and identity_limits is proved), and the conclusion is the source's classical claim rather than a narrowing.

**Report correspondence.** The report's theorem states the same closed/unbounded fixed-point class, normal enumeration, recursion clauses, d(ω) limit, and nfp iteration formula; it explicitly distinguishes d(ω) from iteration from zero. Lean's FixedPointClaim matches; no stronger prose claim.

## Disposition

APPROVED — merged as PR 1115. The submission gives a complete, formalised proof of conjecture 00000003527.
