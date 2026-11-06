# Solution Review — Conjecture 00000002819 (PR 1091)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022105333`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002819; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: in the independent case the large-deviation rate function of subadditive functionals is always linear (affine) in the deviation level. The submission reads 'rate' as the rate function I(x) in the standard LDP at linear speed N, and allows an arbitrary affine I(x)=ax+b.

**Decisive results.** The Lean builds the genuine infinite product of standard Gaussians, proves coordinate independence, and shows the block sums are additive hence subadditive. For the sample-mean laws it proves the Chernoff bound P(M_N>1) ≤ exp(-N/2) and that every nonempty real interval has positive probability. The full epsilon-form LDP definition ranges over all open and closed sets; nonnegativity forces a=0, normalization forces b=0, and the open-set lower bound on (1,2) contradicts the exponential tail bound. Hence no affine LDP rate exists; the hypotheses are satisfiable and the conclusion is the negation of the universal linearity claim.

**Report correspondence.** The report's Theorem, Chernoff bound, LDP definition and contradiction match the Lean. The report explicitly says the alternative reading in which only the LDP speed is linear is not refuted, and that the paper proof that x^2/2 satisfies the full LDP is optional and not formalized. No stronger formal claim is made.

## Disposition

APPROVED — merged as PR 1091. The submission gives a complete, formalised disproof of conjecture 00000002819.
