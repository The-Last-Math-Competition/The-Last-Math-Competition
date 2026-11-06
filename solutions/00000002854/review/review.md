# Solution Review — Conjecture 00000002854 (PR 1086)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022104017`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002854; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says global identifiability of a SEM holds iff the Jacobian rank deficit at the generic point is zero, with any deficit compensated by additional instrumental-variable moment conditions. The submission uses a one-factor Gaussian SEM Y=(aλ+b)H+E with H,E independent standard Gaussian, both variances fixed at one, and λ∈R.

**Decisive results.** Lean computes the observed covariance as (aλ+b)²+1 and the Jacobian as 2(aλ+b); for a=1,b=0 it is full rank outside the proper exceptional set {0}. But λ and −λ are distinct parameters with the same observed covariance and the same complete observed Gaussian law (proved by the pushforward under the latent reflection). Hence the model is not globally identifiable in the strict labelled-parameter sense even though the generic rank deficit is zero. This refutes the sufficiency direction of the filed equivalence; the instrumental-variable compensation clause cannot repair a case with no generic deficit. The parameter space is the labelled real loading, with no sign quotient or positive-loading restriction; the paper discloses that such quotients would change the problem.

**Report correspondence.** The report and Lean agree on the covariance formula, the Jacobian, the generic full rank, the λ/−λ covariance equality, the full-law equality, and the negation of RankCriterion. The report explicitly states that it does not refute identifiability after a latent-sign quotient or a positive-loading restriction, and does not address a particular instrumental-variable specification. No stronger prose claim beyond that scope.

## Disposition

APPROVED — merged as PR 1086. The submission gives a complete, formalised disproof of conjecture 00000002854.
