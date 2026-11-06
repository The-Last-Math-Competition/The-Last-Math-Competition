# Solution Review — Conjecture 00000007803 (PR 1087)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022104309`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007803; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says that for an isotropic log-concave sequence X_i, the distribution of M_n/√n−c_n converges to a Gumbel-type extreme value law, with c_n=√(2 log n)/√n and correction term (log log n)/(√(2 log n)√n), and adds an L_K/thin-shell relation. The submission uses iid samples uniform on [−√3,√3] in dimension one.

**Decisive results.** Lean proves the uniform law on [−√3,√3] has the actual density, is log-concave, centered, and has second moment one, so it is isotropic in dimension one; it constructs the genuine infinite product measure and proves independence and that all coordinates are bounded by √3 almost surely. Hence the running maximum M_n is bounded, M_n/√n→0, and both c_n and the correction term tend to zero. The actual normalized maximum Z_n tends to zero almost surely, and its CDF at 1 is eventually one, whereas every standard Gumbel CDF is continuous and strictly below one at 1. Therefore no CDF convergence to a nondegenerate Gumbel law holds. The source does not exclude dimension one, bounded support, or iid sampling; the counterexample satisfies the literal hypotheses and falsifies the first distributional clause.

**Report correspondence.** The report and Lean agree on the uniform density, log-concavity, isotropy, product measure, bounded maximum, vanishing center/correction, almost-sure zero limit, and the CDF obstruction. The report explicitly uses the standard continuity-point characterization of weak convergence and labels the full weak-convergence equivalence and the Gumbel measure construction as paper-level; the Lean proves the necessary CDF non-convergence. No stronger prose claim beyond that disclosure.

## Disposition

APPROVED — merged as PR 1087. The submission gives a complete, formalised disproof of conjecture 00000007803.
