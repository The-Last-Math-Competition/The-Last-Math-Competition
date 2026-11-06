# Solution Review — Conjecture 00000004003 (PR 1103)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022113015`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000004003; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement defines the expected signature as the integral of the signature against the process distribution, then claims the expected signature determines 'the distribution' iff the Carleman condition for the moment problem holds, with the first floor(d/2) levels never determining it. I take the literal process-distribution reading: the distribution being determined is the law of the path/process on the observation interval. The report explicitly notes that a different reading, in which 'distribution' means the law of the signature or a tree-like quotient, is not addressed.

**Decisive results.** The Lean theorem negates a literal path-law determinacy statement: `CarlemanSignatureDetermination` says that any two probability laws on paths that are smooth and based a.e., satisfy the radial path-norm Carleman condition, have integrable signatures, and have equal expected signatures at every level must have equal observed laws. The counterexample uses the two Dirac laws at x_1(t)=4t(1-t) and x_2(t)=8t(1-t). Both paths start and end at 0, so their full signatures are both (1,0,0,...), hence all expected-signature levels agree. Their midpoint values differ (1 versus 2), so the observed path laws differ. Both Dirac laws satisfy the Carleman condition because their sup norms are 1 and 2, giving inverse-even-root terms 1 and 1/2, whose series diverge. Thus the literal sufficiency direction fails. The result is a universal negation over the stated class, and all hypotheses are satisfiable. The report discloses that a signature-law reading is different and is not refuted.

**Report correspondence.** The report and Lean agree on the two paths, the identical full signature, the differing midpoint values, the path-norm Carleman verification, and the negation of path-law determination. The report explicitly says the result concerns an original unaugmented process/path law and does not concern a probability law on signatures or a tree-like quotient; that is a disclosed interpretation boundary, not a contradiction between the report and Lean.

## Disposition

APPROVED — merged as PR 1103. The submission gives a complete, formalised disproof of conjecture 00000004003.
