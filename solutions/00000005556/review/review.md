# Solution Review — Conjecture 00000005556 (PR 1089)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022104953`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005556; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the characteristic polynomial of a unit-root crystal is determined explicitly by its Newton polygon, and in the unit-root case is uniquely determined by the pure weight. The submission reads 'determined' as: equal Newton polygons (and equal pure weight) imply equal characteristic polynomials, for rank-one unit-root F-crystals over Spec F_3.

**Decisive results.** positiveCrystal and negativeCrystal are actual Z_3-line F-crystals with Frobenius +1 and -1; both have unit-root coefficient (norm 1, valuation 0) and pure weight zero, and their characteristic polynomials are X-1 and X+1. Their Newton polygons are the same horizontal segment from (0,0) to (1,0). Thus the universal Newton-polygon determination claim and the pure-weight determination claim are both false; the hypotheses are satisfiable and the conclusion is the negation of the filed determination clause.

**Report correspondence.** The report's Theorem matches the Lean: same Newton polygon, equal pure weight zero, distinct char polys, and non-conjugacy. The report explicitly notes that the weaker reading 'pure weight determines only the Newton polygon' is not refuted; the Lean does not claim otherwise.

## Disposition

APPROVED — merged as PR 1089. The submission gives a complete, formalised disproof of conjecture 00000005556.
