# Solution Review — Conjecture 00000004993 (PR 1205)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261025195100`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000004993; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says all attainable b_3 values are odd and the minimal attainable value is 1186. The submission reads 'minimum' in the ordinary attained sense and uses only these two explicit clauses.

**Decisive results.** If 1186 is the minimum, then 1186 is attainable; if all attainable values are odd, then 1186 is odd. But 1186=2·593 is even. This contradiction is universal over every attainable predicate and does not assume any Spin(7) example. The conclusion is the negation of the conjunction; the lower-bound half is not needed.

**Report correspondence.** Report and Lean agree exactly: both prove the arithmetic contradiction for every attainable set and note that the geometric/twist-sum clauses cannot repair an inconsistent conjunction. No stronger claim is made.

## Disposition

APPROVED — merged as PR 1205. The submission gives a complete, formalised disproof of conjecture 00000004993.
