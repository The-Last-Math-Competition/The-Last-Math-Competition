# Solution Review — Conjecture 00000008875 (PR 1201)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261024192000`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008875; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says the unique right vertical of a thermograph is half-integral. The submission reads a wall coordinate q as half-integral when 2q∈Z and uses the standard numerical base case: the thermograph of a number v at positive temperatures is the vertical line at v. It takes Q={0|{0|1}}=1/4, which is not equivalent to any nimber.

**Decisive results.** Q is a number of value 1/4; its positive-temperature right wall/mast is the vertical line at 1/4, and 2·(1/4)=1/2 is not an integer. Q is not equivalent to any nimber because its left option 0 prevents Q≤0 and (for n>0) the right option 0 of *n prevents Q≤*n. Thus the half-integrality clause fails even after excluding the named star exception. The conclusion is the negation of a necessary consequence of the filed clause.

**Report correspondence.** Report and Lean agree on Q=1/4, non-half-integrality, and non-equivalence to every nimber. The report explicitly says the Lean implements only the numerical base case and not general cooling/thermography of non-number games; the semantic link is the standard numerical thermograph fact cited to Berlekamp.

## Disposition

APPROVED — merged as PR 1201. The submission gives a complete, formalised disproof of conjecture 00000008875.
