# Solution Review — Conjecture 00000000479 (PR 1222)

**Submission:** jiakeboge — `jiakeboge_submission_20261030002730`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000479; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The conjecture asserts that the number N_k of order-n Aztec-diamond matchings with exactly k NW-SE main-diagonal lozenges has v2(N_k)=0 for k=0 mod 4 and v2(N_k)=1 otherwise, with period 4.

**Decisive results.** Lean enumerates all matchings of the order-1 and order-2 Aztec diamonds and kernel-checks the stratum sizes. At order 2 the k=2 stratum has 3 matchings and the k=6 stratum has 1, both odd, whereas the conjecture requires 2-adic valuation 1. At order 1 the k=2 stratum has 1 matching, also odd. The report identifies the NW-SE main-diagonal orientation with the horizontal domino count; reflection in x=y exchanges the two orientations, so the stratum sizes are the same for either choice. This is a literal counterexample to the printed valuation formula.

**Report correspondence.** The report, README and Lean agree on the order-1 and order-2 counts and on the orientation convention. The order-3/order-4 numerical remarks are supplementary and not needed for the formal refutation.

## Disposition

APPROVED — merged as PR 1222. The submission gives a complete, formalised disproof of conjecture 00000000479.
