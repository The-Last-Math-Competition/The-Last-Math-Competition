# Solution Review — Conjecture 00000004374 (PR 1208)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261026200500`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000004374; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says that beyond low degrees the next nonzero odd-degree homotopy appears in degrees that are multiples of p²−1, uniformly for all odd primes p. The submission reads the necessary existence/degree clause for an arbitrary nonzero predicate and cutoff.

**Decisive results.** For p=3, p²−1=8; any multiple of 8 is even, so no degree d can be both odd and a multiple of 8. This contradicts the clause already for p=3, independent of the homotopy predicate and cutoff. The conclusion is the negation of a necessary consequence of the filed claim; the shifted-period distinction is explicitly not claimed.

**Report correspondence.** Report and Lean agree exactly: both prove the parity obstruction for every nonzero predicate and cutoff and note that a shifted-period statement would be different. No stronger claim is made.

## Disposition

APPROVED — merged as PR 1208. The submission gives a complete, formalised disproof of conjecture 00000004374.
