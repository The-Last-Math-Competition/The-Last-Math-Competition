# Solution Review — Conjecture 00000000358 (PR 1161)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023182730`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000358; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** For the Leech lattice (Wilson's three-condition integer coordinates with the Golay code and standard scale a=1/sqrt8), the error term of N(t)/vol(tB) has cofinal amplitude at least c t^11 for some c>0; B is a fixed bounded body of positive finite volume (the source leaves B unspecified).

**Decisive results.** Lean proves for every binary code C (hence for the Golay code), every a>0, every bounded B with 0<vol(B)<∞, every center b and every c>0, that |N(t)/vol(tB)-b| is bounded for t≥1. The count is the actual finite ncard of the intersection with t•B, bounded by the actual integer box, and vol(t•B)=t^24 vol(B) is Mathlib's genuine Lebesgue scaling. Therefore no cofinal c t^11 lower bound can hold; this is exactly the negation of the printed amplitude clause. The unit-ball and standard-scale instance is included, and no count or volume value is assigned as a definition.

**Report correspondence.** report.tex Sections 1-4 match the Lean definitions and bounds (pointCount, normalizedCount, scaled_volume, CofinalAmplitude, no_normalized_power_amplitude). The PDF text matches. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1161. The submission gives a complete, formalised disproof of conjecture 00000000358.
