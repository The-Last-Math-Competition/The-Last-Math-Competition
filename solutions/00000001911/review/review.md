# Solution Review — Conjecture 00000001911 (PR 1196)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024213540`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001911; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: H_V f = p.v.∫ f(x−V(x)t)dt/t is L² bounded for Lipschitz vector fields. The submission reads the full untruncated principal value on the Euclidean plane and takes V(z)=W(z)/‖W(z)‖ with W(z)=(max(1,Re z), Im z).

**Decisive results.** The constructed V is everywhere unit and 2-Lipschitz. For the Schwartz bump f supported in radius 2, on the cone {x≥4, 0≤y≤x} the PV integral equals ∫_{r−2}^{r+2} f(...)/t dt and is ≥1/(2x). If an L² representative g existed, g² would dominate 1/(4x²) on the cone, whose integral over x≥4 diverges; contradiction. The theorem excludes every bounded L² operator representing the full PV. This is the negation of the untruncated L²-boundedness clause; the hypotheses are satisfiable.

**Report correspondence.** The report theorem matches the Lean `printed_untruncated_conjunct_false`; the report explicitly states it refutes only the untruncated full PV and not the standard truncated Stein problem or the resonance-set clause.

## Disposition

APPROVED — merged as PR 1196. The submission gives a complete, formalised disproof of conjecture 00000001911.
