# Solution Review — Conjecture 00000007991 (PR 1074)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022095240`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007991; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source claims, among other things, that the optimal p-Laplace Hölder exponent α(p) has slope limits -∞ and +∞ at the endpoints p→∞ and p→1, i.e. that the ordinary derivative dα/dp tends to -∞ at infinity. The submission reads 'slope of the graph' as the ordinary derivative with respect to p and uses the definitional nonnegativity of a C^{1,α} Hölder exponent.

**Decisive results.** Lean proves the general calculus fact: if f is bounded below on a tail, then deriv f cannot tend to -∞ at +∞. The proof notes that eventual deriv f≤-1 forces differentiability at every point of the tail (since deriv is 0 at non-differentiable points), then applies the real mean value theorem on an explicit interval [a,b] to contradict the lower bound. Applying this to a Hölder exponent α≥0 on p>2 gives `conjecture_cusp_impossible`: no such α can have deriv α→-∞. Hence the filed infinity-endpoint cusp claim is impossible. The optional fixed-parameter formula is also shown to equal 1/(p-1) on a tail and have derivative→0.

**Report correspondence.** The report and Lean agree: the same mean-value-theorem obstruction, the same nonnegativity application and the same direct negation `conjecture_cusp_impossible`. The report explicitly states the ordinary-derivative convention and that no differentiability hypothesis is silently added; the Lean proof derives differentiability from the eventual slope bound.

## Disposition

APPROVED — merged as PR 1074. The submission gives a complete, formalised disproof of conjecture 00000007991.
