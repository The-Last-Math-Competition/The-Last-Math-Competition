# Solution Review — Conjecture 00000007367 (PR 1097)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022111507`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007367; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the exact discrete-gradient identity holds, and its realization is the averaging operator in the average-vector-field method. The submission reads the discrete gradient as the Bochner interval average of the actual Fréchet derivative along the segment from x to y, and proves exactness, diagonal consistency and energy conservation for every step y-x=hJ(average) with g(Jg)=0.

**Decisive results.** For any real normed space E and C^1 H with continuous Fréchet derivative, the Lean proves ∫_0^1 DH(x+t(y-x))dt [y-x] = H(y)-H(x) by the chain rule and the fundamental theorem of calculus; the diagonal case gives DH(x). If y-x=hJ(g) with g(Jg)=0, then H(y)-H(x)=g(y-x)=h g(Jg)=0. The hypotheses are satisfiable (e.g. finite-dimensional Hamiltonian systems) and the Claim is the universal statement, not a special case.

**Report correspondence.** The report's Theorems (exact discrete differential, exact AVF energy preservation) and the coordinate-free formulation match the Lean. The report explicitly says the finite-dimensional Riesz identification and the skew-matrix implication are paper-level bridges; the Lean proves the stronger coordinate-free theorem directly.

## Disposition

APPROVED — merged as PR 1097. The submission gives a complete, formalised proof of conjecture 00000007367.
