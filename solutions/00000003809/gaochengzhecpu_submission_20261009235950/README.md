# Conjecture 00000003809: Gap convexity is not equivalent to operator monotonicity

On C=[0,1], the smooth monotone operator F(x)=2x-x^2 has primal gap 2x^2-x^3, which violates the midpoint convexity inequality at 2/3 and 1. For the dual convention, K(x)=-x is nonmonotone but its dual gap is the affine function 1-x. Both formulas are proved for the actual defining suprema.

## Scope and formal correspondence

The source specifies no gap convention. The standard primal gap already refutes the claimed implication from monotonicity to convexity on a compact convex domain. The standard dual (Minty) gap independently refutes the reverse implication. No equivalence of primal and dual solution sets is assumed for the nonmonotone second operator; the source's separate gap-minimization clause need not be denied.

The operators act on the actual real interval [0,1]. OperatorMonotone is the usual one-dimensional inner-product inequality. primalGap and dualGap are real sSup values of their true images over the interval. IsGreatest proofs establish attainment and the upper bound at every feasible point. The nonconvex midpoint inequality and the convex affine dual gap are expressed with Mathlib ConvexOn; the final theorem negates each universal equivalence.

## Files and reproduction

- `main.tex` and `main.pdf`: full argument and formal correspondence.
- `SOURCE.md`: exact bilingual source; its commit and SHA-256 are recorded in `verification/SOURCE_PROVENANCE.json`.
- `lean/`: portable Lean 4.19.0 project with Mathlib pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `verification/`: actual clean-build logs, theorem dependencies, PDF compilation and rendering records, and reviews.

Inside `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. On a new machine, `lake exe cache get` retrieves the pinned official dependency artifacts. From the submission directory, `tectonic main.tex` reproduces the PDF. No auxiliary numerical script is needed for this exact proof.

Only the official commit-pinned dependency cache is reused; the submission itself is compiled in a fresh directory without its prior build artifacts. The audit excludes proof gaps, added axioms, and native computation shortcuts. Author self-review and parent review are distinct; no external independent review is claimed.
