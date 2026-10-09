# Author self-review: conjecture 00000003454

Main.lean SHA-256: `fe1a02c83169e72354ee1541a35367f3bad70c6ce4f7dd454eb49faf10dff2d4`

SOURCE.md SHA-256: `c21e1c9ffa2f0c80058a12549ee78a487a94a67d12c25ce606a55658e469194f`

1. The exact function and midpoint are admissible: the midpoint lies in the unit interval, and Lean proves the polynomial is infinitely differentiable.
2. The proof uses the actual Mathlib Bernstein operator; the variance identity is explicitly converted to its defining finite sum.
3. The n+1 indexing excludes order zero without changing the positive-order asymptotic claim.
4. Both standard n-scaled and literal unscaled deviation limits are handled. Their values are respectively 1/4 and zero, while Lean computes the actual second derivative as two.
5. The submission distinguishes the false coefficient claim from the correct classical expression with x(1-x)/2; it does not assert that the O(1/n) error bound is false.

Numerical support is not needed: all arithmetic and finite cases are checked in Lean. See verification/BUILD.json and its logs for the independently recorded actual commands. This document is an author scope review, not an external review certificate.

Verdict: PASS (author self-review).

Fresh-directory lake build and direct Lean execution passed with warnings as errors. All reported axioms are standard. Native LaTeX compilation succeeded; Tectonic export and Poppler render passed. Both final PDF pages were visually inspected. Parent-agent adversarial review is still a separate required step.
