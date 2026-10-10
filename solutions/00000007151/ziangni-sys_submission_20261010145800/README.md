# 00000007151: trace-norm vertex counterexample

In the actual real 1×1 matrix trace-norm unit body, [-1] is the unique maximizer of the nonzero linear functional A ↦ -A₀₀ and hence an exposed vertex. It is not a standard unsigned partial permutation matrix. The source states no positivity or dimension exclusion.

Includes proof.tex, compiled proof.pdf, and a full Lean project in lean/. Run lake build with Lean 4.19.0; mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The formalization proves actual Gram multiplication and the unique eigenvalue, computes the singular-value trace norm, constructs the exposing matrix functional, and proves mathlib extreme-point membership and the full partial-permutation exclusion. Printed audits use standard permitted axioms only.
