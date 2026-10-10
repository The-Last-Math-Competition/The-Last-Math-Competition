# 00000008963: identity-jump Riemann–Hilbert counterexample

The actual normalized identity-jump problem on the unit circle is solved by the entire constant function 1. Its actual Cauchy correction operator vanishes because J-I=0. The standard rank-zero Fredholm determinant det(I-C) is therefore 1, contradicting the source's assertion of a vanishing solvability criterion.

Includes proof.tex, compiled proof.pdf, and the full pinned Lean project in lean/. Run lake build with Lean 4.19.0. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The formalization verifies complex differentiability, boundary matching and normalization at infinity, computes the parametrized Cauchy integral and actual zero linear operator, and proves determinant 1 in every finite-rank reduction dimension. Printed axiom audits use standard permitted axioms only.
