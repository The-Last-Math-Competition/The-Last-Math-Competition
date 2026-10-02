# Lean 4 formalization — Disproof of TLMC conjecture 00000001168

Pure core Lean 4 (no Mathlib, no dependencies). The conjecture claims a
spectral multiplicity upper bound of two for Zoll metrics on SU(2), citing
"the family of rotated round metrics" as the counterexample to multiplicity
rigidity. The counterexample to the conjecture is the round metric on
SU(2) = S³ itself: it is Zoll (all geodesics are great circles, closed with
common period 2π) and its k-th Laplace eigenvalue k(k+2) has multiplicity
(k+1)² — already 4 > 2 at k = 1.

`Main.lean` formalizes the discrete skeleton:

- `lambda k = k*(k+2)` and `harmDim k = homCount k - homBelow k`, the honest
  dimension count `#monomials(deg k, 4 vars) − #monomials(deg k−2, 4 vars)`
  for the space of degree-k harmonic homogeneous polynomials (the classical
  model of the λ_k eigenspace on the round S³; Δ: Hom_k → Hom_{k−2} is
  surjective, and both the kernel dimensions and the surjectivity are
  independently recomputed by exact rational elimination in
  `../reproduce.py`).
- `lambda_1 = 3`, `harmDim_1 = 4`; `mult_table` checks `harmDim k = (k+1)²`
  for k = 0..12; `nonzero_mult_exceed_two` checks every k ≥ 1 multiplicity
  exceeds 2.
- `coord_functions_independent`: the four coordinate functions lie in the
  λ₁-eigenspace and the evaluation matrix at the four axis points of S³ is
  the identity, so mult(λ₁) ≥ 4 (in fact exactly 4 by the count).
- `Qrot_preserves_sqNorm` and `Qrot_axes`: the cyclic coordinate rotation
  preserves the squared Euclidean norm and permutes the axis points, hence is
  an isometry of the round metric — every "rotated round metric" is the round
  metric with the identical spectrum, so the conjecture's own family violates
  its claimed bound on every member.
- `disproof` packages the counterexample.

All proofs are `rfl`/`decide` on closed computations (the core `Int.add_*`
lemmas carry `propext`, so the norm-preservation argument is written over
`Nat` with axiom-free core lemmas). `ℕ` notation is not used; everything is
bare `Nat`/`Int`.

## Build and verify

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints the axiom profile of every theorem; each line must read
"does not depend on any axioms" (zero axioms, zero `sorry`).
