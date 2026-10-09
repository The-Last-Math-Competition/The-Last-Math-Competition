# Formalization contract checkpoints — 00000007768

Source SHA256 independently checked:
`2d82e97886ce44404e1c3204f10740a4d59ad617dbd1296045b5db5bdcb82cfd`.
The exact copy is `sources/00000007768.md`. Work interprets complex-polynomial
conjugacy as affine conjugacy and fractal dimension as Hausdorff dimension;
these standard conventions are declared, not additional mathematical premises.

## 0. Actual pinned Hausdorff/Chebyshev interfaces

Role: ensure the final dimension and all-degree exceptional family use actual
Mathlib objects, not replacements. Exact import targets are
`Mathlib.Topology.MetricSpace.HausdorffDimension` and
`Mathlib.RingTheory.Polynomial.Chebyshev`. Acceptance: compile original pinned
dependency sources only into this worker's `private-lib/lean`, at most two
compiler processes, then successful actual `#check dimH`, `dimH_mono`,
`Real.dimH_univ`, `Isometry.dimH_image`, `Polynomial.Chebyshev.T`, `natDegree_T`.
Source interfaces were read; their actual imports were unavailable during scout.
No shared cache modification, revision change or dependency network install.

## 1. Actual objects and escape-radius equivalence

Original role: the source's polynomial Julia set must be the boundary of actual
bounded forward orbits. Statements:

```lean
def polynomial : Polynomial ℂ := Polynomial.X ^ 2 - Polynomial.C 6
def quadratic (z : ℂ) : ℂ := polynomial.eval z
def filledJulia : Set ℂ := {z | ∃ B : ℝ, ∀ n : ℕ, ‖quadratic^[n] z‖ ≤ B}
def radiusJulia : Set ℂ := {z | ∀ n : ℕ, ‖quadratic^[n] z‖ ≤ 3}
theorem filled_eq_radius : filledJulia = radiusJulia
theorem filled_closed : IsClosed filledJulia
def julia : Set ℂ := frontier filledJulia
```

Checked dependencies: actual norm-sub bound, complex norm powers, iterate-succ,
Archimedean growth and continuous complex maps. Acceptance: all-n proof of
escape, both inclusions, closedness using arbitrary-iterate closed sublevel sets;
no bounded finite truncation, assumed escape bridge or vacuous premise.

## 2. Real-axis inclusion

Original role: prove the actual Julia has dimension at most one. Statements:
`filledJulia ⊆ Set.range Complex.ofReal` and
`julia ⊆ Set.range Complex.ofReal`.
Checked dependencies: complex real/imaginary parts, local image-radius square
bound, imaginary expansion and closed real embedding. Acceptance: infinite
imaginary expansion contradicts actual bounded orbit and uses the proved
escape-radius bridge. The Julia inclusion follows via frontier/closedness.

## 3. Actual Hausdorff dimension

Statement: `dimH julia ≤ 1`. Dependencies to check after private build:
root `dimH_mono`, `Complex.isometry_ofReal.dimH_image`, `Real.dimH_univ`.
Acceptance: actual Hausdorff dimension of an actual subset of ℂ; no finite
covering/sample surrogate or free dimension parameter.

## 4. All-degree affine exceptional exclusion

Original role: the universal >1 claim applies only outside power/±Chebyshev
families. Define affine conjugacy as polynomial identity using `a ≠ 0` and
`h=X*C a+C b`, equivalently `p.comp h=h.comp q`. Define the exceptional family
over all integers/naturals d≥2 using actual `Polynomial.Chebyshev.T` and signs.
Statements: no affine conjugacy of `polynomial` to `X^d` or either sign of
`Polynomial.Chebyshev.T ℂ d` for every d≥2.
Acceptance: actual polynomial degrees force d=2; coefficients/evaluations prove
the d=2 contradiction for both signs. No default Chebyshev parameter −2 premise.

## 5. Original-conjunct counterexample and artifacts

Statement: exists an algebraic-coefficient complex polynomial of degree≥2,
outside the actual all-d exceptional family, whose standard Julia has dimH≤1;
therefore the universal non-exceptional dimension>1 clause is false.
Acceptance: assemble proved obligations with polynomial coefficient algebraicity;
portable Main package, exact source copy, SourceCorrespondence, proof.tex/PDF,
strict schema result and frozen semantic-file hashes. Author self-checks are
preparation; manager/reviewer acceptance remains independent.

## 6. Nonempty actual witness (admissibility audit)

Statements: `(3 : ℂ) ∈ filled` and `(3 : ℂ) ∈ juliaSet candidate`.
Role: explicitly rule out an empty-object/vacuity interpretation of the example.
Checked dependencies: `quadratic 3=3`, all-n iterates, `filled_im_zero` and ordinary
closure/frontier interfaces. Acceptance: prove the fixed bounded orbit and use
arbitrarily close nonreal points outside K to place 3 on the actual boundary.

Also expose `julia_closed (p : ℂ[X]) : IsClosed (juliaSet p)`, the source's explicit
closed-subset admissibility, directly from actual closedness of a frontier.
