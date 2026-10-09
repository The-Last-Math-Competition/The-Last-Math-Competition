# Source correspondence — 00000007768

Original exact bytes: `sources/00000007768.md`.
SHA256: `2d82e97886ce44404e1c3204f10740a4d59ad617dbd1296045b5db5bdcb82cfd`.
Both English and Chinese contain the necessary universal assertion that every
polynomial outside the power/Chebyshev exceptional families has Julia fractal
dimension greater than one. The proposed package refutes that conjunct with a
degree-two, algebraic-coefficient, nonempty actual Julia-set witness. Therefore
it need not separately adjudicate the arc equivalence, transcendence and cusp
parameter clauses to refute the original conjunction.

## Declared semantic conventions

- Polynomials are actual `Polynomial ℂ`. Degree is actual polynomial `natDegree`.
  Source degree is not explicitly bounded, but the witness has degree 2 and is
  admissible under the standard degree-at-least-2 polynomial Julia theory.
- `filledJuliaSet p` means a common real upper bound for the norms of every
  forward iterate of `fun z => p.eval z`. `juliaSet p` is its topological
  boundary. This is the standard polynomial Julia object, as Milnor §17,
  Lemma 17.1 identifies; it is a definition, not an assumed escape/dimension
  result. The candidate's closedness and radius description are proved.
- “Fractal dimension” is interpreted as actual Hausdorff dimension `dimH` in the
  complex norm metric. The source does not name a dimension definition, so this
  convention remains a semantic-review item. No freely supplied dimension number
  appears anywhere in the theorem.
- “Conjugate” is interpreted as affine polynomial conjugacy. `AffineConjugate p q`
  is the polynomial identity `p.comp h = h.comp q`, where `h=C a*X+C b` and `a≠0`.
  `affine_conjugate_iff_functional` proves equivalence to the all-complex-point
  functional identity, and `affine_bijective` proves the affine map is invertible.
  Thus neither an assumed functional bridge nor a noninvertible map is admitted.
- `Exceptional` ranges over every `d : ℕ`, using actual `X^d` and actual
  `Polynomial.Chebyshev.T ℂ (d : ℤ)` and its negative. Including degrees 0 and 1
  is harmless: the proof forces every putative exceptional degree to 2. No
  centered-parameter characterization is assumed.

## Object/obligation mapping

| Original role | Actual Lean definitions/theorems |
|---|---|
| Complex polynomial witness | `candidate = X^2-C 6`, `quadratic`, `candidate_eval` |
| Every forward orbit term | `filledJuliaSet`, `filled`, `candidate_filled` |
| No finite-horizon escape surrogate | `orbit_norm_growth`, `filled_iterate`, `norm_le_three_of_bounded`, `filled_eq_radius` |
| Actual closed filled Julia and boundary | `filled_closed`, `juliaSet`, `julia_closed` |
| Real-axis dimension bridge | `orbit_im_growth`, `filled_im_zero`, `filled_real`, `julia_real` |
| Nonempty concrete Julia | `three_mem_filled`, `three_mem_julia` |
| Invertible conjugacy and actual degree | `affine_bijective`, `affine_conjugate_iff_functional`, `conjugate_degree` |
| Every power degree | `not_conjugate_power` |
| Every actual signed Chebyshev degree | `not_conjugate_chebyshev`, `not_conjugate_negative_chebyshev`, `candidate_not_exceptional` |
| Algebraic coefficients, without assuming all ℂ algebraic | `candidate_algebraic_coefficients` for every coefficient over ℚ |
| Actual Hausdorff dimension | `real_axis_dimension`, `candidate_julia_dimension` |
| Complete necessary-clause counterexample | `source_counterexample`, `disproves_dimension_clause` |

`DimensionClause` retains the universal polynomial quantifier, standard degree
domain, actual exceptional predicate and strict >1 conclusion. Algebraic
coefficients are proved for the witness separately rather than added as an
unproved nondegeneracy premise. All iterates range over ℕ without a cutoff.
The actual witness 3 lies on the actual Julia boundary, ruling out an empty-set
or impossible-hypothesis mechanism.

## What is not being claimed

The source does not specify alternative conjugacy or dimension conventions.
The theorem is presented under the explicit standard conventions above; an
independent reviewer must decide fidelity. Author compiler checks and PDF
rendering are preparation. No local priority, confidence, cached dependency
file or author assertion is manager acceptance, a useful-solve count, or an
external submission.

At freeze time, actual successful compile logs and dependency source hashes must
support each table row. Uncompiled rows are remaining obligations and must not
be described as locally verified.
