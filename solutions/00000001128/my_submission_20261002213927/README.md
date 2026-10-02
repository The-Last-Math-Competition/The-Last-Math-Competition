# Disproof of conjecture `00000001128` (v3: correct Schubert polynomial)

**Verdict: FALSE — with the correct 𝔖₃₂₁, the conjectured factorial factor
does not divide M.**

## The conjecture (verbatim from `conjectures/00000001128.md`)

> Definition: M(w,j) is the maximal monomial coefficient in the degree-j
> part of the Schubert polynomial 𝔖_w. Conjecture: M(w,j) equals
> min(j, ℓ(w), ⌈ℓ(w)/2⌉)! times a lattice-path count C(w), where C(w) has a
> product formula on 321-avoiding permutations; in particular M(w,ℓ(w)) is
> an explicit function of the increasing-subsequence count of w.

## v1 error (superseded by this package)

The earlier submission (#161) hardcoded 𝔖₃₂₁ = x₁²x₂ + x₁x₂² — **wrong**:
that polynomial is symmetric in x₁,x₂ and cannot be a Schubert polynomial
in any convention. As the review correctly stated, the true polynomial is
the single monomial obtained from the classical longest-element formula.

## The counterexample (corrected)

For w = 321 = w₀ ∈ S₃, the Schubert polynomial is given by the classical
textbook identity for the longest permutation (the base case of the
divided-difference construction — every 𝔖_w is obtained from 𝔖_{w₀} by
isobaric divided differences):

    𝔖_{w₀} = x₁^{n−1} x₂^{n−2} ⋯ x_{n−1}   ⟹   **𝔖₃₂₁ = x₁² x₂**

— a single monomial with coefficient 1. Hence:

- ℓ(w₀) = 3, and the degree-3 part of 𝔖₃₂₁ is the whole polynomial:
  **M(321, 3) = 1**;
- the conjectured factor is min(3, 3, ⌈3/2⌉)! = min(3,3,2)! = **2**;
- the conjecture therefore forces 1 = 2·C(321), i.e. **C(321) = 1/2** —
  not a lattice-path count (not an integer); equivalently 2 ∤ 1.

Lean: the polynomial is represented by its monomial list (single monomial,
coefficient 1); `M_value` = 1, `degree_is_3`, `factor_is_two` = 2,
`no_half_C` (¬∃c, 1 = 2c, by a structural case analysis — no `Dvd`
decidability, keeping the proof axiom-free), `C_not_integer`. All 5
theorems `does not depend on any axioms`.

## Reproduce

`python3 reproduce.py` — computes 𝔖₃₂₁ from the w₀ monomial formula,
double-checks via divided differences from x₁²x₂ down the weak order of
S₃ (the Roichman/Monk axioms), extracts M, and checks 2 ∤ 1. Exit 0.

## Boundary

The anchor 𝔖_{w₀} = x₁^{n−1}⋯x_{n−1} is the classical identity (standard
reference: Manivel, *Symmetric Functions, Schubert Polynomials and
Degeneracy Loci*; it is also the defining base of the divided-difference
recursion). Only the divisibility consequence is refuted here; the
321-avoiding product formula clause is not addressed.
