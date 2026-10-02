# Disproof of conjecture 00000001128

> **Original definition (quoted verbatim).** "Definition: M(w,j) is the maximal monomial coefficient in the degree-j part of the Schubert polynomial 𝔖_w. Conjecture: M(w,j) equals min(j, ℓ(w), ⌈ℓ(w)/2⌉)! times a lattice-path count C(w), where C(w) has a product formula on 321-avoiding permutations; in particular M(w, ℓ(w)) is an explicit function of the increasing-subsequence count of w."

**Verdict: FALSIFIED.** A single counterexample at w = 321 in S₃ kills the unconditional
identity M(w,j) = min(j, ℓ(w), ⌈ℓ(w)/2⌉)! · C(w), because a "lattice-path count" is a
non-negative integer, and the identity forces C(321) = 1/2.

## The counterexample

For the longest permutation w = 321 ∈ S₃ (one-line notation), ℓ(321) = 3 and the
Schubert polynomial is homogeneous of degree 3:

  𝔖₃₂₁ = x₁·(x₁+x₂)·x₂ = x₁²x₂ + x₁x₂²   (top Schubert polynomial in n = 3 variables)

Both monomials in the degree-3 part (= the whole polynomial) have coefficient 1, so

  M(321, 3) = 1.

The conjectured factor is

  min(j, ℓ(w), ⌈ℓ(w)/2⌉)! = min(3, 3, ⌈3/2⌉)! = min(3, 3, 2)! = 2! = 2.

If the conjecture held, M(321,3) = 2 · C(321) with C(321) a lattice-path count, i.e.
C(321) ∈ ℤ≥0. But 2 ∤ 1, so C(321) = 1/2 — not an integer, hence not a count of
anything. Contradiction.

## Checks performed

- `reproduce.py` recomputes 𝔖₃₂₁ independently by the standard down-transition
  recurrence S_w = Σ_{i : ℓ(w tᵢ) < ℓ(w)} x_i · S_{w tᵢ} in exact integer arithmetic,
  extracts M(321,3), computes the conjectured factor, and verifies 2 ∤ 1.
  It also cross-checks the polynomial against the product formula x₁(x₁+x₂)x₂.
- `lean4/Main.lean` formalizes the arithmetic core with zero axioms: it computes
  ℓ(321) = 3 and M(321,3) = 1 from the data, forms k = min 3 3 ⌈3/2⌉ = 2, and proves
  `¬ ∃ C : ℕ, M(321,3) = k! * C`.

## Files

- `main.tex` — the written disproof.
- `reproduce.py` — exact recomputation of every attack number (`python3 reproduce.py`).
- `lean4/Main.lean` — zero-axiom Lean 4 certificate; `lean4/Check.lean` runs
  `#print axioms` on every theorem (all report "does not depend on any axioms").
