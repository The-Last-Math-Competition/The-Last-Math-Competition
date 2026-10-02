# Disproof of conjecture `00000001951`

**Verdict: FALSE — at n = 3 the claimed smallest index 2³·C(3,2) = 24 is
contradicted by the classical determinant construction: the map
Out(F₃) → GL₃(Z) → {±1} is surjective, giving a proper subgroup of
index 2 < 24.**

## The conjecture (verbatim from `conjectures/00000001951.md`)

> Definition: The congruence subgroup property (CSP) of Out(F_n) is the
> coincidence of its congruence subgroups with all finite-index
> subgroups. Conjecture: Out(F_n) (n ≥ 3) fails CSP (its
> smallest-index proper subgroup is an automorphism kernel); the
> smallest index of a proper subgroup is 2^n·C(n,2).

## The refutation (n = 3)

The classical map Aut(F₃) → GL₃(Z) (the action on
H₁(F₃, Z) = Z³ ≅ F₃^{ab}) kills the inner automorphisms (each inner
acts trivially on homology; classical), hence descends to
Out(F₃) → GL₃(Z). Composing with det: GL₃(Z) → {±1} — surjective
(diag(−1,1,1) has determinant −1) — yields a surjective homomorphism
Out(F₃) → {±1}. Its kernel is a proper subgroup of index 2 (classical:
a surjection onto a group of order 2 has kernel of index 2).

The smallest index of a proper subgroup is therefore ≤ 2 < 24 = 2³·C(3,2):
the claimed formula fails at its first case. (The same construction
works for every n ≥ 2, so the "smallest index = 2ⁿ·C(n,2)" clause fails
throughout the claimed range.)

## Verification

* `reproduce.py` — exact arithmetic: 2³·C(3,2) = 24 vs the index-2
  kernel of det ∘ (the action on homology); illustrates diag(−1,1,1)
  with determinant −1.
* Lean 4 (core, v4.33.1) — `lean4/`: the claimed value 24, the
  refutation 2 < 24 ∧ 2 ≠ 24. All 2 audited theorems report `does not
  depend on any axioms`. The determinant construction, its descent to
  Out, and the surjectivity are classical and cited (Nielsen; the
  standard Aut(Fₙ) → GLₙ(Z) map).

## Boundary

Only the claimed smallest-index formula is refuted (at n = 3); the CSP
clause and larger n are not addressed.
