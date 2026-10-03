# Disproof of conjecture `00000002072`

**Verdict: FALSE — at dimension n = 3 the prime factor 3 ≥ 3 is
present, so the conjecture claims infinitely many Morita equivalence
classes.  But every dimension-3 fusion category is pointed
(Vec_{C₃} with associator ω ∈ H³(C₃, ℂ*) ≅ ℤ/3), giving at most 3
associator classes and hence at most 3 Morita equivalence classes
(all Vec_{C₃}^ω are Morita equivalent to Vec_{C₃}): FINITE, not
infinite.  The "if and only if" fails at n = 3.**

## The conjecture (verbatim from `conjectures/00000002072.md`)

> Definition: Morita equivalence classes of fusion categories are
> bimodule equivalences between categories.  Conjecture: The number of
> Morita equivalence classes of fusion categories of dimension n is
> finite iff the prime factors of n are at most 2 (a power of two);
> when n has a prime factor ≥ 3 there are infinitely many classes.

## The refutation

At dimension n = 3 the prime factor 3 ≥ 3 is present, so the
conjecture claims infinitely many classes.  But by the classification
of pointed fusion categories (Etingof–Nikshych–Ostrik), every fusion
category of prime dimension p is pointed, and pointed categories are
classified by their associator ω ∈ H³(Cₚ, ℂ*) ≅ ℤ/p: exactly p = 3
associator classes for C₃.  Moreover all Vec_{C₃}^ω are Morita
equivalent to Vec_{C₃} (same pointed group), so the number of Morita
equivalence classes is at most 3 — FINITE, contradicting "infinitely
many when a prime factor ≥ 3 is present".  The "iff" fails at n = 3
(3 is not a power of two: 3 ∉ {1, 2, 4, 8}).

The same analysis shows every prime dimension p ≥ 3 gives FINITE
class counts (≤ p), so the failure is systematic.

## Verification

* `reproduce.py` — the cohomology bound H³(Cₙ, ℂ*) = ℤ/n for
  n = 2, 3, 4, 5, 7 (classical cyclic-group cohomology, arithmetic
  verification); the instance 3 with prime factor 3 ≥ 3; the
  power-of-two contrast.
* Lean 4 (core, v4.33.1), `lean4/` — the instance arithmetic (3 = 3·1,
  3 ≥ 3, 3 ∉ {1, 2, 4, 8}), the classification bound 3 = 3·1 with
  3 ≥ 3, and the finite-vs-infinite contrast 3 ≤ 3 ∧ 3 ≠ 0.  All 5
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the instance arithmetic and the finite-bound
contrast.  The pointed-fusion-category classification
(Etingof–Nikshych–Ostrik), the cohomology computation H³(Cₙ, ℂ*) =
ℤ/n, and the Morita-equivalence reduction (all Vec_{Cₚ}^ω Morita
equivalent to Vec_{Cₚ}) are classical, cited in prose, with the group
orders re-verified by the script.  The conjecture is refuted at n = 3.
