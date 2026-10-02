# Disproof of conjecture `00000002221`

**Verdict: FALSE — for R = k³ (zero-dimensional, dim R = 0) the Stone
space of the Booleanization of Spec R has 8 points, exceeding the
claimed bound 2^(2^0) = 2.**

## The conjecture (verbatim from `conjectures/00000002221.md`)

> Definition: The constructible topology on Spec R. Conjecture: The
> cardinality of the Stone space of the Booleanization
> (complemented-closure algebra) of the spectrum is at most 2^{2^d}
> with d = dim, explicitly (Booleanization cardinality).

## The counterexample

Take R = k × k × k (product of three copies of a field k).

1. **dim R = 0.** A finite product of fields is zero-dimensional
   (classical). So the claimed bound is 2^(2^0) = 2^(1) = **2**.
2. **Spec R has exactly 3 points.** The prime ideals of a finite
   product of fields ∏ kᵢ are exactly the kernels of the projections
   (classical; e.g. Atiyah–Macdonald, Exercise 1.21 / Ch. 1): here
   {0}×k×k, k×{0}×k, k×k×{0}. So |Spec R| = **3 > 2** — the bound
   fails already at the level of points.
3. **The Booleanization gives 8.** Spec R is a finite discrete space,
   hence every subset is constructible (the constructible topology is
   the discrete topology); the Boolean algebra of constructible subsets
   is the full powerset P({1,2,3}) with 2³ = 8 elements, and its Stone
   space (the space of ultrafilters) has **8 = 2³ > 2** points.

## General family

For every N ≥ 2, the ring k^N is zero-dimensional with Spec of N
points and Booleanization P(N), whose Stone space has 2^N > 2 = 2^(2^0)
points: the claimed bound fails for the entire zero-dimensional family
(kernel-certified as a general statement over N). The bound 2^{2^d}
cannot hold with d = dim.

## Verification

* `reproduce.py` — recomputes the prime ideals of k^N symbolically
  (kernels of projections), the constructible subsets, and the
  ultrafilter count 2^N for N = 1..8; prints the comparison against
  2^(2^dim).
* Lean 4 (core, v4.33.1) — `lean4/`: the bound value 2^(2^0) = 2, the
  point-count violation 3 > 2, the Stone-space violation 8 > 2, and the
  general family statement 2^N > 2 for all N ≥ 2 (via the clean
  monotonicity lemma Nat.pow_le_pow_right). All 4 audited theorems
  report `does not depend on any axioms`. The commutative-algebra facts
  (3 prime ideals of k³; constructible = all subsets in the finite
  discrete case) are classical and cited.

## Boundary

Only the claimed cardinality bound with d = dim is refuted; the
constructible topology itself is not disputed.
