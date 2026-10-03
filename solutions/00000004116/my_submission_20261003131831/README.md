# Disproof of conjecture `00000004116`

**Verdict: FALSE — the formula is off by one at every instance.
Conf₁(R^d) = R^d has asymptotic dimension d (asdim of a
d-dimensional normed vector space equals its topological
dimension), not the claimed dn − 1 = d − 1; at (d, n) = (1, 1):
asdim Conf₁(R) = asdim R = 1 ≠ 0; at (d, n) = (2, 1): Conf₂(R) =
{(x, y) : x ≠ y} is the union of two open half-planes, each
homeomorphic to R² via the linear map (x, y) ↦ (x, y − x), so
asdim = 2 ≠ 1.  Conf_n(R^d) is a dn-dimensional open manifold
(free Sₙ-action on an open subset of R^{dn}), so the correct value
is dn — and since the conjecture asserts the fractal correction
term is always ZERO, the base-case failure cannot be repaired by
adding 1.**

## The conjecture (verbatim from `conjectures/00000004116.md`)

> Definition: The asymptotic dimension is the large-scale geometric
> dimension invariant. Conjecture: The asymptotic dimension of
> Conf_n(R^d) is exactly dn − 1, coinciding with the coarse
> dimension, and the fractal correction term is always zero.
> (Euclidean configuration asymptotic dimension formula)

## The refutation

Configuration spaces of Euclidean space are open manifolds of
dimension dn: the ordered configuration is the open set
{(x₁, …, xₙ) : xᵢ ≠ xⱼ} ⊂ R^{dn}, and the unordered quotient is a
dn-manifold since the free Sₙ-action is by diffeomorphisms.  The
asymptotic dimension of R^k is k, and asdim is invariant under
homotopy equivalence for these spaces:

* **(d, n) = (1, 1)**: Conf₁(R) = R, asdim = **1**; claimed
  dn − 1 = 0.  1 ≠ 0 (kernel-certified).
* **(d, n) = (2, 1)**: Conf₂(R) = {x ≠ y} = {x < y} ∪ {x > y},
  each component mapped by the invertible linear map
  (x, y) ↦ (x, y − x) onto (0, ∞) × R ≅ R²: asdim = **2**;
  claimed dn − 1 = 1.  2 ≠ 1 (kernel-certified).

The pattern is structural: asdim Conf_n(R^d) = dn for all d, n
(e.g. Conf₂(R) ≃ S⁰ × R²), while dn − 1 < dn always (`off_by_one`).
Since the conjecture explicitly fixes the fractal correction term
to zero, the off-by-one failure at the base case is unrepairable
within the conjecture's own terms.

## Verification

* `reproduce.py` — the linear homeomorphism (det ±1, invertibility)
  for the Conf₂(R) component; the dimension comparisons; the
  manifold-structure statement.
* Lean 4 (core, v4.33.1), `lean4/` — `instance_11` (1·1−1 = 0,
  1 ≠ 0), `instance_21` (1·2−1 = 1, 2 ≠ 1), `off_by_one`
  (0 < 1 ∧ 1 < 2), `conjecture_refuted`.  All 4 audited theorems
  report `does not depend on any axioms`.

## Boundary

The kernel certifies the dimension comparisons at the two smallest
instances; that asdim R^k = k, that Conf_n(R^d) is a dn-manifold,
and the asdim-homotopy invariance are classical, cited in prose and
illustrated by the script's explicit homeomorphism.  The formula
dn − 1 (with its zero-correction assertion) is refuted at the base
cases and structurally for all (d, n).
