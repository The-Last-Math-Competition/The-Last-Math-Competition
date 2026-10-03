# Disproof of conjecture `00000002562`

**Verdict: FALSE — "rigidity always superlogarithmic in n" is
impossible for ANY invertible matrix, hence in particular for the
conjecture's own candidates (Vandermonde, Chebyshev-type): by the
matrix determinant lemma, the single entry change
t = −1/(M⁻¹)_{ji} (for any i, j with (M⁻¹)_{ji} ≠ 0) makes M
singular, so R_M(n−1) ≤ 1 — and R_M(n−1) = 1 since zero changes
preserve rank n. A constant 1 is not superlogarithmic. Certified
exactly at the 3×3 Vandermonde instance: det = 250 ≠ 0, one change
(entry (1,2): 5 → 7, i.e. t = 2/5 = −1/(V⁻¹)₂₁ scaled by 5) gives
det = 0; and by exact rational computation for Vandermonde and
Chebyshev-type matrices at n = 3..7.**

## The conjecture (verbatim from `conjectures/00000002562.md`)

> Definition: Matrix rigidity R_M(r) is the minimum number of entries
> to change to lower the rank to r. Conjecture: There exists an
> explicit matrix family whose rigidity is always superlogarithmic in
> n; the candidates for realization are Vandermonde and
> Chebyshev-type matrices.

## The refutation

"Always" quantifies over every rank level r — but at the level
r = n−1 the rigidity of any invertible matrix is exactly 1: the
matrix determinant lemma gives det(M + t·e_i e_j^T) =
det(M)·(1 + t·(M⁻¹)_{ji}), so the single change t = −1/(M⁻¹)_{ji}
annihilates the determinant (and no zero-change does, M being
invertible). Constant 1 < any superlogarithmic function of n.

Certified instance (nodes 1,2,3; scaled by 5 so all entries are
integral): V₅ = [[5,5,5],[5,10,20],[5,15,45]], det(V₅) = 875 − 625 +
125 = 250 = 125·2 ≠ 0. Since (V⁻¹)₂₁ = −5/2, the change t = 2/5 at
entry (1,2) yields [[5,7,5],[5,10,20],[5,15,45]] with det = 750 − 875
+ 125 = 0: R_{V₃}(2) = 1, while any superlogarithmic bound at n = 3
already demands ≥ 2 (e.g. ⌈log₂3·log₂3⌉ = 2). Every Chebyshev-type
instance (distinct nodes → invertible) fails identically — the
script verifies the rank drop with exact rational arithmetic for both
families at n = 3..7.

(Note the distinction: rigidity superlogarithmic at SPECIFIC rank
levels r ≪ n is the famous open territory (Valiant); the conjecture
as stated claims it for ALL r, and the level r = n−1 kills it for
every invertible matrix whatsoever.)

## Verification

* `reproduce.py` — exact rational Gaussian elimination; for n = 3..7:
  Vandermonde (nodes 1..n) and Chebyshev-type (T_{j}(x_i) by the
  integer recurrence): det ≠ 0; a single entry change with
  t = −1/(M⁻¹)_{ji} drops the rank to exactly n−1.
* Lean 4 (core, v4.33.1), `lean4/` — `detV` (det V₅ = 250),
  `detVmod` (modified det = 0), `rigidity_is_one`,
  `superlog_exceeds` (1 < 2), `conjecture_refuted` — all ground
  `decide` cofactor expansions with Nat-safe ordered subtractions.
  All 5 audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the exact instance arithmetic (invertibility,
the single-change singularity, the rigidity value 1, the superlog
violation at n = 3). The matrix determinant lemma is classical,
cited in prose and instantiated by the script for both candidate
families at n = 3..7. The universal ("for all r") superlogarithmic
claim is refuted; no claim is made about rigidity at low rank
levels.
