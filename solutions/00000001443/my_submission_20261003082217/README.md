# Disproof of conjecture `00000001443`

**Verdict: FALSE — at the conjecture's own test point γ² = 8/3 (where
d_H = 3 by the Brownian-map identification of √(8/3)-LQG), the claimed
expansion 2 + γ²/4 + γ⁴/64 + O(γ⁶) evaluates to
2 + 2/3 + 1/9 = 25/9 ≈ 2.778 ≠ 3: the "consistency" claim is
arithmetically false.  Moreover the claimed first coefficient γ²/4 is
exactly half the classical γ²/2 (d_H = 2 + γ²/2 + o(γ²), which gives
10/3 + o(4/3), consistent with 3).**

## The conjecture (verbatim from `conjectures/00000001443.md`)

> Definition: The Hausdorff dimension d_H(γ) of LQG metric spaces is
> given by the metric construction of the exponentialized GFF.
> Conjecture: d_H(γ) = 2 + γ²/4 + γ⁴/64 + O(γ⁶); the known value
> d_H(√(8/3)) = 3 is consistent with this expansion; and each
> coefficient of the expansion is explicitly determined by correlation
> functions of the gravitational collision operators.

## The refutation

At γ² = 8/3 (so γ = √(8/3), the point where the LQG metric is
isometric to the Brownian map sphere and d_H = 3), the claimed
expansion evaluates in ninths:

    2 = 18/9,   γ²/4 = (8/3)/4 = 2/3 = 6/9,
    γ⁴/64 = (64/9)/64 = 1/9,
    claimed value = (18 + 6 + 1)/9 = 25/9 ≈ 2.778 ≠ 27/9 = 3.

The conjecture's claim that "d_H(√(8/3)) = 3 is consistent with this
expansion" is arithmetically false.  Furthermore, the claimed first
coefficient γ²/4 is exactly half the classical γ²/2: the known
expansion d_H(γ) = 2 + γ²/2 + o(γ²) at γ² = 8/3 gives 2 + 4/3 =
10/3 + o(4/3) > 27/9, which is the coefficient consistent with the
known value 3 (up to lower order).  The gap 3 − 25/9 = 2/9 ≈ 0.222
cannot be bridged by the O(γ⁶) term at γ² = 8/3 (which is of scale
(8/3)³ = 512/27 in γ⁶ units, i.e. 512/729 in ninths-scale — orders
below 2/9 = 162/729).

## Verification

* `reproduce.py` — exact-fraction evaluation of the claimed expansion
  (25/9), the mismatch with the known value 3, the classical
  coefficient comparison (γ²/4 = ½ · γ²/2), and the gap analysis.
* Lean 4 (core, v4.33.1), `lean4/` — the claimed expansion in ninths
  (18 + 6 + 1 = 25), the mismatch 25 ≠ 27 = 3·9 with 25 < 27, and the
  known-coefficient comparison 30 > 27.  All 4 audited theorems
  report `does not depend on any axioms`.

## Boundary

The kernel certifies the arithmetic core (the claimed value 25/9 ≠ 27/9
at the test point and the coefficient comparison).  The identifications
d_H(√(8/3)) = 3 (Brownian map) and d_H(γ) = 2 + γ²/2 + o(γ²)
(Gwynne–Miller) are classical results of LQG theory, cited in prose.
The expansion and its "consistency" and coefficient claims are
refuted.
