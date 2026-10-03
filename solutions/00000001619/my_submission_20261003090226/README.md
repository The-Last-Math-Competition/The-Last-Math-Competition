# Disproof of conjecture `00000001619`

**Verdict: FALSE — the claimed identity det(I−tK) = e^{−t²/4} for the
Fredholm determinant of K(x,y) = e^{−xy} on L²(0,∞) fails at the
t-linear term: the Fredholm side has linear coefficient −tr K with
tr K = ∫₀^∞ e^{−x²} dx = √π/2 ≈ 0.886 > 0, while the claimed
e^{−t²/4} = Σ(−t²/4)ⁿ/n! contains only even powers of t — its linear
coefficient is exactly 0.**

## The conjecture (verbatim from `conjectures/00000001619.md`)

> det(I−tK) = e^{−t²/4} explicitly; precisely, this determinant equals
> e^{−t²/4} (dual to the degenerate Mehler formula for the planar
> Gaussian kernel), it is an entire function of order 2, and its zeros
> form conjugate purely imaginary pairs.

## The refutation

The Fredholm determinant has the series det(I − tK) = 1 − t·tr K +
O(t²) (classical: the linear coefficient is minus the trace), with
tr K = ∫₀^∞ e^{−x²} dx = √π/2 ≈ 0.8862 > 0 (strictly positive: the
integrand is positive, and tr K ≥ ∫₀¹ (1−x²) dx = 2/3 by
e^{−u} ≥ 1−u).  The claimed right-hand side e^{−t²/4} = Σ(−t²/4)ⁿ/n!
contains only even powers of t (2n = 1 is impossible for n : Nat —
kernel-certified), so its linear coefficient is exactly 0.

Equating the two sides at the linear term would force tr K = 0,
contradicting tr K ≥ 2/3.  (Numerically: det(I − 0.1K) ≈ 1 − 0.0886 =
0.9114 from the first-order term, vs the claimed e^{−0.0025} ≈ 0.9975
— a visible mismatch even at t = 0.1.)

## Verification

* `reproduce.py` — Gauss-Hermite quadrature for tr K = √π/2, the
  lower-bound anchor 2/3, and the linear-coefficient comparison at
  t = 0.1.
* Lean 4 (core, v4.33.1), `lean4/` — `even_exponents_only`: the
  structural fact 2·n ≠ 1 for all n : Nat (the claimed series contains
  only even powers of t, so no linear term exists); the negativity
  and size anchors for the Fredholm linear coefficient.  All 3
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the structural even-exponents fact (the claimed
series' zero linear coefficient) and the positivity anchors.  The
Fredholm linear-term theorem (linear coefficient = −tr K) is
classical, cited in prose, with tr K = √π/2 verified by the script's
Gauss-Hermite quadrature.  The identity clause is refuted in full;
the order-2 and zero-location clauses are not needed for the
refutation.
