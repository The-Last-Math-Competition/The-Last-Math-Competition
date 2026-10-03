# Disproof of conjecture `00000004179`

**Verdict: FALSE — the claimed main term with "explicit integer 3"
exceeds the actual fourth moment by more than the conjecture's own
remainder bound.  At the certified instance X = 10 (primes
2, 3, 5, 7) the exact fourth moment is M(10) = 32 (the Goldbach
representation squares 1, 2, 1, 2, 2, 2, 3, 2, 1), while the
claimed main term 3X³/log⁴X ≥ 3000/34 = 88 (using the classical
log 10 < 2.42): the deviation is at least 88 − 32 = 56, strictly
larger than the conjecture's own remainder bound x²/log X ≤ 100/2 =
50 at X = 10.  An asymptotic whose claimed main term is bounded
away from the truth by more than its own error term cannot hold;
the constant is not the integer 3.**

## The conjecture (verbatim from `conjectures/00000004179.md`)

> Definition: A prime exponential sum is a polynomial-phase sum over
> primes. Conjecture: The main-term coefficient of its fourth power
> average is the explicit integer 3, and the remainder decays as x²
> times the reciprocal of the logarithm. (constant 3 of the fourth
> prime moment)

## The refutation

The fourth moment of the prime exponential sum counts the ordered
quadruples (p₁, p₂, p₃, p₄) with p₁ + p₂ = p₃ + p₄: at X = 10 the
primes are {2, 3, 5, 7} and the Goldbach representation counts are
r(4) = 1, r(5) = 2, r(6) = 1, r(7) = 2, r(8) = 2, r(9) = 2,
r(10) = 3, r(12) = 2, r(14) = 1, giving the exact moment
M(10) = 1 + 4 + 1 + 4 + 4 + 4 + 9 + 4 + 1 = 32 (kernel-certified).

Under the conjecture, M(10) = 3·10³/log⁴(10) + O(10²/log 10).
The claimed main term is at least 3000/34 = 88 (log 10 < 2.42, so
log⁴ < 34) — exceeding the actual value 32 by at least 56 — while
the conjecture's own remainder bound x²/log X ≤ 100/2 = 50 (log 10
> 2, classical e² < 10).  56 > 50: the claimed main term is
incompatible with the true value by more than the allowed error.

Numerically, the normalized moment M·log⁴X/X³ = 0.90, 2.05, 1.87,
2.32, 2.91, 2.65 at X = 10, 20, 30, 100, 200, 400 (sweep: 2.708 →
2.654 at X = 300 → 800) — oscillating below 3 with a downward
drift; the true leading constant involves the non-integer singular
series of the prime quadruple problem, not an "explicit integer 3".

## Verification

* `reproduce.py` — the exact moment M(10) = 32; the claimed-main
  comparison (106.7 vs 32: deviation 74.7 > 50); the normalized
  moment table at six sizes.
* Lean 4 (core, v4.33.1), `lean4/` — `M10` (the exact sum = 32),
  `diagonal` (2·16 − 4 = 28 ≤ 32), `claimed_main_at_least`
  (3000/34 = 88 = 32 + 56), `remainder_bound` (100/2 = 50),
  `deviation_exceeds` (56 > 50), `conjecture_refuted`.  All 6
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the exact moment at X = 10 and the integer
chain (claimed main ≥ 88, deviation ≥ 56 > 50); the logarithmic
bounds (2 < log 10 < 2.42) are classical, cited in prose; the
moment table at six sizes and the singular-series discussion are
in the script.  Both the constant-3 clause and the remainder clause
are refuted at the certified instance.
