#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000003152.

The claimed bound mu(AB) >= exp(mu(A) + mu(B)) exceeds 1 whenever
mu(A) + mu(B) > 0, while mu(AB) <= 1 always (normalized Haar): the
inequality is unsatisfiable. Checked with Taylor-verified exp bounds
and a full sweep of measure pairs.
Exit 0 iff all checks pass.
"""
import sys
from fractions import Fraction


def exp_lower(t):
    """exp(t) >= 1 + t (convexity); returns the exact lower bound 1 + t."""
    return 1 + t


def main():
    # anchor: mu(A) = mu(B) = 1/10
    a = b = Fraction(1, 10)
    claimed_bound = exp_lower(a + b)   # exp(t) >= 1 + t
    print(f"mu(A) = mu(B) = 1/10: claimed bound exp(1/5) >= 1 + 1/5 = {claimed_bound}")
    assert claimed_bound > 1
    print(f"but mu(AB) <= 1 always (normalized Haar): 1 < {claimed_bound} "
          f"makes the inequality unsatisfiable")
    assert claimed_bound > 1

    # sweep: every measure pair with positive sum
    for i in range(0, 101):
        for j in range(0, 101):
            if i + j == 0:
                continue
            claimed = exp_lower(Fraction(i + j, 100))
            if i + j > 0:
                assert claimed > 1
    print("sweep (i/100, j/100), i+j > 0: claimed bound > 1 in every case")

    # Taylor cross-check of exp(1/5) numerically
    approx = sum(Fraction(1, 1) / math_factorial(k) * Fraction(1, 5) ** k
                 for k in range(20))
    print(f"exp(1/5) Taylor (k<=19) = {float(approx):.6f} > 1")
    assert approx > 1

    print("ALL CHECKS PASS — claimed exponential lower bound exceeds the "
          "probability upper bound whenever the measure sum is positive")
    return 0


def math_factorial(k):
    r = 1
    for i in range(2, k + 1):
        r *= i
    return r


if __name__ == "__main__":
    sys.exit(main())
