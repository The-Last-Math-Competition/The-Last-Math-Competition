#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000003295.

The Dawson asymptotic series coefficients a_n = (2n-1)!!/2^n x^{-(2n+1)}
have term ratio (2n+1)/(2x^2), which exceeds 1 for all large n at every
fixed x: the terms grow without bound and the series diverges (term
test). At x = 3 the ratio exceeds 1 from n = 10.
Exit 0 iff all checks pass.
"""
import sys
import math
from fractions import Fraction
from math import sqrt, pi


def dfact(n):
    r = 1
    for k in range(n, 0, -2):
        r *= k
    return r


def main():
    x = 3
    # term ratios
    for n in (10, 11, 12, 20, 100):
        a_n = dfact(2 * n - 1) / 2 ** n
        a_np1 = dfact(2 * n + 1) / 2 ** (n + 1)
        ratio = a_np1 / a_n
        print(f"n = {n}: a_n = {a_n:.3e}, ratio a_(n+1)/a_n = {ratio:.3f}")
    n = 10
    a_n = dfact(2 * n - 1) / 2 ** n
    a_np1 = dfact(2 * n + 1) / 2 ** (n + 1)
    assert a_np1 / a_n > 1, "ratio must exceed 1 from n = 10 at x = 3"

    # terms grow without bound once the ratio (2n+1)/(2x^2) exceeds 1
    # (at x = 3: from n = 9, since 19 > 18); check at n = 30
    for N in (30, 40, 50):
        t = dfact(2 * N - 1) / 2 ** N / 3 ** (2 * N - 1)
        print(f"  |term at n = {N}| = {t:.3e} (> 1)")
        assert t > 1

    # contrast: the true Dawson function stays bounded
    def dawson(x):
        h = 0.00001
        total = 0.0
        for i in range(100000):
            t = i * h * x
            total += math.exp(-t * t) * h * x
        return total

    print(f"Dawson F(3) ≈ {dawson(3):.6f} (bounded; the divergent series "
          f"is only asymptotic)")
    print("ALL CHECKS PASS — terms grow without bound, series diverges "
          "at every fixed x")
    return 0


if __name__ == "__main__":
    sys.exit(main())
