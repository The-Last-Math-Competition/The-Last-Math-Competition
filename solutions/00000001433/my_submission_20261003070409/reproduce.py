#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001433.

The conjecture's own explicit rate c(lambda) = lambda - 1 is negative
on (lambda_c, 1) for any threshold lambda_c < 1 (the known ARW regime):
the claimed "exponential decay" bound exp(-c t) = exp((1-lambda) t)
there GROWS, and c(lambda_c) = lambda_c - 1 < 0 != 0 contradicts the
stated limit "c -> 0 as lambda -> lambda_c".
Exit 0 iff all checks pass.
"""
import math
import sys
from fractions import Fraction


def main():
    # 1. the rate is negative at lambda = 0.9 (exact fractions)
    lam = Fraction(9, 10)
    c = lam - 1
    assert c == Fraction(-1, 10) < 0
    print(f"c(9/10) = {c} < 0 — OK")

    # 2. the claimed bound exp(-c t) then GROWS: it exceeds 1 for t > 0
    #    and diverges, so it is not a decay bound
    for t in (1, 10, 100):
        b = math.exp(-c * t)
        assert b > 1, t
        print(f"  exp(-c * {t}) = {b:.3e} > 1 — growing, not decaying")
    assert math.exp(-c * 100) > 1e4

    # 3. the limit contradiction: c(lambda_c) = lambda_c - 1 < 0 for any
    #    lambda_c < 1, while the conjecture states c -> 0 as
    #    lambda -> lambda_c
    for lam_c in (Fraction(1, 2), Fraction(7, 10), Fraction(9, 10)):
        c_at = lam_c - 1
        assert c_at < 0 and c_at != 0
        print(f"  lambda_c = {lam_c}: c(lambda_c) = {c_at} < 0, not 0")

    # 4. instance scaling: 9 < 10 certifies lambda = 9/10 < 1
    assert 9 < 10 and 10 - 9 == 1
    print("instance lambda = 9/10: 9 < 10 — OK")

    print("ALL CHECKS PASS — the rate formula is negative inside the "
          "claimed parameter region and contradicts the stated limit")
    return 0


if __name__ == "__main__":
    sys.exit(main())
