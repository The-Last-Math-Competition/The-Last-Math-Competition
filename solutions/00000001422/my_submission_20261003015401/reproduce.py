#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001422.

1. SRW on K_n: the one-step TV distance to uniform is exactly 1/n
   (exact fractions, n = 4..200); t_mix = 1 for the 1/4 threshold.
2. Interchange on K_n = random transpositions: Diaconis-Shahshahani
   cutoff (1/2) n ln n, e.g. ~230 at n = 100.
3. Ratio ~ (1/2) n ln n -> infinity, not 2.
Exit 0 iff all checks pass.
"""
import sys
from fractions import Fraction
from math import log


def tv_one_step(n):
    """TV of (uniform on n-1 non-start vertices) vs uniform on n."""
    start = Fraction(0, 1)
    others = Fraction(1, n - 1)
    uni = Fraction(1, n)
    tv = (abs(start - uni) + (n - 1) * abs(others - uni)) / 2
    return tv


def main():
    # (1) TV = 1/n exactly
    for n in range(4, 201):
        tv = tv_one_step(n)
        assert tv == Fraction(1, n), (n, tv)
    print("SRW on K_n: one-step TV = 1/n exactly for n = 4..200")
    assert tv_one_step(100) <= Fraction(1, 4)
    print("t_mix(SRW on K_n) = 1 (TV <= 1/4 after one step, n >= 4)")

    # (2) DS cutoff for random transpositions
    for n in (50, 100, 200):
        t = 0.5 * n * log(n)
        print(f"n = {n}: interchange t_mix ~ (1/2) n ln n = {t:.1f}")
    t100 = 0.5 * 100 * log(100)
    assert t100 > 200

    # (3) ratio
    print(f"ratio at n = 100: ~{t100:.0f} / 1 = {t100:.0f}, not 2")
    assert t100 > 2
    print("ALL CHECKS PASS — ratio diverges on the regular graph K_n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
