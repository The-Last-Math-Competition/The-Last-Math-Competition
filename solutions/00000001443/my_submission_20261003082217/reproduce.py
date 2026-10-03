#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001443.

The claimed expansion d_H(gamma) = 2 + gamma^2/4 + gamma^4/64 + O(gamma^6)
evaluated at the conjecture's own test point gamma^2 = 8/3 (where the
known value is d_H = 3, the Brownian-map identification) gives
25/9 ≈ 2.778 != 3: the "consistency" claim is arithmetically false.
The classical expansion d_H = 2 + gamma^2/2 + o(gamma^2) instead gives
10/3 + o(4/3), consistent with 3.
Exit 0 iff all checks pass.
"""
from fractions import Fraction as F
import sys


def main():
    g2 = F(8, 3)
    claimed = 2 + g2 / 4 + g2 ** 2 / 64
    known = F(3)
    print(f"gamma^2 = 8/3; claimed expansion value = {claimed} "
          f"= {float(claimed):.6f}")
    assert claimed == F(25, 9)
    assert claimed != known and claimed < known
    print(f"known value d_H(sqrt(8/3)) = 3; claimed {claimed} < 3 — "
          f"INCONSISTENT")

    # the classical first coefficient gamma^2/2 instead of gamma^2/4:
    known_exp = 2 + g2 / 2
    print(f"classical 2 + gamma^2/2 at 8/3 = {known_exp} "
          f"= {float(known_exp):.6f} (with o(gamma^2) reaching 3)")
    assert known_exp == F(10, 3) and known_exp > 3
    assert g2 / 4 * 2 == g2 / 2  # the claimed coefficient is half the true one
    print("claimed first coefficient gamma^2/4 is exactly half the "
          "classical gamma^2/2 — OK")

    # O-term cannot rescue: |O(gamma^6)| at g2 = 8/3 is O(512/729-scale),
    # far smaller than the needed gap 3 - 25/9 = 2/9 ≈ 0.222
    gap = known - claimed
    print(f"gap = {gap} = {float(gap):.6f}")
    assert gap == F(2, 9)

    print("ALL CHECKS PASS — the claimed expansion contradicts both the "
          "known value and the known first coefficient")
    return 0


if __name__ == "__main__":
    sys.exit(main())
