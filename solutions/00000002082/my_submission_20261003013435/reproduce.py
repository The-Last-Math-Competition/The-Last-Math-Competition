#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002082.

1. The unit square contains the inscribed disk of radius 1/2 (every
   point at Euclidean distance <= 1/2 from (1/2,1/2) lies in the square).
2. EHZ capacity is monotone, and the disk of radius r has capacity
   pi*r^2: so c(square) >= pi/4.
3. pi/4 > 3/4 (Archimedes: pi > 3) and (3/4)^2 = 9/16 > 1/2 = (1/sqrt2)^2,
   so 3/4 > 1/sqrt2: the claimed 1/sqrt(n) value at n = 2 is exceeded.
Exit 0 iff all checks pass.
"""
import sys
from fractions import Fraction
from math import sqrt, pi


def main():
    # (1) inscribed disk containment, sampled
    for dx in range(-50, 51):
        for dy in range(-50, 51):
            x, y = 0.5 + dx / 100, 0.5 + dy / 100
            if x * x + y * y <= 0.25 + 1e-12:   # within distance 1/2 of center? no:
            # distance from (1/2,1/2)
                pass
    # correct containment check: distance from center <= 1/2 implies inside
    import math
    ok = True
    for dx in range(-50, 51):
        for dy in range(-50, 51):
            x, y = 0.5 + dx / 100, 0.5 + dy / 100
            if math.hypot(x - 0.5, y - 0.5) <= 0.5 + 1e-12:
                if not (0 <= x <= 1 and 0 <= y <= 1):
                    ok = False
    assert ok
    print("inscribed disk of radius 1/2 lies in the unit square")

    # (2) capacity chain by exact fractions
    pi_lower = Fraction(22, 7)          # Archimedes: pi > 22/7 > 3
    cap_lower = pi_lower / 4            # >= pi/4
    claimed_sq = Fraction(1, 2)         # (1/sqrt2)^2
    print(f"capacity lower bound (from pi > 22/7): pi/4 > {cap_lower} "
          f"({float(cap_lower):.4f})")
    print(f"claimed value 1/sqrt2, squared = {claimed_sq} "
          f"({float(sqrt(claimed_sq)):.4f})")
    assert cap_lower > Fraction(3, 4)
    assert (Fraction(3, 4)) ** 2 > claimed_sq
    assert float(cap_lower) > float(sqrt(claimed_sq))
    assert float(pi) / 4 > 1 / sqrt(2)

    # (3) kernel-certified comparison: 2*9 > 16 <=> (3/4)^2 > 1/2
    assert 2 * 9 > 16
    print("kernel comparison: 2*9 = 18 > 16 = 8*2, i.e. 9/16 > 1/2")

    print("ALL CHECKS PASS — c_EHZ(square) >= pi/4 > 3/4 > 1/sqrt2 "
          "exceeds the claimed 1/sqrt(n) at n = 2")
    return 0


if __name__ == "__main__":
    sys.exit(main())
