#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001670."""
import sys, math
from fractions import Fraction

def main():
    val = (2 / math.pi) * math.atan(math.sqrt(2))
    print(f"(2/pi)*arctan(sqrt 2) = {val:.6f}  (conjecture also asserts P_3 = 0.918)")
    assert val < 2/3
    assert Fraction(2, 3) < Fraction(459, 500)
    assert 2 * 500 < 3 * 459  # 1000 < 1377
    print(f"chain: {val:.4f} < 2/3 = {2/3:.4f} < 0.918  (1000 < 1377)")
    print("the conjecture's two descriptions of P_3 contradict each other")
    print("ALL CHECKS PASS — conjecture refuted")
    return 0

if __name__ == "__main__":
    sys.exit(main())
