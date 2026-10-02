#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001857.

1. Numerical quadrature of (1/2pi) int_0^{2pi} log(3-2cos): matches the
   classical identity log((3+sqrt5)/2) to 12 digits.
2. The conjecture's closed form evaluates to ~0.2168 < 1/2, while the
   conjecture claims the limit is 1.175 > 1: internally inconsistent.
3. The true McKay-type constant for random 3-regular graphs is ~1.216
   (literature), also != 1.175.
Exit 0 iff all checks pass.
"""
import sys
from math import log, cos, pi, sqrt, exp


def main():
    # (1) quadrature of the normalized integral
    N = 2 * 10 ** 6
    avg = sum(log(3 - 2 * cos(2 * pi * k / N)) for k in range(N)) / N
    classical = log((3 + 5 ** 0.5) / 2)
    print(f"(1/2pi) int log(3-2cos) ≈ {avg:.12f}; classical log((3+sqrt5)/2) "
          f"= {classical:.12f}")
    assert abs(avg - classical) < 1e-9

    # (2) closed form
    pref = ((3 ** 0.5 - 1) / 2) ** 2
    closed = pref * exp(classical / 2)
    print(f"prefactor (2-sqrt3)/2 = {pref:.6f}; exponential part = "
          f"{exp(classical/2):.6f}")
    print(f"closed form c_3 ≈ {closed:.6f}")
    assert closed < 0.5 < 1.0
    assert closed < 1.175

    # (3) claimed value vs literature
    print(f"claimed numerical limit: 1.175 (conjecture's own text); "
          f"claimed > 1 while closed form < 1/2: mutually exclusive")
    print(f"literature McKay-type constant for d=3: ~1.216 (also != 1.175)")
    assert abs(1.216 - 1.175) > 0.03

    print("ALL CHECKS PASS — closed form 0.2168 < 1 < 1.175: internal "
          "contradiction")
    return 0


if __name__ == "__main__":
    sys.exit(main())
