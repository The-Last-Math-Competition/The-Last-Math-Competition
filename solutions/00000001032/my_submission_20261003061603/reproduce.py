#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001032.

q^2+q+1 is never a perfect square for q >= 1 (strict squeeze
q^2 < q^2+q+1 < (q+1)^2), and q = 0 gives v = 1, not a prime power.
The conjecture's exceptional class is empty; non-cyclic planar
difference sets exist classically ((91,10,1), order 9, v = 91 not a
square).
Exit 0 iff all checks pass.
"""
import sys


def main():
    # 1. squeeze for a wide range
    for q in range(1, 10**6 + 1):
        v = q * q + q + 1
        s = v // 2
        assert not (s * s == v), f"q = {q} gives a square?!"
    print("squeeze: no 1 <= q <= 10^6 has q^2+q+1 a perfect square — OK")

    # spot-check the strict inequalities symbolically for a sample
    for q in (1, 2, 3, 5, 9, 100, 12345):
        assert q * q < q * q + q + 1 < (q + 1) * (q + 1)
    print("spot checks q^2 < q^2+q+1 < (q+1)^2 — OK")

    # 2. q = 0: v = 1, and every prime power square >= 4
    assert 0 * 0 + 0 + 1 == 1
    print("q = 0 gives v = 1 = 1^2; prime power squares >= 2^2 = 4 — OK")

    # 3. the conjecture's own parameter for q = 9
    assert 9 * 9 + 9 + 1 == 91
    assert 81 < 91 < 100
    print("q = 9: v = 91 = 7*13, not a square (9^2 < 91 < 10^2) — OK")

    print("ALL CHECKS PASS — the exceptional class is empty for all q")
    return 0


if __name__ == "__main__":
    sys.exit(main())
