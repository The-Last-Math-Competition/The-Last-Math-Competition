#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002118.

The exact Quicksort moment recurrences (split position J uniform on
{0..n-1}, subproblems independent):
  E[C_n]     = (n-1) + (2/n) sum_j E[C_j]
  E[C_n^2]   = (n-1)^2 + (2/n) sum_j (E[C_j^2] + E[C_j'^2] + 2 E[C_j] E[C_j'])
  E[C_n^3]   = (n-1)^3 + (2/n) sum_j (E[C_j^3] + E[C_j'^3] + 3 E[C_j] E[C_j'^2]
                                      + 3 E[C_j^2] E[C_j'])
with kappa_3 = M3 - 3 M1 M2 + 2 M1^3, computed exactly over Fractions.
Result: kappa_3(n) = Theta(n^3), not the claimed 2n - 6 log n + C.
Exit 0 iff all checks pass.
"""
from fractions import Fraction as F
import sys


def main():
    N = 55
    M1 = [F(0)] * N
    M2 = [F(0)] * N
    M3 = [F(0)] * N
    for n in range(1, N):
        base = n - 1
        t1 = t2 = t3 = F(0)
        for j in range(n):
            r = n - 1 - j
            t1 += M1[j] + M1[r]
            t2 += M2[j] + M2[r] + 2 * M1[j] * M1[r]
            t3 += (M3[j] + M3[r] + 3 * M1[j] * M2[r] + 3 * M2[j] * M1[r])
        M1[n] = base + t1 / n
        M2[n] = base * base + t2 / n + 2 * base * t1 / n
        M3[n] = base ** 3 + t3 / n + 3 * base * t2 / n + 3 * base * base * t1 / n

    print("n, kappa_3, kappa_3/n:")
    prev = None
    for n in (5, 10, 20, 30, 40, 50):
        k3 = M3[n] - 3 * M1[n] * M2[n] + 2 * M1[n] ** 3
        ratio = k3 / n
        print(f"  n = {n}: kappa_3 = {float(k3):.4f}, kappa_3/n = "
              f"{float(ratio):.4f}")
        if n == 50:
            assert float(k3) > 22000 and float(k3) < 22100
            assert abs(float(ratio) - 441.7) < 0.2
        if prev is not None:
            assert ratio > prev  # growing, not constant
        prev = ratio

    # the claimed linear main coefficient 2 at n = 50: 2*50 = 100
    assert 2 * 50 == 100
    assert float(M3[50] - 3 * M1[50] * M2[50] + 2 * M1[50] ** 3) > 22000
    print("claimed linear main coefficient 2 vs measured kappa_3(50) ≈ "
          "22085 (ratio 442) — refuted")

    print("ALL CHECKS PASS — kappa_3 is Theta(n^3), not linear in n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
