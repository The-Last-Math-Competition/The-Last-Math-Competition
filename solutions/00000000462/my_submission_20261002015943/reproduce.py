#!/usr/bin/env python3
"""
Independent recomputation for the disproof of TLMC conjecture 00000000462.

Conjecture 00000000462: tau(C_n(1,2)) (number of spanning trees of the circulant
graph on n vertices with jumps 1 and 2) satisfies a linear recurrence whose
largest real characteristic root tends to alpha^2 with alpha = 2 + sqrt(3),
i.e. (2+sqrt(3))^2 = 7 + 4*sqrt(3) ~= 13.9282.

This script recomputes everything from scratch, with no third-party dependencies:

  1. tau(C_n(1,2)) EXACTLY, as an integer Laplacian-minor determinant (Bareiss).
  2. The closed form  tau(C_n(1,2)) = n * (L_{2n} - 2*(-1)^n) / 5  for n >= 5
     (L = Lucas numbers), checked against (1).
  3. Growth rates tau^(1/n), compared with the verifier's 2.81 / 2.76 / 2.71
     (n = 20 / 40 / 80); they converge to phi^2 = (3+sqrt(5))/2 ~= 2.6180.
  4. The Laplacian eigenvalue ceiling max_k lambda_k = 25/4 = 6.25 < 8 < 13.93.

Run:  python3 reproduce.py
"""

from fractions import Fraction
import math


def laplacian_c12(n):
    """Laplacian of the circulant graph C_n(1,2): vertex i adjacent to i+-1, i+-2."""
    L = [[0] * n for _ in range(n)]
    for i in range(n):
        for d in (1, 2):
            j = (i + d) % n
            if j != i:
                L[i][i] += 1
                L[i][j] -= 1
                L[j][j] += 1
                L[j][i] -= 1
    return L


def bareiss_det(M):
    """Exact integer determinant (fraction-free Bareiss algorithm)."""
    M = [row[:] for row in M]
    n = len(M)
    if n == 0:
        return 1
    sign = 1
    prev = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for i in range(k + 1, n):
                if M[i][k] != 0:
                    M[k], M[i] = M[i], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[-1][-1]


def tau_kirchhoff(n):
    """tau(C_n(1,2)) by the matrix-tree theorem: any cofactor of the Laplacian."""
    L = laplacian_c12(n)
    minor = [row[1:] for row in L[1:]]
    return bareiss_det(minor)


def tau_eigen_product(n):
    """tau via eigenvalue products (float): (1/n) * prod_{k=1}^{n-1} lambda_k."""
    p = Fraction(1)
    for k in range(1, n):
        t = 2 * math.pi * k / n
        lam = (2 - 2 * math.cos(t)) + (2 - 2 * math.cos(2 * t))
        p *= Fraction(lam).limit_denominator(10**15)
    return float(p / n)


def lucas(m):
    a, b = 2, 1
    for _ in range(m):
        a, b = b, a + b
    return a


def tau_closed(n):
    """Closed form: tau = n * (L_{2n} - 2*(-1)^n) / 5, valid for n >= 5."""
    return n * (lucas(2 * n) - (2 if n % 2 == 0 else -2)) // 5


def main():
    ok = True

    print("== 1. Exact matrix-tree (Bareiss) vs closed form n*(L_{2n}-2*(-1)^n)/5 ==")
    for n in [5, 6, 7, 8, 9, 10, 12, 15, 20, 24]:
        a = tau_kirchhoff(n)
        b = tau_closed(n)
        flag = "MATCH" if a == b else "MISMATCH"
        ok &= a == b
        print(f"  n={n:3d}  tau={a}  closed={b}  {flag}")
    for n in [40, 80]:
        b = tau_closed(n)
        f = tau_eigen_product(n)
        rel = abs(f - b) / b
        flag = "MATCH" if rel < 1e-9 else "MISMATCH"
        ok &= rel < 1e-9
        print(f"  n={n:3d}  tau={b}  eigen-product={f:.6e} (rel err {rel:.2e})  {flag}")

    print("\n== 2. Growth rates tau^(1/n) (verifier reported 2.81 / 2.76 / 2.71) ==")
    for n in [20, 40, 80]:
        t = tau_closed(n)
        r = t ** (1.0 / n)
        print(f"  n={n:3d}  tau^(1/n)={r:.6f}")
        ok &= 2.7 <= r <= 2.82

    print("\n== 3. Laplacian eigenvalue ceiling ==")
    # f(t) = 4 - 2 cos t - 2 cos 2t, f'(t) = 2 sin t (1 + 4 cos t);
    # interior maximum at cos t = -1/4:  f = 4 + 1/2 + 2*(1/8) = 25/4 = 6.25.
    theta = math.acos(-0.25)
    sup = 4 - 2 * math.cos(theta) - 2 * math.cos(2 * theta)
    print(f"  continuous sup over theta: {sup:.6f}  (exact 25/4 = 6.25)")
    for n in [40, 80]:
        m = max((2 - 2 * math.cos(2 * math.pi * k / n))
                + (2 - 2 * math.cos(4 * math.pi * k / n)) for k in range(1, n))
        print(f"  max_k lambda_k (n={n}) = {m:.6f}")
        ok &= m < 6.25 + 1e-9

    print("\n== 4. Decisive comparisons ==")
    phi_sq = ((1 + math.sqrt(5)) / 2) ** 2
    alpha_sq = (2 + math.sqrt(3)) ** 2
    print(f"  true growth constant  phi^2   = (3+sqrt(5))/2 = {phi_sq:.6f}")
    print(f"  claimed root limit    alpha^2 = (2+sqrt(3))^2 = 7+4*sqrt(3) = {alpha_sq:.6f}")
    print("  separator: phi^2 < 3 < 25/4 = 6.25 < 8 < 9 < alpha^2")
    t80 = tau_closed(80)
    checks = [
        ("tau(80) < 8^80", t80 < 8 ** 80),
        ("tau(80) > 2^80", t80 > 2 ** 80),
        ("tau(80)*2^80 > 5^80  (rate > 5/2)", t80 * 2 ** 80 > 5 ** 80),
        ("alpha^2 > 8  (sqrt(3) > 1/4)", alpha_sq > 8.0),
        ("alpha^2 < 14 (sqrt(3) < 7/4: 48 < 49)", alpha_sq < 14.0),
        ("phi^2 < 3   (sqrt(5) < 3: 5 < 9)", phi_sq < 3.0),
        ("phi^2 > 5/2 (sqrt(5) > 2: 4 < 5)", phi_sq > 2.5),
    ]
    for name, c in checks:
        print(f"  {'PASS' if c else 'FAIL'}  {name}")
        ok &= c

    print("\n== 5. Literals certified in lean4/Main.lean ==")
    for n in [5, 6, 7, 8, 9, 10, 12, 15, 20, 40, 80]:
        print(f"  tau {n} = {tau_closed(n)}")

    print("\nALL CHECKS PASSED" if ok else "\nSOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
