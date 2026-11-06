#!/usr/bin/env python3
"""Exact check of conjecture 00000002118 (third cumulant of Quicksort comparisons).

Model (standard, Knuth / Rosler / Neininger-Ruschendorf):
  C_0 = C_1 = 0 (deterministic).
  For n >= 2:  C_n = (n-1) + C_J + C'_{n-1-J},
  J uniform on {0,...,n-1}; C and C' are independent copies of the cost.
  Here C_n is the number of comparisons of Quicksort with uniform random pivot
  (pivot compared with the other n-1 elements, then recursion on both parts).

Two independent exact computations:
  (A) exact pmf of C_n (dict value -> Fraction) by convolution, for n <= N_LAW;
  (B) exact raw moments m1, m2, m3 by the moment recursion, for n <= N_MOM.
Third cumulant: kappa3 = m3 - 3*m1*m2 + 2*m1^3 (equals the third central moment).
All arithmetic over Fraction, so no rounding is involved in the exact values.
"""
from fractions import Fraction as F
import math

N_LAW = 12     # pmf-based check range
N_MOM = 120    # moment-recursion range (exact)


def law_pmfs(N):
    """Exact pmf of C_n for n = 0..N, by direct convolution (ground truth)."""
    pmf = {0: {0: F(1)}, 1: {0: F(1)}}
    for n in range(2, N + 1):
        a = n - 1
        acc = {}
        for j in range(n):
            k = n - 1 - j
            for x, px in pmf[j].items():
                for y, py in pmf[k].items():
                    v = a + x + y
                    acc[v] = acc.get(v, F(0)) + px * py / n
        pmf[n] = acc
    return pmf


def moments_from_pmf(p):
    m1 = sum(v * q for v, q in p.items())
    m2 = sum(v * v * q for v, q in p.items())
    m3 = sum(v ** 3 * q for v, q in p.items())
    return m1, m2, m3


def moment_recursion(N):
    """Exact raw moments (m1, m2, m3) of C_n for n = 0..N.

    For a mixture over J (weight 1/n) of independent X ~ C_j and Y ~ C_k, k = n-1-j,
    with shift a = n-1:  W = a + X + Y.
    """
    M = [(F(0), F(0), F(0)), (F(0), F(0), F(0))]
    for n in range(2, N + 1):
        a = n - 1
        s1 = s2 = s3 = F(0)
        for j in range(n):
            k = n - 1 - j
            x1, x2, x3 = M[j]
            y1, y2, y3 = M[k]
            z1 = x1 + y1
            z2 = x2 + 2 * x1 * y1 + y2
            z3 = x3 + 3 * x2 * y1 + 3 * x1 * y2 + y3
            w1 = a + z1
            w2 = a * a + 2 * a * z1 + z2
            w3 = a ** 3 + 3 * a * a * z1 + 3 * a * z2 + z3
            s1 += w1
            s2 += w2
            s3 += w3
        M.append((s1 / n, s2 / n, s3 / n))
    return M


def kappa3(m):
    m1, m2, m3 = m
    return m3 - 3 * m1 * m2 + 2 * m1 ** 3


def H(n):
    return sum(F(1, i) for i in range(1, n + 1))


def main():
    print("=== Model: C_n = (n-1) + C_J + C'_{n-1-J}, C_0 = C_1 = 0 ===")

    pmf = law_pmfs(N_LAW)
    M = moment_recursion(N_MOM)

    # (1) Cross-check the two exact computations for n <= N_LAW
    ok = all(moments_from_pmf(pmf[n]) == M[n] for n in range(N_LAW + 1))
    print("pmf-based and moment-recursion moments agree exactly for n<=%d: %s" % (N_LAW, ok))

    # (2) Sanity check of mean against closed form 2(n+1)H_n - 4n
    mean_ok = all(M[n][0] == 2 * (n + 1) * H(n) - 4 * n for n in range(2, N_MOM + 1))
    print("mean equals 2(n+1)H_n - 4n (exact) for 2<=n<=%d: %s" % (N_MOM, mean_ok))

    # (3) Small-n exact values, incl. hand check C_3 in {2 (prob 1/3), 3 (prob 2/3)}
    print("\nC_3 pmf:", {v: str(q) for v, q in sorted(pmf[3].items())})
    print("C_2 pmf:", {v: str(q) for v, q in sorted(pmf[2].items())})

    kap = {n: kappa3(M[n]) for n in range(2, N_MOM + 1)}
    print("\nExact kappa3(n) for n=2..12:")
    for n in range(2, N_LAW + 1):
        print("  n=%2d  kappa3 = %-28s = %.9f" % (n, str(kap[n]), float(kap[n])))

    # Check the scanner's expected values
    print("\nScanner's expected values:")
    print("  kappa3(2) = 0 ?                    %s" % (kap[2] == 0))
    print("  kappa3(3) = -2/27 ?                %s" % (kap[3] == F(-2, 27)))
    print("  kappa3(4) ~ 0.240741 ?             %.6f" % float(kap[4]))
    print("  kappa3(5) ~ 1.728 ?                %.6f" % float(kap[5]))
    print("  kappa3(12) ~ 136.954 ?             %.6f" % float(kap[12]))

    # (4) Test of the claimed form kappa3(n) = 2n - 6 ln n + C with natural log
    L = math.log
    print("\n--- Natural-log form: kappa3(n) - (2n - 6 ln n) should be constant ---")
    f = {}
    for n in range(2, N_LAW + 1):
        f[n] = float(kap[n]) - (2 * n - 6 * L(n))
        print("  n=%2d  f(n) = %.6f" % (n, f[n]))
    C2 = float(kap[2]) - 4 + 6 * L(2)
    C3 = float(kap[3]) - 6 + 6 * L(3)
    print("C forced by n=2: 6 ln2 - 4        = %.6f" % C2)
    print("C forced by n=3: -2/27 - 6 + 6ln3 = %.6f" % C3)
    print("difference C3 - C2 = %.6f  (6 ln(3/2) - 56/27 = %.6f)" % (C3 - C2, 6 * L(1.5) - 56 / 27))

    # (5) Exact general-base test: is there ANY base b with kappa3(n) = 2n - 6 log_b n + C ?
    # g(n) = kappa3(n) - 2n = -6 log_b n + C.  Using n=2,3 exactly:
    #   g(3) - g(2) = -6 log_b(3/2)  and  g(3)-g(2) = -2/27 - 2 = -56/27 (exact)
    # so log_b(3/2) = 28/81 exactly, i.e. ln b = (81/28) ln(3/2).  Test n = 4..12.
    g = {n: kap[n] - 2 * n for n in range(2, N_LAW + 1)}
    g_diff_exact = g[3] - g[2]
    log_b_32 = -g_diff_exact / 6  # exact Fraction
    print("\n--- General base b: forced by n=2,3 exactly ---")
    print("g(3)-g(2) = %s ;  log_b(3/2) = %s" % (g_diff_exact, log_b_32))
    ln_b = L(1.5) / float(log_b_32)
    print("implied ln b = %.9f  (b = %.6f)" % (ln_b, math.exp(ln_b)))
    logb = lambda n: L(n) / ln_b
    C_b = float(g[2]) + 6 * logb(2)
    print("implied C = %.9f" % C_b)
    print("residual R(n) = g(n) + 6 log_b n - C  (must be 0 for every n if the form holds):")
    for n in range(3, N_LAW + 1):
        R = float(g[n]) + 6 * logb(n) - C_b
        print("  n=%2d  R(n) = %+.9f" % (n, R))
    R4 = float(g[4]) + 6 * logb(4) - C_b
    print("Base 2 and base 10 are also excluded: base-2 would need log_2(3/2)=%.6f, have %.6f"
          % (L(1.5) / L(2), float(log_b_32)))
    print("  base-10 would need log_10(3/2)=%.6f, have %.6f" % (L(1.5) / L(10), float(log_b_32)))
    print("  => no base b works at n=4 (|R(4)| = %.6f > 0)" % abs(R4))

    # (6) Growth: is kappa3(n) linear (main term 2n) or cubic?
    print("\n--- Growth of kappa3 (exact values, float view) ---")
    print("  n      kappa3(n)          kappa3/n^3       kappa3-(2n-6ln n)")
    for n in [12, 20, 30, 40, 60, 80, 100, 120]:
        v = float(kap[n])
        print("  %3d  %18.6f   %12.6f   %16.4f" % (n, v, v / n ** 3, v - (2 * n - 6 * L(n))))

    ratios = [float(kap[n]) / n ** 3 for n in (60, 90, 120)]
    print("\nkappa3(n)/n^3 at n=60,90,120: %s" % ["%.5f" % r for r in ratios])
    print("kappa3(120) / kappa3(60) = %.4f   (linear law would give ~2, cubic ~8)"
          % (float(kap[120]) / float(kap[60])))


if __name__ == "__main__":
    main()
