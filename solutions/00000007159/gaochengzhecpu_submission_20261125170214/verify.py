#!/usr/bin/env python3
"""
Standalone exact verification script for Conjecture 00000007159.
Uses only the Python 3 standard library (exact integer and rational arithmetic).

Verifies:
1. Positive regimes (commuting PSD simplex-lattice system for m >= 1, and noncommuting
   two-matrix identities & log-convexity on Delta_k^(2) across n = 2, 3, 4).
2. All eight explicit 2x2 strictly positive definite integer Gram counterexamples
   (A = L^T L with det(L) != 0) refuting every candidate simplex-lattice
   multiplicative trace-product system:
   - Two-matrix lattice-semigroup submultiplicativity on Delta_4^(2)
   - Three-matrix cycle-partition trace-product submultiplicativity on Delta_3^(3)
   - Three-matrix simplex-lattice interior positivity at (1,1,1) in Delta_3^(3)
   - Three-matrix simplex-lattice midpoint log-convexity on Delta_4^(3) (all traces > 0)
   - Three-matrix pure-interior midpoint log-convexity on Delta_5^(3) (all traces > 0, det = 1)
   - Three-matrix Frobenius-norm / sandwich log-convexity on Delta_3^(3) (det = 1)
   - Three-matrix Lieb-Thirring / word-grouping extrema at (2,2,2) in Delta_6^(3)
   - Three-matrix Ordered Muirhead majorization on Delta_6^(3) and Word-Averaged
     Hurwitz/BMV Muirhead majorization on Delta_5^(3) (cross-checked via both
     Pascal lattice DP and explicit enumeration over all noncommutative words).
"""

import itertools
import random
import sys
from fractions import Fraction


def mat_eye(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def mat_add(A, B):
    n = len(A)
    return [[A[i][j] + B[i][j] for j in range(n)] for i in range(n)]


def mat_sub(A, B):
    n = len(A)
    return [[A[i][j] - B[i][j] for j in range(n)] for i in range(n)]


def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def mat_T(A):
    n = len(A)
    return [[A[j][i] for j in range(n)] for i in range(n)]


def mat_pow(A, p):
    n = len(A)
    res = mat_eye(n)
    base = A
    e = p
    while e > 0:
        if e & 1:
            res = mat_mul(res, base)
        base = mat_mul(base, base)
        e >>= 1
    return res


def tr(A):
    return sum(A[i][i] for i in range(len(A)))


def frob_sq(A):
    return tr(mat_mul(mat_T(A), A))


def det2(A):
    return A[0][0] * A[1][1] - A[0][1] * A[1][0]


def gram_of(L):
    return mat_mul(mat_T(L), L)


def assert_strict_spd2_gram(L, expected_M=None):
    dL = det2(L)
    assert dL != 0, f"Expected det(L) != 0, got {dL}"
    M = gram_of(L)
    if expected_M is not None:
        assert M == expected_M, f"Expected M={expected_M}, got {M}"
    assert M == mat_T(M), "Matrix not symmetric"
    assert M[0][0] > 0 and tr(M) > 0 and det2(M) == dL * dL > 0, "Sylvester SPD check failed"
    return M


def ordered_prod(mats, alpha):
    n = len(mats[0])
    P = mat_eye(n)
    for M, e in zip(mats, alpha):
        if e > 0:
            P = mat_mul(P, mat_pow(M, e))
    return P


def ordered_prod_trace(mats, alpha):
    return tr(ordered_prod(mats, alpha))


def hurwitz_dp_mat(X, Y, Z, a, b, c):
    n = len(X)
    dp = {}
    dp[(0, 0, 0)] = mat_eye(n)
    for s in range(1, a + b + c + 1):
        for i in range(a + 1):
            for j in range(b + 1):
                k = s - i - j
                if k < 0 or k > c:
                    continue
                acc = [[0] * n for _ in range(n)]
                if i > 0:
                    acc = mat_add(acc, mat_mul(dp[(i - 1, j, k)], X))
                if j > 0:
                    acc = mat_add(acc, mat_mul(dp[(i, j - 1, k)], Y))
                if k > 0:
                    acc = mat_add(acc, mat_mul(dp[(i, j, k - 1)], Z))
                dp[(i, j, k)] = acc
    return dp[(a, b, c)]


def verify_positive_regimes():
    print("[1/3] Verifying positive regimes (commuting m >= 1 and noncommuting m = 2)...")
    rng = random.Random(202607159)

    # 1A. Commuting non-negative diagonal regime (n=4, m=3, k=6)
    for _ in range(100):
        ds = [[rng.randint(0, 6) for _ in range(4)] for _ in range(3)]
        mats = [[[ds[m_i][i] if i == j else 0 for j in range(4)] for i in range(4)] for m_i in range(3)]
        # Midpoint check: (2,1,3) = 1/2((3,0,3) + (1,2,3))
        f_mid = ordered_prod_trace(mats, (2, 1, 3))
        f_l = ordered_prod_trace(mats, (3, 0, 3))
        f_r = ordered_prod_trace(mats, (1, 2, 3))
        assert f_mid * f_mid <= f_l * f_r
        # Submultiplicativity: (2,1,3) = (1,1,1) + (1,0,2)
        assert f_mid <= ordered_prod_trace(mats, (1, 1, 1)) * ordered_prod_trace(mats, (1, 0, 2))

    # 1B. Noncommuting two-matrix Gram PSD identities & log-convexity (n=2, 3, 4)
    for n in (2, 3, 4):
        for _ in range(80):
            X = [[rng.randint(-3, 3) for _ in range(n)] for _ in range(n)]
            Y = [[rng.randint(-3, 3) for _ in range(n)] for _ in range(n)]
            A = gram_of(X)
            B = gram_of(Y)
            AB = mat_mul(A, B)
            comm = mat_sub(AB, mat_mul(B, A))

            # Degree-2 positivity & submultiplicativity
            assert 0 <= tr(AB) <= tr(A) * tr(B)

            # Degree-4 Lieb-Thirring commutator identity
            lhs4 = 2 * tr(mat_mul(mat_pow(A, 2), mat_pow(B, 2))) - 2 * tr(mat_pow(AB, 2))
            assert lhs4 == frob_sq(comm) >= 0

            # Degree-5 word-grouping identity
            lhs5 = tr(mat_mul(mat_pow(A, 3), mat_pow(B, 2))) - tr(mat_mul(mat_mul(mat_pow(A, 2), B), AB))
            assert lhs5 == frob_sq(mat_mul(X, comm)) >= 0

            # Two-matrix simplex-lattice log-convexity for 1 <= p, q <= 4
            for p in range(0, 4):
                for q in range(0, 4):
                    mid = tr(mat_mul(mat_pow(A, p + 1), mat_pow(B, q + 1)))
                    left = tr(mat_mul(mat_pow(A, p + 2), mat_pow(B, q)))
                    right = tr(mat_mul(mat_pow(A, p), mat_pow(B, q + 2)))
                    assert mid * mid <= left * right

    print("      PASS: All positive regime identities and inequalities verified.")


def verify_counterexamples():
    print("[2/3] Verifying all eight explicit M_2(Z) Gram SPD counterexamples...")

    # Gram factors matching Counterexamples.lean byte-for-byte
    L_1_m1_0_1 = [[1, -1], [0, 1]]
    L_1_1_0_1 = [[1, 1], [0, 1]]
    L_m1_m1_1_0 = [[-1, -1], [1, 0]]
    L_m2_m1_1_0 = [[-2, -1], [1, 0]]
    L_m1_1_1_m2 = [[-1, 1], [1, -2]]
    L_2_1_1_1 = [[2, 1], [1, 1]]
    L_1_0_0_2 = [[1, 0], [0, 2]]
    L_1_2_0_1 = [[1, 2], [0, 1]]
    L_m1_0_1_m1 = [[-1, 0], [1, -1]]
    L_m2_0_1_m2 = [[-2, 0], [1, -2]]
    L_m3_1_m1_0 = [[-3, 1], [-1, 0]]
    L_1_0_3_1 = [[1, 0], [3, 1]]
    L_1_m3_0_1 = [[1, -3], [0, 1]]
    L_1_0_m2_1 = [[1, 0], [-2, 1]]

    # 1. Two-matrix submultiplicativity failure on Delta_4^(2)
    A1 = assert_strict_spd2_gram(L_1_m1_0_1, [[1, -1], [-1, 2]])
    B1 = assert_strict_spd2_gram(L_1_1_0_1, [[1, 1], [1, 2]])
    tr_AB = ordered_prod_trace([A1, B1], (1, 1))
    tr_A2B2 = ordered_prod_trace([A1, B1], (2, 2))
    assert tr_AB == 3 and tr_A2B2 == 11 and tr_A2B2 > tr_AB * tr_AB
    print(f"      [CE 1] m=2 submultiplicativity: tr(A^2 B^2) = {tr_A2B2} > {tr_AB}^2 = {tr_AB**2}")

    # 2. Three-matrix interior strict negativity at (1,1,1) in Delta_3^(3)
    A2 = assert_strict_spd2_gram(L_1_1_0_1, [[1, 1], [1, 2]])
    B2 = assert_strict_spd2_gram(L_m2_m1_1_0, [[5, 2], [2, 1]])
    C2 = assert_strict_spd2_gram(L_m1_1_1_m2, [[2, -3], [-3, 5]])
    tr_ABC_neg = ordered_prod_trace([A2, B2, C2], (1, 1, 1))
    assert tr_ABC_neg == -2 < 0
    print(f"      [CE 2] m=3 interior positivity: tr(A B C) = {tr_ABC_neg} < 0")

    # 3. Three-matrix cycle-partition trace-product submultiplicativity on Delta_3^(3)
    C3 = assert_strict_spd2_gram(L_2_1_1_1, [[5, 3], [3, 2]])
    tr_ABC_pos = ordered_prod_trace([A2, B2, C3], (1, 1, 1))
    tr_AB_tr_C = ordered_prod_trace([A2, B2, C3], (1, 1, 0)) * ordered_prod_trace([A2, B2, C3], (0, 0, 1))
    assert tr_ABC_pos == 79 and tr_AB_tr_C == 77 and tr_ABC_pos > tr_AB_tr_C
    print(f"      [CE 3] m=3 cycle trace-product: tr(A B C) = {tr_ABC_pos} > {tr_AB_tr_C} = tr(A B) tr(C)")

    # 4a. Simplex-lattice midpoint log-convexity failure on Delta_4^(3) (all traces > 0)
    B4 = assert_strict_spd2_gram(L_m1_m1_1_0, [[2, 1], [1, 1]])
    C4a = assert_strict_spd2_gram(L_1_0_0_2, [[1, 0], [0, 4]])
    f121 = ordered_prod_trace([A2, B4, C4a], (1, 2, 1))
    f211 = ordered_prod_trace([A2, B4, C4a], (2, 1, 1))
    f031 = ordered_prod_trace([A2, B4, C4a], (0, 3, 1))
    assert (f121, f211, f031) == (36, 39, 33) and f121 * f121 == 1296 > 1287 == f211 * f031
    print(f"      [CE 4a] m=3 Delta_4^(3) log-convexity: F(1,2,1)^2 = {f121**2} > {f211 * f031} = F(2,1,1) F(0,3,1)")

    # 4b. Pure-interior midpoint log-convexity failure on Delta_5^(3) (all traces > 0, det = 1)
    C4b = assert_strict_spd2_gram(L_1_2_0_1, [[1, 2], [2, 5]])
    f212 = ordered_prod_trace([A2, B4, C4b], (2, 1, 2))
    f311 = ordered_prod_trace([A2, B4, C4b], (3, 1, 1))
    f113 = ordered_prod_trace([A2, B4, C4b], (1, 1, 3))
    assert (f212, f311, f113) == (459, 207, 1014) and f212 * f212 == 210681 > 209898 == f311 * f113
    print(f"      [CE 4b] m=3 interior Delta_5^(3) log-convexity: F(2,1,2)^2 = {f212**2} > {f311 * f113} = F(3,1,1) F(1,1,3)")

    # 5. Frobenius-norm / Hermitian-sandwich log-convexity failure on Delta_3^(3)
    C5 = assert_strict_spd2_gram(L_m1_0_1_m1, [[2, -1], [-1, 1]])
    g111 = frob_sq(ordered_prod([A2, B4, C5], (1, 1, 1)))
    g201 = frob_sq(ordered_prod([A2, B4, C5], (2, 0, 1)))
    g021 = frob_sq(ordered_prod([A2, B4, C5], (0, 2, 1)))
    assert (g111, g201, g021) == (43, 7, 70) and g111 * g111 == 1849 > 490 == g201 * g021
    print(f"      [CE 5] m=3 Frobenius log-convexity: G(1,1,1)^2 = {g111**2} > {g201 * g021} = G(2,0,1) G(0,2,1)")

    # 6. Three-matrix Lieb-Thirring / word-grouping extrema failure at (2,2,2) in Delta_6^(3)
    C6 = assert_strict_spd2_gram(L_m2_0_1_m2, [[5, -2], [-2, 4]])
    ABC6 = ordered_prod([A2, B4, C6], (1, 1, 1))
    tr_ABC_sq = tr(mat_mul(ABC6, ABC6))
    tr_ABC_frob = frob_sq(ABC6)
    tr_grouped_222 = ordered_prod_trace([A2, B4, C6], (2, 2, 2))
    assert (tr_ABC_sq, tr_ABC_frob, tr_grouped_222) == (193, 337, 175)
    assert tr_ABC_sq > tr_grouped_222 > 0 and tr_ABC_frob > tr_grouped_222 > 0
    print(f"      [CE 6] m=3 Lieb-Thirring extrema: tr((ABC)^2)={tr_ABC_sq}, ||ABC||_F^2={tr_ABC_frob} > {tr_grouped_222}=tr(A^2 B^2 C^2)")

    # 7a. Symmetrized Ordered Matrix Muirhead failure on Delta_6^(3): (3,2,1) >- (2,2,2)
    C7a = assert_strict_spd2_gram(L_m3_1_m1_0, [[10, -3], [-3, 1]])
    ms7a = [A1, C4b, C7a]
    m321 = sum(ordered_prod_trace([ms7a[p[0]], ms7a[p[1]], ms7a[p[2]]], (3, 2, 1)) for p in itertools.permutations(range(3)))
    m222 = sum(ordered_prod_trace([ms7a[p[0]], ms7a[p[1]], ms7a[p[2]]], (2, 2, 2)) for p in itertools.permutations(range(3)))
    assert m321 == -8606 and m222 == -6900 and m321 < m222 < 0
    print(f"      [CE 7a] m=3 Ordered Muirhead (3,2,1) vs (2,2,2): {m321} < {m222} < 0")

    # 7b. Symmetrized Word-Averaged (Hurwitz/BMV) Muirhead failure on Delta_5^(3): (3,1,1) >- (2,2,1)
    A7b = assert_strict_spd2_gram(L_1_0_3_1, [[10, 3], [3, 1]])
    B7b = assert_strict_spd2_gram(L_1_m3_0_1, [[1, -3], [-3, 10]])
    C7b = assert_strict_spd2_gram(L_1_0_m2_1, [[5, -2], [-2, 1]])
    ms7b = [A7b, B7b, C7b]

    def hurwitz_by_words(alpha):
        letters = [0] * alpha[0] + [1] * alpha[1] + [2] * alpha[2]
        words = sorted(set(itertools.permutations(letters)))
        tot = 0
        for p in itertools.permutations(range(3)):
            for w in words:
                P = mat_eye(2)
                for l in w:
                    P = mat_mul(P, ms7b[p[l]])
                tot += tr(P)
        return len(words), tot, Fraction(tot, len(words))

    cnt311, sum311, avg311 = hurwitz_by_words((3, 1, 1))
    cnt221, sum221, avg221 = hurwitz_by_words((2, 2, 1))

    # Cross-check against Pascal lattice DP matching Lean's hurwitzSymWordSum3
    dp_sum311 = sum(tr(hurwitz_dp_mat(ms7b[p[0]], ms7b[p[1]], ms7b[p[2]], 3, 1, 1)) for p in itertools.permutations(range(3)))
    dp_sum221 = sum(tr(hurwitz_dp_mat(ms7b[p[0]], ms7b[p[1]], ms7b[p[2]], 2, 2, 1)) for p in itertools.permutations(range(3)))
    assert dp_sum311 == sum311 == 144480 and cnt311 == 20 and avg311 == 7224
    assert dp_sum221 == sum221 == 220800 and cnt221 == 30 and avg221 == 7360
    assert 0 < avg311 < avg221
    print(f"      [CE 7b] m=3 Hurwitz Word-Avg Muirhead (3,1,1) vs (2,2,1): 0 < {avg311} < {avg221}")


def verify_additional_variants():
    print("[3/3] Checking normalized trace tau = (1/n) tr and unimodular inverse invariance...")
    # Normalized trace tau(X) = (1/2) tr(X) scales homogeneous systems by (1/2)^k and fails identically;
    # for submultiplicativity tau(A^2 B^2) <= tau(AB)^2:
    # With A = [[10, 0], [0, 1]], B = [[11, 9], [9, 11]], tau(A^2 B^2) = 10201 > 14641/4 = tau(AB)^2!
    A = [[10, 0], [0, 1]]
    B = [[11, 9], [9, 11]]
    tau_A2B2 = Fraction(tr(mat_mul(mat_pow(A, 2), mat_pow(B, 2))), 2)
    tau_AB_sq = Fraction(tr(mat_mul(A, B)), 2) ** 2
    assert tau_A2B2 == 10201 and tau_AB_sq == Fraction(14641, 4) and tau_A2B2 > tau_AB_sq

    # Also verify positive Ordered Muirhead with strictly positive sum-of-squares SPD matrices at k=6:
    # (4,1,1) >- (3,2,1) with M^ord_(4,1,1) = 147776 < 147792 = M^ord_(3,2,1)
    M1 = [[4, -2], [-2, 4]]
    M2 = [[1, -2], [-2, 5]]
    M3 = [[5, -2], [-2, 1]]
    ms = [M1, M2, M3]
    v411 = sum(ordered_prod_trace([ms[p[0]], ms[p[1]], ms[p[2]]], (4, 1, 1)) for p in itertools.permutations(range(3)))
    v321 = sum(ordered_prod_trace([ms[p[0]], ms[p[1]], ms[p[2]]], (3, 2, 1)) for p in itertools.permutations(range(3)))
    assert 0 < v411 == 147776 < 147792 == v321
    print(f"      PASS: Normalized trace (tau(A^2 B^2)={tau_A2B2} > {tau_AB_sq}=tau(AB)^2) and positive Ordered Muirhead ({v411} < {v321}) verified.")


def main():
    print("=== Conjecture 00000007159 Exact Verification Suite ===")
    verify_positive_regimes()
    verify_counterexamples()
    verify_additional_variants()
    print("=== ALL VERIFICATION CHECKS PASSED (EXIT 0) ===")


if __name__ == "__main__":
    sys.exit(main() or 0)
