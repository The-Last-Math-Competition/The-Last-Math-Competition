#!/usr/bin/env python3
"""
Exact verification suite for Conjecture 00000007166:
  "The Kantorovich inequality with the multiplicative bound of the quotient.
   Conjecture: The optimal constant is an explicit function of the condition
   ratio, and the minimum of the function is the harmonic mean."

All core verifications use exact rational arithmetic (fractions.Fraction) with
zero floating-point approximation error.

Summary of verified results:
  1. Clause 1 (TRUE): For every n >= 1, positive eigenvalues
     0 < m <= lambda_1, ..., lambda_n <= M with condition ratio kappa = M / m >= 1,
     and every nonzero x in Q^n (including general orthogonally diagonalizable
     SPD matrices A = Q diag(lambda) Q^T with Q^T Q = I_n):
         1 <= <Ax, x><A^{-1}x, x> / ||x||^4 <= (M + m)^2 / (4 M m) = K(kappa),
     where K(kappa) = (kappa + 1)^2 / (4 kappa) = AM(M, m) / HM(M, m).
     Moreover, for every n >= 2 and kappa >= 1, the upper bound K(kappa) is
     exact (tight), attained at x = q_min + q_max (equal weights 1/2, 1/2 on
     eigenspaces for m and M), uniquely so when m < M and lambda_i are distinct.
  2. Clause 2 (FALSE across all candidate readings A, B, C, D):
     - Reading A: min_{kappa >= 1} K(kappa) = min_{kappa > 0} K(kappa) = 1
       (attained uniquely at kappa = 1), NOT HM(M, m) and NOT HM(kappa, 1).
     - Reading B: min_{x != 0} Q_A(x) = 1 (attained on each eigenspace of A),
       NOT HM(M, m) and NOT HM(kappa, 1).
     - Reading C: Reciprocal function R(kappa) = K(kappa)^{-1} = 4*kappa/(kappa+1)^2
       equals HM(M, m) / AM(M, m) != HM(M, m), has maximum 1 at kappa = 1, is
       strictly decreasing on [1, inf), and has NO minimum on [1, inf) (inf = 0).
     - Reading D: min_{||x||=1} <Ax, x> = m < HM(M, m) for m < M, while at the
       Kantorovich extremizer, <Ax, x>/||x||^2 = AM(M, m) and
       <A^{-1}x, x>/||x||^2 = HM(M, m)^{-1} (reciprocal of HM, not HM).
"""

from fractions import Fraction
import random
import sys
from typing import List, Sequence, Tuple


def am(a: Fraction, b: Fraction) -> Fraction:
    """Arithmetic mean (a + b) / 2."""
    return (a + b) / Fraction(2)


def hm(a: Fraction, b: Fraction) -> Fraction:
    """Harmonic mean 2ab / (a + b) for a + b != 0."""
    return (Fraction(2) * a * b) / (a + b)


def kantorovich_k(kappa: Fraction) -> Fraction:
    """Optimal Kantorovich constant K(kappa) = (kappa + 1)^2 / (4 * kappa)."""
    return (kappa + Fraction(1)) ** 2 / (Fraction(4) * kappa)


def kantorovich_r(kappa: Fraction) -> Fraction:
    """Reciprocal Wielandt-Kantorovich constant R(kappa) = 4 * kappa / (kappa + 1)^2."""
    return (Fraction(4) * kappa) / ((kappa + Fraction(1)) ** 2)


def dot(u: Sequence[Fraction], v: Sequence[Fraction]) -> Fraction:
    return sum((ui * vi for ui, vi in zip(u, v)), Fraction(0))


def mat_vec(mat: Sequence[Sequence[Fraction]], vec: Sequence[Fraction]) -> List[Fraction]:
    return [dot(row, vec) for row in mat]


def mat_mul(a: Sequence[Sequence[Fraction]], b: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    n = len(a)
    p = len(b[0])
    bt = [[b[r][c] for r in range(len(b))] for c in range(p)]
    return [[dot(a[i], bt[j]) for j in range(p)] for i in range(n)]


def transpose(mat: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    return [[mat[r][c] for r in range(len(mat))] for c in range(len(mat[0]))]


def householder_orthogonal(v: Sequence[Fraction]) -> List[List[Fraction]]:
    """Construct an exact rational orthogonal matrix H = I - 2 v v^T / ||v||^2."""
    n = len(v)
    norm_sq = dot(v, v)
    assert norm_sq > 0
    mat: List[List[Fraction]] = []
    for i in range(n):
        row: List[Fraction] = []
        for j in range(n):
            entry = (Fraction(1) if i == j else Fraction(0)) - (
                Fraction(2) * v[i] * v[j] / norm_sq
            )
            row.append(entry)
        mat.append(row)
    return mat


def verify_master_identities() -> None:
    print("[1/5] Verifying exact algebraic master identities for Clause 1...")
    rng = random.Random(716601)
    trials = 400
    for t in range(trials):
        n = rng.choice([1, 2, 3, 4, 5, 8])
        m = Fraction(rng.randint(1, 9), rng.randint(1, 7))
        if n == 1 or t % 10 == 0:
            M = m
            lambdas = [m for _ in range(n)]
        else:
            delta = Fraction(rng.randint(1, 15), rng.randint(1, 7))
            M = m + delta
            lambdas = [m, M]
            for _ in range(n - 2):
                alpha = Fraction(rng.randint(0, 10), 10)
                lambdas.append(m + alpha * (M - m))
            rng.shuffle(lambdas)

        raw_x = [Fraction(rng.randint(-6, 6), rng.randint(1, 4)) for _ in range(n)]
        if all(xi == 0 for xi in raw_x):
            raw_x[0] = Fraction(1)

        norm_sq = sum((xi * xi for xi in raw_x), Fraction(0))
        weights = [xi * xi / norm_sq for xi in raw_x]
        assert sum(weights, Fraction(0)) == Fraction(1)

        S = sum((w * lam for w, lam in zip(weights, lambdas)), Fraction(0))
        T = sum((w / lam for w, lam in zip(weights, lambdas)), Fraction(0))
        kappa = M / m

        # Identity 1 (Lower bound): S * (S * T - 1) == sum_i w_i * (lam_i - S)^2 / lam_i
        lhs_lower = S * (S * T - Fraction(1))
        rhs_lower = sum(
            (w * ((lam - S) ** 2) / lam for w, lam in zip(weights, lambdas)),
            Fraction(0),
        )
        assert lhs_lower == rhs_lower, f"Lower identity mismatch: {lhs_lower} != {rhs_lower}"
        assert rhs_lower >= 0 and S > 0
        assert S * T >= Fraction(1)

        # Identity 2 (Upper bound):
        # (M + m)^2 / (4Mm) - S*T == (2S - (M + m))^2 / (4Mm)
        #                            + S * sum_i w_i * (M - lam_i)*(lam_i - m)/(M*m*lam_i)
        bound = (M + m) ** 2 / (Fraction(4) * M * m)
        assert bound == kantorovich_k(kappa)
        assert bound == am(M, m) / hm(M, m)

        sq_term = (Fraction(2) * S - (M + m)) ** 2 / (Fraction(4) * M * m)
        eig_defect = S * sum(
            (
                w * (M - lam) * (lam - m) / (M * m * lam)
                for w, lam in zip(weights, lambdas)
            ),
            Fraction(0),
        )
        assert bound - S * T == sq_term + eig_defect, "Upper master identity mismatch"
        assert sq_term >= 0 and eig_defect >= 0
        assert S * T <= bound

    print(f"      PASS: {trials} exact rational master-identity trials verified.")


def verify_orthogonal_spd_and_sharpness() -> None:
    print("[2/5] Verifying non-diagonal SPD matrices A = Q diag(lambda) Q^T and sharpness...")
    rng = random.Random(716602)
    tested_matrices = 0
    for n in [2, 3, 4, 5, 6]:
        for trial in range(25):
            m = Fraction(rng.randint(1, 8), rng.randint(1, 5))
            M = m if trial == 0 else m + Fraction(rng.randint(1, 12), rng.randint(1, 5))
            kappa = M / m

            # Place m at index 0 and M at index 1, intermediate eigenvalues elsewhere
            lambdas = [m, M] + [
                m + Fraction(rng.randint(0, 8), 8) * (M - m) for _ in range(n - 2)
            ]

            # Product of two exact rational Householder reflections gives det = +1 orthogonal Q
            v1 = [Fraction(rng.randint(1, 5)) for _ in range(n)]
            v2 = [Fraction(rng.randint(-4, 5) or 1) for _ in range(n)]
            Q = mat_mul(householder_orthogonal(v1), householder_orthogonal(v2))
            QT = transpose(Q)

            # Confirm exact orthogonality Q^T Q = I_n
            ident = mat_mul(QT, Q)
            for i in range(n):
                for j in range(n):
                    expected = Fraction(1) if i == j else Fraction(0)
                    assert ident[i][j] == expected

            diag_a = [
                [lambdas[i] if i == j else Fraction(0) for j in range(n)]
                for i in range(n)
            ]
            diag_inv = [
                [Fraction(1) / lambdas[i] if i == j else Fraction(0) for j in range(n)]
                for i in range(n)
            ]
            A = mat_mul(mat_mul(Q, diag_a), QT)
            A_inv = mat_mul(mat_mul(Q, diag_inv), QT)

            # Confirm A * A_inv == I_n
            prod = mat_mul(A, A_inv)
            for i in range(n):
                for j in range(n):
                    assert prod[i][j] == (Fraction(1) if i == j else Fraction(0))

            # Random nonzero vectors satisfy 1 <= Q_A(x) <= K(kappa)
            for _ in range(10):
                x = [Fraction(rng.randint(-5, 5)) for _ in range(n)]
                if all(xi == 0 for xi in x):
                    x[0] = Fraction(1)
                norm4 = dot(x, x) ** 2
                q_val = dot(mat_vec(A, x), x) * dot(mat_vec(A_inv, x), x) / norm4
                assert Fraction(1) <= q_val <= kantorovich_k(kappa)

            # Exact tightness witness: x* = q_0 + q_1 (sum of columns 0 and 1 of Q)
            q0 = [Q[r][0] for r in range(n)]
            q1 = [Q[r][1] for r in range(n)]
            x_star = [q0[r] + q1[r] for r in range(n)]
            norm_sq_star = dot(x_star, x_star)
            assert norm_sq_star == Fraction(2)

            rayleigh_a = dot(mat_vec(A, x_star), x_star) / norm_sq_star
            rayleigh_inv = dot(mat_vec(A_inv, x_star), x_star) / norm_sq_star
            q_star = rayleigh_a * rayleigh_inv

            assert rayleigh_a == am(M, m)
            assert rayleigh_inv == Fraction(1) / hm(M, m)
            assert q_star == kantorovich_k(kappa)

            # Eigenvector witness q_0 attains the lower bound Q_A(q_0) = 1
            q_min_val = (
                dot(mat_vec(A, q0), q0) * dot(mat_vec(A_inv, q0), q0) / (dot(q0, q0) ** 2)
            )
            assert q_min_val == Fraction(1)
            tested_matrices += 1

    print(
        f"      PASS: {tested_matrices} exact orthogonal SPD matrices (n=2..6) "
        f"verified for bounds and exact sharpness."
    )


def verify_reading_a_and_b_refutations() -> None:
    print("[3/5] Verifying refutation of Clause 2 under Readings A and B...")
    # Reading A: K(kappa) - 1 = (kappa - 1)^2 / (4*kappa) >= 0, unique min = 1 at kappa = 1.
    sample_kappas = [
        Fraction(1, 4),
        Fraction(1, 2),
        Fraction(1, 1),
        Fraction(3, 2),
        Fraction(2, 1),
        Fraction(3, 1),
        Fraction(5, 1),
        Fraction(10, 1),
        Fraction(100, 1),
    ]
    for kap in sample_kappas:
        diff = kantorovich_k(kap) - Fraction(1)
        assert diff == (kap - Fraction(1)) ** 2 / (Fraction(4) * kap)
        if kap == Fraction(1):
            assert diff == Fraction(0)
        else:
            assert diff > Fraction(0)
        if kap > Fraction(1):
            # Normalized harmonic mean HM(kap, 1) = 2*kap/(kap+1) is strictly > 1 = min K
            hm_norm = hm(kap, Fraction(1))
            assert hm_norm - Fraction(1) == (kap - Fraction(1)) / (kap + Fraction(1)) > 0
            assert hm_norm != Fraction(1)

    # Canonical concrete counterexample 1: m = 1, M = 3 (kappa = 3)
    m1, M1 = Fraction(1), Fraction(3)
    kap1 = M1 / m1
    assert kap1 == Fraction(3)
    assert kantorovich_k(Fraction(1)) == Fraction(1)  # global minimum of K
    assert kantorovich_k(kap1) == Fraction(4, 3)      # value of K(3)
    assert hm(M1, m1) == Fraction(3, 2)               # harmonic mean HM(3, 1) = 3/2
    assert hm(M1, m1) != Fraction(1)                  # != min K and != min Q_A
    assert hm(M1, m1) != kantorovich_k(kap1)          # != K(3)

    # Canonical concrete counterexample 2 (scale/homogeneity obstruction): m = 2, M = 2 (kappa = 1)
    m2, M2 = Fraction(2), Fraction(2)
    assert kantorovich_k(M2 / m2) == Fraction(1)
    assert hm(M2, m2) == Fraction(2)
    assert kantorovich_k(M2 / m2) != hm(M2, m2)

    print(
        "      PASS: Reading A (min K(kappa) = 1) and Reading B (min_{x!=0} Q_A(x) = 1) "
        "strictly refuted; e.g. at (m, M) = (1, 3), min = 1, K(3) = 4/3, HM(3, 1) = 3/2."
    )


def verify_reading_c_and_d_refutations() -> None:
    print("[4/5] Verifying refutation of Clause 2 under Readings C and D...")
    # Reading C: R(kappa) = 4*kappa / (kappa + 1)^2 = HM(M, m) / AM(M, m)
    # 1) Value mismatch at (m, M) = (1, 3): R(3) = 3/4 != 3/2 = HM(3, 1)
    assert kantorovich_r(Fraction(3)) == Fraction(3, 4)
    assert kantorovich_r(Fraction(3)) == hm(Fraction(3), Fraction(1)) / am(
        Fraction(3), Fraction(1)
    )
    assert kantorovich_r(Fraction(3)) != hm(Fraction(3), Fraction(1))

    # 2) Strict decrease on [1, inf): for 1 <= k1 < k2, R(k1) > R(k2)
    grid = [Fraction(1) + Fraction(i, 5) for i in range(40)]
    for i in range(len(grid) - 1):
        k1, k2 = grid[i], grid[i + 1]
        lhs = kantorovich_r(k1) - kantorovich_r(k2)
        rhs = (
            Fraction(4)
            * (k2 - k1)
            * (k1 * k2 - Fraction(1))
            / (((k1 + Fraction(1)) ** 2) * ((k2 + Fraction(1)) ** 2))
        )
        assert lhs == rhs and lhs > 0

    # 3) Infimum is 0 (no minimum on [1, inf)): for any eps > 0, kappa = ceil(4/eps) + 1 gives 0 < R(kappa) < eps
    for eps_den in [2, 10, 100, 10000]:
        eps = Fraction(1, eps_den)
        kap = Fraction(4 * eps_den + 1)
        r_val = kantorovich_r(kap)
        assert Fraction(0) < r_val < Fraction(4) / kap < eps

    # Reading D: Rayleigh quotient minimum and extremizer values
    for m_num in range(1, 6):
        for M_num in range(m_num + 1, 10):
            m, M = Fraction(m_num), Fraction(M_num)
            # Global minimum of <Ax, x>/||x||^2 is m, strictly less than HM(M, m)
            assert hm(M, m) - m == m * (M - m) / (M + m) > 0
            # Extremizer <Ax, x>/||x||^2 is AM(M, m), strictly greater than HM(M, m)
            assert am(M, m) - hm(M, m) == (M - m) ** 2 / (Fraction(2) * (M + m)) > 0
            # Extremizer <A^{-1}x, x>/||x||^2 is 1 / HM(M, m); at (1, 3), 2/3 != 3/2
            if (m, M) == (Fraction(1), Fraction(3)):
                assert Fraction(1) / hm(M, m) == Fraction(2, 3) != hm(M, m)

    print(
        "      PASS: Reading C (R(kappa) has max 1, no min on [1, inf), inf = 0) "
        "and Reading D (Rayleigh values m, AM, HM^{-1} != HM) strictly refuted."
    )


def verify_uniqueness_at_extremum() -> None:
    print("[5/5] Verifying equality characterization for both lower and upper bounds...")
    # Exhaustive rational simplex grid for n = 3 with distinct eigenvalues (1, 2, 4)
    m, mid, M = Fraction(1), Fraction(2), Fraction(4)
    lambdas = [m, mid, M]
    upper = kantorovich_k(M / m)  # (4 + 1)^2 / 16 = 25/16
    assert upper == Fraction(25, 16)

    denom = 24
    attained_upper = []
    attained_lower = []
    for a in range(denom + 1):
        for b in range(denom + 1 - a):
            c = denom - a - b
            w = [Fraction(a, denom), Fraction(b, denom), Fraction(c, denom)]
            S = sum((wi * li for wi, li in zip(w, lambdas)), Fraction(0))
            T = sum((wi / li for wi, li in zip(w, lambdas)), Fraction(0))
            q = S * T
            assert Fraction(1) <= q <= upper
            if q == upper:
                attained_upper.append(tuple(w))
            if q == Fraction(1):
                attained_lower.append(tuple(w))

    assert attained_upper == [(Fraction(1, 2), Fraction(0), Fraction(1, 2))]
    assert sorted(attained_lower) == sorted(
        [
            (Fraction(1), Fraction(0), Fraction(0)),
            (Fraction(0), Fraction(1), Fraction(0)),
            (Fraction(0), Fraction(0), Fraction(1)),
        ]
    )
    print(
        "      PASS: Equality holds at upper bound iff w = (1/2, 0, 1/2), "
        "and at lower bound iff w is supported on a single eigenvalue."
    )


def main() -> int:
    print("=" * 74)
    print("Conjecture 00000007166 -- Exact Rational Verification Suite")
    print("=" * 74)
    verify_master_identities()
    verify_orthogonal_spd_and_sharpness()
    verify_reading_a_and_b_refutations()
    verify_reading_c_and_d_refutations()
    verify_uniqueness_at_extremum()
    print("=" * 74)
    print("OVERALL VERDICT: Conjecture 00000007166 is FALSE (Clause 1 TRUE; Clause 2 FALSE).")
    print("ALL EXACT VERIFICATION CHECKS PASSED (exit code 0).")
    print("=" * 74)
    return 0


if __name__ == "__main__":
    sys.exit(main())
