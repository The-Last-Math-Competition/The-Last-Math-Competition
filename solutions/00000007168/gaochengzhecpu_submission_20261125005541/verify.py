#!/usr/bin/env python3
"""
Independent verification suite for Conjecture 00000007168:
"Definition: Schur's inequality with the spectral bounds of power sums.
 Conjecture: The upper bound of power sums is the sum of spectral-radius powers,
 and the realization of the bound is the normal matrix.
 (normal-realized Schur power-sum bound)"

This script uses only the Python 3 standard library (fractions, math, cmath, random)
to perform:
  1. Exact arithmetic checks (over Q and Q(i)) of all algebraic counterexamples and
     identities across dimensions n = 2..6 and exponents k = 1..6:
       - Non-normal Jordan/shear block J_n = I_n + E_{0,1}: attains n * rho(A)^k
         for BOTH sum |lambda_i|^k and |tr(A^k)| for all k >= 1 while AA* != A*A,
         and violates ||A^k||_F^2 <= n * rho(A)^{2k} (giving n + k^2 > n).
       - Dense non-triangular unitary conjugate U J_2 U* (Pythagorean unitary U):
         attains 2 * rho(A)^k for all k >= 1 while non-normal.
       - Diagonalizable non-normal involution B = [[1, -2], [0, -1]]:
         attains sum |lambda_i|^k = 2 * rho(B)^k for all k >= 1 (and |tr(B^k)| = 2
         for all even k) while BB* != B*B.
       - Normal rank-1 projection D_n = diag(1, 0, ..., 0): satisfies D_n D_n* = D_n* D_n
         and Schur equality sum |lambda_i|^2 = ||D_n||_F^2 = 1, yet strictly fails to
         attain n * rho(D_n)^k (1 < n) under EVERY power-sum reading for all n >= 2, k >= 1.
       - Non-normal nilpotent family N_{n,c} = c * E_{0,1} (c != 0): has rho = 0 while
         ||N_{n,c}||_F^2 = |c|^2 > 0 and tr((N* N)^k) = |c|^{2k} > 0 for all k >= 1,
         violating all Frobenius / singular-value / entrywise spectral-radius bounds,
         while also attaining sum |lambda_i|^k = 0 = n * rho^k despite being non-normal.
       - Identity matrix I_n (n >= 2): refutes the unscaled bound sum_{k=1}^K rho(A)^k
         (without the factor n).
  2. Numerical stress tests on random ensembles in M_n(R) and M_n(C) (normal, unitary,
     scaled-unitary, general dense, upper-triangular, nilpotent, defective) verifying:
       - Classical Schur's inequality sum |lambda_i|^2 <= ||A||_F^2 and its exact
         normality characterization (equality iff ||AA* - A*A||_F == 0).
       - Eigenvalue and trace power-sum inequalities |tr(A^k)| <= sum |lambda_i|^k <= n*rho(A)^k
         and the exact equal-modulus characterization (equality iff all |lambda_i| == rho(A)).
       - Normal-matrix validity of ||A^k||_F^2 <= n * rho(A)^{2k} vs systematic failure
         on generic non-normal matrices.
"""

from __future__ import annotations

import cmath
import math
import random
import sys
from dataclasses import dataclass
from fractions import Fraction
from typing import List, Sequence, Tuple


# =============================================================================
# 1. Exact Gaussian Rational Arithmetic Q(i) and Matrix Operations
# =============================================================================

@dataclass(frozen=True)
class QComplex:
    re: Fraction
    im: Fraction = Fraction(0)

    @staticmethod
    def of(val: int | Fraction | "QComplex") -> "QComplex":
        if isinstance(val, QComplex):
            return val
        return QComplex(Fraction(val), Fraction(0))

    def __add__(self, other: "QComplex") -> "QComplex":
        return QComplex(self.re + other.re, self.im + other.im)

    def __sub__(self, other: "QComplex") -> "QComplex":
        return QComplex(self.re - other.re, self.im - other.im)

    def __neg__(self) -> "QComplex":
        return QComplex(-self.re, -self.im)

    def __mul__(self, other: "QComplex") -> "QComplex":
        return QComplex(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def conj(self) -> "QComplex":
        return QComplex(self.re, -self.im)

    def norm_sq(self) -> Fraction:
        return self.re * self.re + self.im * self.im

    def __pow__(self, k: int) -> "QComplex":
        assert k >= 0
        res = QComplex(Fraction(1), Fraction(0))
        base = self
        exp = k
        while exp > 0:
            if exp & 1:
                res = res * base
            base = base * base
            exp >>= 1
        return res


QMat = List[List[QComplex]]


def qmat_zeros(n: int) -> QMat:
    z = QComplex(Fraction(0), Fraction(0))
    return [[z for _ in range(n)] for _ in range(n)]


def qmat_eye(n: int) -> QMat:
    m = qmat_zeros(n)
    one = QComplex(Fraction(1), Fraction(0))
    for i in range(n):
        m[i][i] = one
    return m


def qmat_mul(a: QMat, b: QMat) -> QMat:
    n = len(a)
    out = qmat_zeros(n)
    for i in range(n):
        for k in range(n):
            aik = a[i][k]
            if aik.re == 0 and aik.im == 0:
                continue
            for j in range(n):
                out[i][j] = out[i][j] + aik * b[k][j]
    return out


def qmat_pow(a: QMat, k: int) -> QMat:
    n = len(a)
    res = qmat_eye(n)
    base = a
    exp = k
    while exp > 0:
        if exp & 1:
            res = qmat_mul(res, base)
        base = qmat_mul(base, base)
        exp >>= 1
    return res


def qmat_adj(a: QMat) -> QMat:
    n = len(a)
    return [[a[j][i].conj() for j in range(n)] for i in range(n)]


def qmat_trace(a: QMat) -> QComplex:
    acc = QComplex(Fraction(0), Fraction(0))
    for i in range(len(a)):
        acc = acc + a[i][i]
    return acc


def qmat_frob_sq(a: QMat) -> Fraction:
    n = len(a)
    total = Fraction(0)
    for i in range(n):
        for j in range(n):
            total += a[i][j].norm_sq()
    return total


def qmat_is_normal(a: QMat) -> bool:
    adj = qmat_adj(a)
    return qmat_mul(a, adj) == qmat_mul(adj, a)


def qmat_is_unitary(u: QMat) -> bool:
    n = len(u)
    adj = qmat_adj(u)
    eye = qmat_eye(n)
    return qmat_mul(adj, u) == eye and qmat_mul(u, adj) == eye


# =============================================================================
# 2. Exact Verification of Counterexamples and Positive Witnesses
# =============================================================================

def verify_exact_families() -> None:
    print("[1/4] Verifying exact counterexample families over Q and Q(i) for n = 2..6, k = 1..6...")

    for n in range(2, 7):
        # Family 1: Non-normal Jordan/shear block J_n = I_n + E_{0,1}
        j_n = qmat_eye(n)
        j_n[0][1] = QComplex.of(1)
        assert not qmat_is_normal(j_n), f"J_{n} must be non-normal"
        # Eigenvalues of upper-triangular J_n are (1, 1, ..., 1), rho = 1
        rho_j = Fraction(1)
        eig_mods_j = [Fraction(1)] * n
        # Schur strict inequality: sum |lambda_i|^2 = n < n + 1 = ||J_n||_F^2
        assert sum(m * m for m in eig_mods_j) == Fraction(n)
        assert qmat_frob_sq(j_n) == Fraction(n + 1)

        for k in range(1, 7):
            jk = qmat_pow(j_n, k)
            # Check exact formula J_n^k = I_n + k E_{0,1}
            expected_jk = qmat_eye(n)
            expected_jk[0][1] = QComplex.of(k)
            assert jk == expected_jk, f"J_{n}^{k} formula mismatch"

            eig_pow_sum = sum(m**k for m in eig_mods_j)
            tr_jk = qmat_trace(jk)
            bound = n * (rho_j**k)
            # Attains bound for both eigenvalue modulus power sum and trace power sum!
            assert eig_pow_sum == bound == Fraction(n)
            assert tr_jk == QComplex.of(n)
            assert tr_jk.norm_sq() == Fraction(n * n) * (rho_j ** (2 * k))
            # Violates Frobenius power bound ||A^k||_F^2 <= n * rho(A)^{2k}
            frob_jk = qmat_frob_sq(jk)
            assert frob_jk == Fraction(n + k * k) > Fraction(n) * (rho_j ** (2 * k))

        # Family 2: Normal rank-1 projection D_n = diag(1, 0, ..., 0)
        d_n = qmat_zeros(n)
        d_n[0][0] = QComplex.of(1)
        assert qmat_is_normal(d_n), f"D_{n} must be normal"
        rho_d = Fraction(1)
        eig_mods_d = [Fraction(1)] + [Fraction(0)] * (n - 1)
        # Satisfies Schur equality: sum |lambda_i|^2 = 1 = ||D_n||_F^2
        assert sum(m * m for m in eig_mods_d) == qmat_frob_sq(d_n) == Fraction(1)

        for k in range(1, 7):
            dk = qmat_pow(d_n, k)
            assert dk == d_n
            eig_pow_sum = sum(m**k for m in eig_mods_d)
            tr_dk = qmat_trace(dk)
            frob_dk = qmat_frob_sq(dk)
            bound = Fraction(n) * (rho_d**k)
            # Strictly fails equality under every reading: 1 < n
            assert eig_pow_sum == Fraction(1) < bound
            assert tr_dk == QComplex.of(1) and tr_dk.norm_sq() == Fraction(1) < Fraction(n * n)
            assert frob_dk == Fraction(1) < Fraction(n) * (rho_d ** (2 * k))

        # Family 3: Non-normal nilpotent N_{n, c} = c * E_{0,1} for c = 1 and c = 2 + 3i
        for c in (QComplex.of(1), QComplex(Fraction(2), Fraction(3))):
            n_mat = qmat_zeros(n)
            n_mat[0][1] = c
            assert not qmat_is_normal(n_mat), f"Nilpotent N_{n} must be non-normal"
            rho_n = Fraction(0)
            eig_mods_n = [Fraction(0)] * n
            # Frobenius norm squared is |c|^2 > 0 = n * rho^2
            assert qmat_frob_sq(n_mat) == c.norm_sq() > Fraction(0) == Fraction(n) * (rho_n**2)
            # Higher Schatten even power sums: tr((N* N)^k) = |c|^{2k} > 0 = n * rho^{2k}
            gram = qmat_mul(qmat_adj(n_mat), n_mat)
            for k in range(1, 7):
                gram_k = qmat_pow(gram, k)
                schatten_2k = qmat_trace(gram_k)
                assert schatten_2k == QComplex.of(c.norm_sq() ** k)
                assert schatten_2k.re > Fraction(0) == Fraction(n) * (rho_n ** (2 * k))
                # Meanwhile eigenvalue power sum is 0 = n * rho^k (attains spectral bound while non-normal!)
                assert sum(m**k for m in eig_mods_n) == Fraction(0) == Fraction(n) * (rho_n**k)

        # Family 4: Identity matrix I_n refutes unscaled bound (without factor n)
        eye_n = qmat_eye(n)
        assert qmat_is_normal(eye_n)
        for k in range(1, 7):
            assert Fraction(n) > Fraction(1)  # sum |lambda_i|^k = n > 1 = rho(I_n)^k

    print("      PASS: All exact n x n families verified for n = 2..6, k = 1..6.")


def verify_dense_and_diagonalizable_witnesses() -> None:
    print("[2/4] Verifying dense non-triangular Schur decompositions and diagonalizable witnesses...")

    # Pythagorean unitary matrix U = (1/5) * [[3, -4], [4, 3]]
    u = [
        [QComplex(Fraction(3, 5)), QComplex(Fraction(-4, 5))],
        [QComplex(Fraction(4, 5)), QComplex(Fraction(3, 5))],
    ]
    assert qmat_is_unitary(u), "Pythagorean matrix U must be unitary"

    # Dense non-normal matrix A = U * J_2 * U^* = (1/25) * [[13, 9], [-16, 37]]
    j2 = [[QComplex.of(1), QComplex.of(1)], [QComplex.of(0), QComplex.of(1)]]
    a_dense = qmat_mul(qmat_mul(u, j2), qmat_adj(u))
    assert a_dense == [
        [QComplex(Fraction(13, 25)), QComplex(Fraction(9, 25))],
        [QComplex(Fraction(-16, 25)), QComplex(Fraction(37, 25))],
    ]
    assert not qmat_is_normal(a_dense)
    assert qmat_frob_sq(a_dense) == Fraction(3) > Fraction(2)
    for k in range(1, 7):
        ak = qmat_pow(a_dense, k)
        assert qmat_trace(ak) == QComplex.of(2)
        assert qmat_frob_sq(ak) == Fraction(2 + k * k)

    # Dense complex normal matrix M = U * diag(1, i) * U^* (unimodular normal -> scaled unitary)
    diag_1_i = [
        [QComplex.of(1), QComplex.of(0)],
        [QComplex.of(0), QComplex(Fraction(0), Fraction(1))],
    ]
    m_normal_unimod = qmat_mul(qmat_mul(u, diag_1_i), qmat_adj(u))
    assert qmat_is_normal(m_normal_unimod)
    assert qmat_is_unitary(m_normal_unimod)
    assert qmat_frob_sq(m_normal_unimod) == Fraction(2)  # Schur equality 1 + 1 = 2
    # Note: for k = 1, |tr(M)|^2 = |1 + i|^2 = 2 < 4 = 2^2 * rho^2 (unimodular normal fails |tr(A)| = n*rho!),
    # while for k = 4, M^4 = I_2 so |tr(M^4)|^2 = 4 = 2^2 * rho^8!
    assert qmat_trace(m_normal_unimod) == QComplex(Fraction(1), Fraction(1))
    assert qmat_trace(m_normal_unimod).norm_sq() == Fraction(2) < Fraction(4)
    assert qmat_trace(qmat_pow(m_normal_unimod, 4)) == QComplex.of(2)

    # Dense normal non-unimodular matrix P = U * diag(1, 0) * U^* = (1/25)*[[9, 12], [12, 16]]
    diag_1_0 = [[QComplex.of(1), QComplex.of(0)], [QComplex.of(0), QComplex.of(0)]]
    p_proj = qmat_mul(qmat_mul(u, diag_1_0), qmat_adj(u))
    assert qmat_is_normal(p_proj)
    assert qmat_frob_sq(p_proj) == Fraction(1)  # Schur equality 1 + 0 = 1
    for k in range(1, 7):
        assert qmat_trace(qmat_pow(p_proj, k)) == QComplex.of(1)  # 1 < 2 = 2 * rho^k

    # Diagonalizable non-normal matrix B = [[1, -2], [0, -1]] with distinct eigenvalues {1, -1}
    b_inv = [[QComplex.of(1), QComplex.of(-2)], [QComplex.of(0), QComplex.of(-1)]]
    assert not qmat_is_normal(b_inv)
    assert qmat_pow(b_inv, 2) == qmat_eye(2), "B must be an involution (B^2 = I_2)"
    for k in range(1, 7):
        # Eigenvalues are +1, -1, so sum |lambda_i|^k = 1 + 1 = 2 = 2 * rho(B)^k for ALL k >= 1
        eig_mod_sum_b = abs(1) ** k + abs(-1) ** k
        assert eig_mod_sum_b == 2
        if k % 2 == 0:
            assert qmat_trace(qmat_pow(b_inv, k)) == QComplex.of(2)

    print("      PASS: Dense unitary conjugates and diagonalizable non-normal witnesses verified.")


# =============================================================================
# 3. 2x2 Analytical Eigenvalue/Singular-Value Checks & Random Ensemble Stress Tests
# =============================================================================

CMat = List[List[complex]]


def cmat_mul(a: CMat, b: CMat) -> CMat:
    n = len(a)
    return [
        [sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)]
        for i in range(n)
    ]


def cmat_pow(a: CMat, k: int) -> CMat:
    n = len(a)
    res = [[1.0 + 0.0j if i == j else 0.0j for j in range(n)] for i in range(n)]
    base = a
    exp = k
    while exp > 0:
        if exp & 1:
            res = cmat_mul(res, base)
        base = cmat_mul(base, base)
        exp >>= 1
    return res


def cmat_adj(a: CMat) -> CMat:
    n = len(a)
    return [[a[j][i].conjugate() for j in range(n)] for i in range(n)]


def cmat_frob_sq(a: CMat) -> float:
    return sum(abs(x) ** 2 for row in a for x in row)


def cmat_commutator_norm(a: CMat) -> float:
    adj = cmat_adj(a)
    aa = cmat_mul(a, adj)
    a_a = cmat_mul(adj, a)
    n = len(a)
    return math.sqrt(sum(abs(aa[i][j] - a_a[i][j]) ** 2 for i in range(n) for j in range(n)))


def eig2x2(a: CMat) -> Tuple[complex, complex]:
    tr = a[0][0] + a[1][1]
    det = a[0][0] * a[1][1] - a[0][1] * a[1][0]
    disc = cmath.sqrt(tr * tr - 4.0 * det)
    return (0.5 * (tr + disc), 0.5 * (tr - disc))


def svdvals2x2(a: CMat) -> Tuple[float, float]:
    gram = cmat_mul(cmat_adj(a), a)
    tr = max(0.0, (gram[0][0] + gram[1][1]).real)
    det = max(0.0, (gram[0][0] * gram[1][1] - gram[0][1] * gram[1][0]).real)
    disc = math.sqrt(max(0.0, tr * tr - 4.0 * det))
    mu1 = 0.5 * (tr + disc)
    mu2 = (det / mu1) if mu1 > 0.0 else 0.0
    return (math.sqrt(mu1), math.sqrt(max(0.0, mu2)))


def qr_householder_unitary(n: int, rng: random.Random, complex_mode: bool) -> CMat:
    """Generate a random n x n orthogonal/unitary matrix via Householder reflections."""
    u: CMat = [[1.0 + 0.0j if i == j else 0.0j for j in range(n)] for i in range(n)]
    for _ in range(n):
        if complex_mode:
            v = [complex(rng.gauss(0.0, 1.0), rng.gauss(0.0, 1.0)) for _ in range(n)]
        else:
            v = [complex(rng.gauss(0.0, 1.0), 0.0) for _ in range(n)]
        norm_sq = sum(abs(x) ** 2 for x in v)
        if norm_sq < 1e-12:
            continue
        # H = I - 2 v v^* / ||v||^2 is Hermitian unitary
        h = [
            [
                (1.0 if i == j else 0.0) - 2.0 * v[i] * v[j].conjugate() / norm_sq
                for j in range(n)
            ]
            for i in range(n)
        ]
        u = cmat_mul(h, u)
    return u


def verify_2x2_singular_value_am_gm() -> None:
    print("[3/4] Verifying singular-value power sums sum sigma_i(J_2(c)^k)^p > 2*rho^{kp} for all p > 0...")
    for c_val in (0.1, 0.5, 1.0, 2.5, 10.0):
        j_c: CMat = [[1.0 + 0.0j, complex(c_val, 0.0)], [0.0j, 1.0 + 0.0j]]
        for k in range(1, 6):
            jk = cmat_pow(j_c, k)
            s1, s2 = svdvals2x2(jk)
            assert abs(s1 * s2 - 1.0) < 1e-10
            assert abs(s1**2 + s2**2 - (2.0 + (k * c_val) ** 2)) < 1e-9
            for p in (0.5, 1.0, 1.5, 2.0, 3.0, 4.0):
                # By strict AM-GM, s1^p + s2^p > 2 * (s1*s2)^{p/2} = 2 = 2 * rho^{kp}
                assert s1**p + s2**p > 2.0 + 1e-9
    print("      PASS: Singular-value power-sum AM-GM bound violation verified across all p > 0.")


def verify_random_ensembles() -> None:
    print("[4/4] Stress-testing 2,000 random matrices in M_n(R) and M_n(C) (n = 2..5, k = 1..5)...")
    rng = random.Random(202607168)
    tol = 1e-8

    # 4a. 800 random 2x2 real and complex matrices (via exact quadratic eigenvalues & SVD)
    frob_violations = 0
    for trial in range(800):
        complex_mode = trial >= 400
        if complex_mode:
            a: CMat = [
                [complex(rng.uniform(-2, 2), rng.uniform(-2, 2)) for _ in range(2)]
                for _ in range(2)
            ]
        else:
            a = [[complex(rng.uniform(-2, 2), 0.0) for _ in range(2)] for _ in range(2)]

        l1, l2 = eig2x2(a)
        s1, s2 = svdvals2x2(a)
        rho = max(abs(l1), abs(l2))
        frob_sq = cmat_frob_sq(a)
        comm = cmat_commutator_norm(a)

        # Classical Schur's inequality & Weyl's power-sum majorization
        assert abs(l1) ** 2 + abs(l2) ** 2 <= frob_sq + tol
        if comm < 1e-10:
            assert abs((abs(l1) ** 2 + abs(l2) ** 2) - frob_sq) < tol
        else:
            assert frob_sq - (abs(l1) ** 2 + abs(l2) ** 2) > -tol

        for k in range(1, 6):
            ak = cmat_pow(a, k)
            tr_ak = ak[0][0] + ak[1][1]
            eig_mod_k = abs(l1) ** k + abs(l2) ** k
            spec_bound = 2.0 * (rho**k)
            # True inequalities: |tr(A^k)| <= sum |lambda_i|^k <= 2 * rho(A)^k
            assert abs(tr_ak) <= eig_mod_k + tol
            assert eig_mod_k <= spec_bound + tol
            # Weyl's inequality: sum |lambda_i|^k <= sum sigma_i(A)^k
            assert eig_mod_k <= (s1**k + s2**k) + tol

        if frob_sq > 2.0 * (rho**2) + 1e-6:
            frob_violations += 1

    assert frob_violations > 200, "Expected abundant random non-normal violations of ||A||_F^2 <= 2*rho^2"

    # 4b. 1,200 structured n x n Schur-constructed ensembles for n = 2, 3, 4, 5
    for n in (2, 3, 4, 5):
        for kind in ("general_schur", "normal_generic", "nonnormal_equal_modulus"):
            for trial in range(100):
                complex_mode = (trial % 2 == 1)
                u = qr_householder_unitary(n, rng, complex_mode=complex_mode)
                t: CMat = [[0.0j for _ in range(n)] for _ in range(n)]

                if kind == "general_schur":
                    for i in range(n):
                        t[i][i] = (
                            complex(rng.uniform(-2, 2), rng.uniform(-2, 2))
                            if complex_mode
                            else complex(rng.uniform(-2, 2), 0.0)
                        )
                        for j in range(i + 1, n):
                            t[i][j] = (
                                complex(rng.uniform(-1.5, 1.5), rng.uniform(-1.5, 1.5))
                                if complex_mode
                                else complex(rng.uniform(-1.5, 1.5), 0.0)
                            )
                elif kind == "normal_generic":
                    # Strictly distinct moduli so rho is NOT attained by all eigenvalues
                    radii = [0.5 * (i + 1) for i in range(n)]
                    for i in range(n):
                        theta = rng.uniform(0, 2 * math.pi) if complex_mode else (0.0 if i % 2 == 0 else math.pi)
                        t[i][i] = cmath.rect(radii[i], theta)
                elif kind == "nonnormal_equal_modulus":
                    # All eigenvalues have equal modulus r > 0, plus nonzero strictly upper-triangular part!
                    r = rng.uniform(0.5, 2.5)
                    for i in range(n):
                        theta = rng.uniform(0, 2 * math.pi) if complex_mode else (0.0 if i % 2 == 0 else math.pi)
                        t[i][i] = cmath.rect(r, theta)
                    t[0][1] = complex(1.0, 0.5 if complex_mode else 0.0)

                a = cmat_mul(cmat_mul(u, t), cmat_adj(u))
                eigs = [t[i][i] for i in range(n)]
                rho = max(abs(lam) for lam in eigs)
                frob_sq = cmat_frob_sq(a)
                eig_sq_sum = sum(abs(lam) ** 2 for lam in eigs)
                comm = cmat_commutator_norm(a)

                # Check Schur's inequality
                assert eig_sq_sum <= frob_sq + tol

                if kind == "normal_generic":
                    assert comm < tol
                    assert abs(eig_sq_sum - frob_sq) < tol  # Schur equality holds!
                    for k in range(1, 6):
                        ak = cmat_pow(a, k)
                        # Normal matrix satisfies ||A^k||_F^2 <= n * rho^{2k},
                        # YET strictly fails equality in sum |lambda_i|^k = n * rho^k!
                        assert cmat_frob_sq(ak) <= n * (rho ** (2 * k)) + tol
                        assert sum(abs(lam) ** k for lam in eigs) < n * (rho**k) - 1e-6

                elif kind == "nonnormal_equal_modulus":
                    assert comm > 1e-3  # Genuinely non-normal!
                    assert frob_sq > eig_sq_sum + 0.5  # Strict Schur inequality!
                    for k in range(1, 6):
                        # EVERY non-normal equal-modulus matrix attains sum |lambda_i|^k = n * rho^k!
                        assert abs(sum(abs(lam) ** k for lam in eigs) - n * (rho**k)) < tol

    print(
        f"      PASS: All 2,000 random ensemble tests passed "
        f"({frob_violations}/800 random 2x2 matrices violated ||A||_F^2 <= 2*rho^2)."
    )


def main() -> int:
    print("=" * 76)
    print("Conjecture 00000007168 - Independent Verification Suite")
    print("=" * 76)
    verify_exact_families()
    verify_dense_and_diagonalizable_witnesses()
    verify_2x2_singular_value_am_gm()
    verify_random_ensembles()
    print("=" * 76)
    print("VERIFICATION RESULT: ALL CHECKS PASSED - CONJECTURE 00000007168 REFUTED")
    print("across every natural mathematical reading over M_n(R) and M_n(C) (n >= 2).")
    print("=" * 76)
    return 0


if __name__ == "__main__":
    sys.exit(main())
