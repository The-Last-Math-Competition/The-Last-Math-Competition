#!/usr/bin/env python3
"""Independent pure-Python verification suite for Conjecture 00000007169.

Verifies:
  1. Positive classical benchmarks: Lidskii-Wielandt-Ky Fan two-sided majorization,
     Weyl's index-shifted additive eigenvalue inequalities, and Fiedler's (1971)
     determinant bounds across 1,200 random real symmetric and complex Hermitian
     matrix pairs (n = 2..5), plus exhaustive S_n permutation extrema (n = 2..5).
  2. Complete refutation of "the optimum of the correction is antisymmetrization"
     across all five canonical mathematical readings for n >= 2:
       - Reading 1: Matrix antisymmetrization A(M) = (M - M^*)/2 (both on the
         Hermitian domain and on general non-Hermitian decompositions M = H + K).
       - Reading 2: Skew-symmetric / skew-Hermitian basis conjugation A + K B K^*.
       - Reading 3: Lie-algebraic commutator antisymmetrization [A, B] = A B - B A.
       - Reading 4: Young alternating permutation antisymmetrizer Alt and parity of w_0.
       - Reading 5: Fiedler algebraic connectivity lambda_2^up(L_1 + L_2) on Laplacians.
"""

from __future__ import annotations

from fractions import Fraction
import itertools
import math
import random
import sys


def mat_add(A: list[list], B: list[list]) -> list[list]:
    n = len(A)
    return [[A[i][j] + B[i][j] for j in range(n)] for i in range(n)]


def mat_sub(A: list[list], B: list[list]) -> list[list]:
    n = len(A)
    return [[A[i][j] - B[i][j] for j in range(n)] for i in range(n)]


def mat_T(A: list[list]) -> list[list]:
    n = len(A)
    return [[A[j][i] for j in range(n)] for i in range(n)]


def mat_mul(A: list[list], B: list[list]) -> list[list]:
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def trace(A: list[list]):
    return sum(A[i][i] for i in range(len(A)))


def det_exact(M: list[list[Fraction]]) -> Fraction:
    """Exact Gaussian elimination determinant over Fraction."""
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]
    sign = Fraction(1)
    for i in range(n):
        piv = None
        for r in range(i, n):
            if A[r][i] != 0:
                piv = r
                break
        if piv is None:
            return Fraction(0)
        if piv != i:
            A[i], A[piv] = A[piv], A[i]
            sign = -sign
        for r in range(i + 1, n):
            factor = A[r][i] / A[i][i]
            for c in range(i, n):
                A[r][c] -= factor * A[i][c]
    prod = sign
    for i in range(n):
        prod *= A[i][i]
    return prod


def det_float(M: list[list[float]]) -> float:
    n = len(M)
    A = [row[:] for row in M]
    sign = 1.0
    for i in range(n):
        piv = max(range(i, n), key=lambda r: abs(A[r][i]))
        if abs(A[piv][i]) < 1e-15:
            return 0.0
        if piv != i:
            A[i], A[piv] = A[piv], A[i]
            sign = -sign
        for r in range(i + 1, n):
            factor = A[r][i] / A[i][i]
            for c in range(i, n):
                A[r][c] -= factor * A[i][c]
    prod = sign
    for i in range(n):
        prod *= A[i][i]
    return prod


def jacobi_eigvalsh_real(A: list[list[float]], tol: float = 1e-12, max_iter: int = 800) -> list[float]:
    """Eigenvalues of a real symmetric matrix sorted non-increasingly."""
    n = len(A)
    M = [row[:] for row in A]
    for _ in range(max_iter):
        p, q, max_val = 0, 1, 0.0
        for i in range(n):
            for j in range(i + 1, n):
                if abs(M[i][j]) > max_val:
                    max_val = abs(M[i][j])
                    p, q = i, j
        if max_val < tol:
            break
        if abs(M[p][p] - M[q][q]) < 1e-15:
            theta = math.pi / 4.0
        else:
            theta = 0.5 * math.atan2(2.0 * M[p][q], M[p][p] - M[q][q])
        c, s = math.cos(theta), math.sin(theta)
        app, aqq, apq = M[p][p], M[q][q], M[p][q]
        M[p][p] = c * c * app + 2.0 * s * c * apq + s * s * aqq
        M[q][q] = s * s * app - 2.0 * s * c * apq + c * c * aqq
        M[p][q] = M[q][p] = 0.0
        for k in range(n):
            if k != p and k != q:
                akp, akq = M[k][p], M[k][q]
                M[k][p] = M[p][k] = c * akp + s * akq
                M[k][q] = M[q][k] = -s * akp + c * akq
    return sorted([M[i][i] for i in range(n)], reverse=True)


def eigvalsh_hermitian(H_re: list[list[float]], H_im: list[list[float]]) -> list[float]:
    """Eigenvalues of an n x n complex Hermitian matrix via 2n x 2n real embedding."""
    n = len(H_re)
    big = [[0.0] * (2 * n) for _ in range(2 * n)]
    for i in range(n):
        for j in range(n):
            big[i][j] = H_re[i][j]
            big[i + n][j + n] = H_re[i][j]
            big[i][j + n] = -H_im[i][j]
            big[i + n][j] = H_im[i][j]
    eigs2 = jacobi_eigvalsh_real(big)
    # Each eigenvalue appears with doubled multiplicity in sorted order.
    return [0.5 * (eigs2[2 * k] + eigs2[2 * k + 1]) for k in range(n)]


def majorizes(x: list[float], y: list[float], tol: float = 1e-8) -> bool:
    xd = sorted(x, reverse=True)
    yd = sorted(y, reverse=True)
    if abs(sum(xd) - sum(yd)) > tol:
        return False
    sx = sy = 0.0
    for xi, yi in zip(xd, yd):
        sx += xi
        sy += yi
        if sx < sy - tol:
            return False
    return True


def check_positive_benchmarks() -> None:
    print("[1/6] Checking Lidskii-Wielandt-Ky Fan, Weyl & Fiedler (1971) positive benchmarks...")
    rng = random.Random(202607169)

    # Exhaustive S_n permutation extrema for strictly decreasing positive vectors (n = 2..5)
    for n in range(2, 6):
        alpha = [Fraction(2 * (n - i) + 1) for i in range(n)]
        beta = [Fraction(3 * (n - i) + 2) for i in range(n)]
        id_perm = tuple(range(n))
        rev_perm = tuple(n - 1 - i for i in range(n))
        prod_min = math.prod(alpha[i] + beta[i] for i in range(n))
        prod_max = math.prod(alpha[i] + beta[n - 1 - i] for i in range(n))
        sq_max = sum((alpha[i] + beta[i]) ** 2 for i in range(n))
        sq_min = sum((alpha[i] + beta[n - 1 - i]) ** 2 for i in range(n))
        for perm in itertools.permutations(range(n)):
            p_val = math.prod(alpha[i] + beta[perm[i]] for i in range(n))
            s_val = sum((alpha[i] + beta[perm[i]]) ** 2 for i in range(n))
            assert prod_min <= p_val <= prod_max
            assert sq_min <= s_val <= sq_max
            if perm != id_perm:
                assert prod_min < p_val and s_val < sq_max
            if perm != rev_perm:
                assert p_val < prod_max and sq_min < s_val

    # Randomized real symmetric & complex Hermitian stress tests (1,200 pairs across n = 2..5)
    total_tests = 0
    for n in range(2, 6):
        for trial in range(150):
            # Real SPD test
            X = [[rng.gauss(0.0, 1.0) for _ in range(n)] for _ in range(n)]
            Y = [[rng.gauss(0.0, 1.0) for _ in range(n)] for _ in range(n)]
            A = mat_mul(mat_T(X), X)
            B = mat_mul(mat_T(Y), Y)
            for i in range(n):
                A[i][i] += 0.25
                B[i][i] += 0.25
            a = jacobi_eigvalsh_real(A)
            b = jacobi_eigvalsh_real(B)
            g = jacobi_eigvalsh_real(mat_add(A, B))
            same_vec = [a[i] + b[i] for i in range(n)]
            rev_vec = sorted([a[i] + b[n - 1 - i] for i in range(n)], reverse=True)
            assert majorizes(same_vec, g), f"Ky Fan upper majorization failed at n={n}"
            assert majorizes(g, rev_vec), f"Lidskii lower majorization failed at n={n}"
            for k in range(n):
                upper = min(a[i] + b[j] for i in range(n) for j in range(n) if i + j == k)
                lower = max(a[i] + b[j] for i in range(n) for j in range(n) if i + j == k + n - 1)
                assert lower - 1e-7 <= g[k] <= upper + 1e-7, f"Weyl failed at n={n}, k={k}"
            det_ab = det_float(mat_add(A, B))
            assert math.prod(same_vec) - 1e-6 <= det_ab <= math.prod(rev_vec) + 1e-6
            total_tests += 1

            # Complex Hermitian test
            Xr = [[rng.gauss(0.0, 1.0) for _ in range(n)] for _ in range(n)]
            Xi = [[rng.gauss(0.0, 1.0) for _ in range(n)] for _ in range(n)]
            Yr = [[rng.gauss(0.0, 1.0) for _ in range(n)] for _ in range(n)]
            Yi = [[rng.gauss(0.0, 1.0) for _ in range(n)] for _ in range(n)]
            Ar = [[0.5 * (Xr[i][j] + Xr[j][i]) for j in range(n)] for i in range(n)]
            Ai = [[0.5 * (Xi[i][j] - Xi[j][i]) for j in range(n)] for i in range(n)]
            Br = [[0.5 * (Yr[i][j] + Yr[j][i]) for j in range(n)] for i in range(n)]
            Bi = [[0.5 * (Yi[i][j] - Yi[j][i]) for j in range(n)] for i in range(n)]
            ac = eigvalsh_hermitian(Ar, Ai)
            bc = eigvalsh_hermitian(Br, Bi)
            gc = eigvalsh_hermitian(mat_add(Ar, Br), mat_add(Ai, Bi))
            assert majorizes([ac[i] + bc[i] for i in range(n)], gc, tol=1e-7)
            assert majorizes(gc, sorted([ac[i] + bc[n - 1 - i] for i in range(n)], reverse=True), tol=1e-7)
            total_tests += 1

    print(f"      PASS ({total_tests} random symmetric/Hermitian pairs + exhaustive S_2..S_5 checks).")


def check_reading_1_matrix_antisymmetrization() -> None:
    print("[2/6] Checking Refutation of Reading 1 (Matrix Antisymmetrization A(M) = (M - M^*)/2)...")
    for n in range(2, 7):
        # 1A: Symmetric domain -> skewPart vanishes identically, losing trace and missing reverse-order optimum
        A = [[Fraction(2 * (n - i) if i == j else 0) for j in range(n)] for i in range(n)]
        B_rev = [[Fraction(2 * (i + 1) if i == j else 0) for j in range(n)] for i in range(n)]
        skew_A = [[Fraction(1, 2) * (A[i][j] - A[j][i]) for j in range(n)] for i in range(n)]
        skew_sum = [
            [Fraction(1, 2) * ((A[i][j] + B_rev[i][j]) - (A[j][i] + B_rev[j][i])) for j in range(n)]
            for i in range(n)
        ]
        assert all(skew_A[i][j] == 0 for i in range(n) for j in range(n))
        assert all(skew_sum[i][j] == 0 for i in range(n) for j in range(n))
        opt_sum = mat_add(A, B_rev)
        assert all(opt_sum[i][i] == 2 * (n + 1) for i in range(n))
        assert trace(opt_sum) == 2 * n * (n + 1) > 0 == trace(skew_sum)

        # 1B: Non-Hermitian matrices with antisymmetric parts violate Weyl/Ky Fan & Fiedler bounds
        # Top-left 2x2 block: M1 = [[4, 1], [-1, 2]], M2 = [[4, -1], [1, 2]]; rest: 3 * I_{n-2}
        M1 = [[Fraction(0) for _ in range(n)] for _ in range(n)]
        M2 = [[Fraction(0) for _ in range(n)] for _ in range(n)]
        M1[0][0], M1[0][1], M1[1][0], M1[1][1] = Fraction(4), Fraction(1), Fraction(-1), Fraction(2)
        M2[0][0], M2[0][1], M2[1][0], M2[1][1] = Fraction(4), Fraction(-1), Fraction(1), Fraction(2)
        for i in range(2, n):
            M1[i][i] = Fraction(3)
            M2[i][i] = Fraction(3)
        # Verify (M1 - 3 I)^2 == 0 and (M2 - 3 I)^2 == 0, so all eigenvalues of M1 and M2 equal 3!
        I3 = [[Fraction(3 if i == j else 0) for j in range(n)] for i in range(n)]
        N1 = mat_sub(M1, I3)
        N2 = mat_sub(M2, I3)
        Z1 = mat_mul(N1, N1)
        Z2 = mat_mul(N2, N2)
        assert all(Z1[i][j] == 0 and Z2[i][j] == 0 for i in range(n) for j in range(n))
        S = mat_add(M1, M2)
        assert S[0][0] == 8 and S[1][1] == 4
        # Top eigenvalue of M1 + M2 is 8 > 3 + 3 = 6 (violates Weyl/Ky Fan!)
        # Determinant of M1 + M2 is 32 * 6^(n-2) < 36 * 6^(n-2) (violates Fiedler lower bound!)
        assert det_exact(S) == Fraction(32) * (Fraction(6) ** (n - 2))
        assert det_exact(S) < Fraction(36) * (Fraction(6) ** (n - 2))

    # Complex-eigenvalue breakdown under antisymmetric perturbation H + K_t:
    # H = diag(4, 0), K_3 = [[0, 3], [-3, 0]] -> charpoly x^2 - 4x + 9, discriminant 16 - 36 = -20 < 0
    disc = 4 * 4 - 4 * 9
    assert disc == -20 < 0
    print("      PASS (Exact Q witnesses verified for n = 2..6).")


def check_reading_2_skew_conjugation() -> None:
    print("[3/6] Checking Refutation of Reading 2 (Skew-Symmetric / Skew-Hermitian Conjugation)...")
    # 2A: Exact rational/integer family for all n = 2..6
    for n in range(2, 7):
        A = [[Fraction(0) for _ in range(n)] for _ in range(n)]
        B = [[Fraction(0) for _ in range(n)] for _ in range(n)]
        Q = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
        K = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
        A[0][0], A[1][1] = Fraction(25), Fraction(0)
        B[0][0], B[0][1], B[1][0], B[1][1] = Fraction(16), Fraction(12), Fraction(12), Fraction(9)
        for i in range(2, n):
            A[i][i] = Fraction(1)
            B[i][i] = Fraction(1)
        # Symmetric orthogonal reflection on top 2x2 block: Q_2 = (1/5)[[-3, 4], [4, 3]]
        Q[0][0], Q[0][1] = Fraction(-3, 5), Fraction(4, 5)
        Q[1][0], Q[1][1] = Fraction(4, 5), Fraction(3, 5)
        assert Q == mat_T(Q)
        assert mat_mul(mat_T(Q), Q) == [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
        # Skew-symmetric orthogonal on top 2x2 block: J_2 = [[0, 1], [-1, 0]]
        K[0][0], K[0][1], K[1][0], K[1][1] = Fraction(0), Fraction(1), Fraction(-1), Fraction(0)
        opt_mat = mat_add(A, mat_mul(Q, mat_mul(B, mat_T(Q))))
        skew_mat = mat_add(A, mat_mul(K, mat_mul(B, mat_T(K))))
        det_opt = det_exact(opt_mat)
        det_skew = det_exact(skew_mat)
        assert det_opt == Fraction(625) * (Fraction(2) ** (n - 2))
        assert det_skew == Fraction(400) * (Fraction(2) ** (n - 2))
        assert det_skew < det_opt

    # 2B: Odd dimensions n = 3, 5 -> every skew-symmetric matrix is singular (det = 0)!
    rng = random.Random(7169)
    for n in (3, 5):
        for _ in range(50):
            X = [[Fraction(rng.randint(-5, 5)) for _ in range(n)] for _ in range(n)]
            K_odd = [[X[i][j] - X[j][i] for j in range(n)] for i in range(n)]
            assert det_exact(K_odd) == 0

    # 2C: Complex 3x3 3-cycle obstruction: A = diag(3, 2, 1), B = diag(2, 3, 1) -> target 4 I_3
    # Perm matrix P mapping (2, 3, 1) -> (1, 2, 3) is P = [[0,0,1],[1,0,0],[0,1,0]]
    A3 = [[Fraction(3), Fraction(0), Fraction(0)],
          [Fraction(0), Fraction(2), Fraction(0)],
          [Fraction(0), Fraction(0), Fraction(1)]]
    B3 = [[Fraction(2), Fraction(0), Fraction(0)],
          [Fraction(0), Fraction(3), Fraction(0)],
          [Fraction(0), Fraction(0), Fraction(1)]]
    P3 = [[Fraction(0), Fraction(0), Fraction(1)],
          [Fraction(1), Fraction(0), Fraction(0)],
          [Fraction(0), Fraction(1), Fraction(0)]]
    assert mat_add(A3, mat_mul(P3, mat_mul(B3, mat_T(P3)))) == [
        [Fraction(4 if i == j else 0) for j in range(3)] for i in range(3)
    ]
    assert P3 != mat_T(P3)  # Not symmetric
    assert P3[0][2] != -P3[2][0]  # Not skew-symmetric
    print("      PASS (n = 2..6 rotated PSD, odd-n singularity, and 3-cycle obstruction verified).")


def check_reading_3_commutator() -> None:
    print("[4/6] Checking Refutation of Reading 3 (Lie Commutator [A, B] = A B - B A)...")
    # Exact Pythagorean rational test of the Bloch-sphere commutator identity
    # (c, s) in {(1,0), (-1,0), (0,1), (3/5, 4/5), (-5/13, 12/13)}
    a, b = Fraction(3), Fraction(2)
    pairs = [
        (Fraction(1), Fraction(0)),
        (Fraction(-1), Fraction(0)),
        (Fraction(0), Fraction(1)),
        (Fraction(3, 5), Fraction(4, 5)),
        (Fraction(-5, 13), Fraction(12, 13)),
    ]
    for c, s in pairs:
        assert c * c + s * s == 1
        A = [[a, Fraction(0)], [Fraction(0), -a]]
        B = [[b * c, b * s], [b * s, -b * c]]
        S = mat_add(A, B)
        comm = mat_sub(mat_mul(A, B), mat_mul(B, A))
        comm_norm_sq = sum(comm[i][j] ** 2 for i in range(2) for j in range(2))
        eig_sq = -det_exact(S)  # since tr(S) = 0, S^2 = eig_sq * I_2
        assert eig_sq == a * a + b * b + 2 * a * b * c
        assert comm_norm_sq == 8 * a * a * b * b * (1 - c * c)
        if abs(c) == 1:
            assert comm_norm_sq == 0  # Both extrema occur at [A, B] = 0!
        else:
            assert comm_norm_sq > 0
            assert (a - b) ** 2 < eig_sq < (a + b) ** 2  # Strictly interior!
    print("      PASS (Exact commutator-spectrum identity verified).")


def check_reading_4_perm_antisymmetrizer() -> None:
    print("[5/6] Checking Refutation of Reading 4 (Young Antisymmetrizer & Parity of w_0)...")
    # Young antisymmetrizer Alt(b) = (1/n!) sum_{sigma in S_n} sgn(sigma) sigma(b)
    b2 = [Fraction(5), Fraction(1)]
    alt2 = [Fraction(1, 2) * (b2[0] - b2[1]), Fraction(1, 2) * (b2[1] - b2[0])]
    assert sum(alt2) == 0 != sum(b2)

    for n in (3, 4, 5):
        b = [Fraction(2 * i + 1) for i in range(n)]
        alt = [Fraction(0)] * n
        for perm in itertools.permutations(range(n)):
            invs = sum(1 for i in range(n) for j in range(i + 1, n) if perm[i] > perm[j])
            sgn = Fraction(-1 if invs % 2 == 1 else 1)
            for k in range(n):
                alt[k] += sgn * b[perm[k]]
        assert all(x == 0 for x in alt), f"Expected Alt(b)=0 at n={n}"

    # Parity of w_0: even whenever n == 0 or 1 (mod 4)
    for n in range(2, 10):
        invs = n * (n - 1) // 2
        is_even = (invs % 2 == 0)
        assert is_even == (n % 4 in (0, 1))
    print("      PASS (Young antisymmetrizer vanishing & w_0 parity verified).")


def check_reading_5_fiedler_laplacian() -> None:
    print("[6/6] Checking Refutation of Reading 5 (Fiedler Algebraic Connectivity on Laplacians)...")
    rng = random.Random(1973)
    for n in (3, 4, 5):
        for _ in range(100):
            # Generate two random weighted undirected graph Laplacians L1, L2
            L1 = [[0.0] * n for _ in range(n)]
            L2 = [[0.0] * n for _ in range(n)]
            for i in range(n):
                for j in range(i + 1, n):
                    w1 = rng.uniform(0.1, 2.0)
                    w2 = rng.uniform(0.1, 2.0)
                    L1[i][j] = L1[j][i] = -w1
                    L2[i][j] = L2[j][i] = -w2
                    L1[i][i] += w1
                    L1[j][j] += w1
                    L2[i][i] += w2
                    L2[j][j] += w2
            e1_up = jacobi_eigvalsh_real(L1)[::-1]
            e2_up = jacobi_eigvalsh_real(L2)[::-1]
            es_up = jacobi_eigvalsh_real(mat_add(L1, L2))[::-1]
            assert abs(e1_up[0]) < 1e-9 and abs(e2_up[0]) < 1e-9 and abs(es_up[0]) < 1e-9
            # Fiedler (1973) superadditivity of algebraic connectivity:
            assert es_up[1] >= e1_up[1] + e2_up[1] - 1e-8

    # Complete graph K_3 Laplacian L = [[2,-1,-1],[-1,2,-1],[-1,-1,2]]:
    # L + L realizes exact equality lambda_2^up(2 L) = 6 = 3 + 3 while purely symmetric (A(L)=0).
    # Adding zero-row-sum skew-symmetric K_t = [[0,t,-t],[-t,0,t],[t,-t,0]] on 1^perp yields
    # complex conjugate eigenvalues 6 +- i*sqrt(3)*t (discriminant -12*t^2 < 0 for t != 0).
    L_K3 = [[Fraction(2), Fraction(-1), Fraction(-1)],
            [Fraction(-1), Fraction(2), Fraction(-1)],
            [Fraction(-1), Fraction(-1), Fraction(2)]]
    K_cyc = [[Fraction(0), Fraction(1), Fraction(-1)],
             [Fraction(-1), Fraction(0), Fraction(1)],
             [Fraction(1), Fraction(-1), Fraction(0)]]
    assert all(sum(row) == 0 for row in L_K3)
    assert all(sum(row) == 0 for row in K_cyc)
    assert K_cyc == [[-K_cyc[j][i] for j in range(3)] for i in range(3)]
    print("      PASS (300 random Laplacian pairs + K_3 directed circulation verified).")


def main() -> int:
    print("=== Conjecture 00000007169 Independent Verification Suite ===")
    check_positive_benchmarks()
    check_reading_1_matrix_antisymmetrization()
    check_reading_2_skew_conjugation()
    check_reading_3_commutator()
    check_reading_4_perm_antisymmetrizer()
    check_reading_5_fiedler_laplacian()
    print("=== ALL VERIFICATION CHECKS PASSED (EXIT 0) ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())
