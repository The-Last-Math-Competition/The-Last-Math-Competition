"""
Independent computational verification for Conjecture 00000007173.

Uses only the Python 3.12 standard library (exact rational arithmetic via
fractions.Fraction, exhaustive symmetric-group checks via itertools.permutations,
and a pure-Python Jacobi eigenvalue solver for floating-point stress tests).

Exits with code 0 iff every positive non-vacuity check and every refutation
witness across Readings I, II, and III passes.
"""

from __future__ import annotations

import itertools
import math
import random
import sys
from fractions import Fraction
from typing import Sequence


# ---------------------------------------------------------------------------
# Exact rational linear algebra and majorization utilities
# ---------------------------------------------------------------------------

MatQ = list[list[Fraction]]


def to_mat_q(rows: Sequence[Sequence[int | Fraction]]) -> MatQ:
    return [[Fraction(x) for x in row] for row in rows]


def mat_add(A: MatQ, B: MatQ) -> MatQ:
    n = len(A)
    return [[A[i][j] + B[i][j] for j in range(n)] for i in range(n)]


def mat_mul(A: MatQ, B: MatQ) -> MatQ:
    n = len(A)
    return [
        [sum((A[i][k] * B[k][j] for k in range(n)), Fraction(0)) for j in range(n)]
        for i in range(n)
    ]


def mat_trans(A: MatQ) -> MatQ:
    n = len(A)
    return [[A[j][i] for j in range(n)] for i in range(n)]


def mat_id(n: int) -> MatQ:
    return [
        [Fraction(1 if i == j else 0) for j in range(n)]
        for i in range(n)
    ]


def diag_mat(d: Sequence[int | Fraction]) -> MatQ:
    n = len(d)
    return [
        [Fraction(d[i]) if i == j else Fraction(0) for j in range(n)]
        for i in range(n)
    ]


def diag_vec(A: MatQ) -> list[Fraction]:
    return [A[i][i] for i in range(len(A))]


def is_symm(A: MatQ) -> bool:
    n = len(A)
    return all(A[i][j] == A[j][i] for i in range(n) for j in range(n))


def is_diag(A: MatQ) -> bool:
    n = len(A)
    return all(A[i][j] == 0 for i in range(n) for j in range(n) if i != j)


def perm_matrices(n: int) -> list[MatQ]:
    mats: list[MatQ] = []
    for sigma in itertools.permutations(range(n)):
        P = [
            [Fraction(1 if j == sigma[i] else 0) for j in range(n)]
            for i in range(n)
        ]
        mats.append(P)
    return mats


def is_perm_similar(A: MatQ, B: MatQ) -> bool:
    n = len(A)
    if len(B) != n:
        return False
    for P in perm_matrices(n):
        if mat_mul(mat_mul(P, B), mat_trans(P)) == A:
            return True
    return False


def majorizes_exact(y: Sequence[int | Fraction], x: Sequence[int | Fraction]) -> bool:
    """Exact rational check for x prec y."""
    if len(x) != len(y):
        return False
    xs = sorted((Fraction(v) for v in x), reverse=True)
    ys = sorted((Fraction(v) for v in y), reverse=True)
    if sum(xs, Fraction(0)) != sum(ys, Fraction(0)):
        return False
    sx = Fraction(0)
    sy = Fraction(0)
    for a, b in zip(xs, ys):
        sx += a
        sy += b
        if sx > sy:
            return False
    return True


def strict_majorizes_exact(
    y: Sequence[int | Fraction], x: Sequence[int | Fraction]
) -> bool:
    return majorizes_exact(y, x) and not majorizes_exact(x, y)


def exact_eigvals_2x2(A: MatQ) -> tuple[Fraction, Fraction] | None:
    """Return exact rational ordered eigenvalues (l1 >= l2) if rational, else None."""
    tr = A[0][0] + A[1][1]
    det = A[0][0] * A[1][1] - A[0][1] * A[1][0]
    disc = tr * tr - 4 * det
    if disc < 0:
        return None
    num = disc.numerator
    den = disc.denominator
    s_num = math.isqrt(num)
    s_den = math.isqrt(den)
    if s_num * s_num != num or s_den * s_den != den:
        return None
    rt = Fraction(s_num, s_den)
    return ((tr + rt) / 2, (tr - rt) / 2)


def charpoly_eval_3x3(A: MatQ, lam: Fraction) -> Fraction:
    """Evaluate det(lam * I_3 - A) in exact rational arithmetic."""
    M = [
        [(lam if i == j else Fraction(0)) - A[i][j] for j in range(3)]
        for i in range(3)
    ]
    return (
        M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
        - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
        + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0])
    )


def verify_spectrum_3x3(A: MatQ, spec: tuple[int | Fraction, int | Fraction, int | Fraction]) -> bool:
    l1, l2, l3 = (Fraction(v) for v in spec)
    if not (l1 >= l2 >= l3):
        return False
    tr = A[0][0] + A[1][1] + A[2][2]
    c2 = (
        (A[0][0] * A[1][1] - A[0][1] * A[1][0])
        + (A[0][0] * A[2][2] - A[0][2] * A[2][0])
        + (A[1][1] * A[2][2] - A[1][2] * A[2][1])
    )
    det = -charpoly_eval_3x3(A, Fraction(0))
    return (
        tr == l1 + l2 + l3
        and c2 == l1 * l2 + l1 * l3 + l2 * l3
        and det == l1 * l2 * l3
    )


# ---------------------------------------------------------------------------
# Pure-Python Jacobi symmetric eigensolver for randomized stress checks
# ---------------------------------------------------------------------------

def jacobi_eigvalsh(A: list[list[float]], max_sweeps: int = 80, tol: float = 1e-13) -> list[float]:
    n = len(A)
    M = [row[:] for row in A]
    for _ in range(max_sweeps * n * n):
        p, q, best = 0, 1, 0.0
        for i in range(n):
            for j in range(i + 1, n):
                if abs(M[i][j]) > best:
                    best = abs(M[i][j])
                    p, q = i, j
        if best < tol:
            break
        diff = M[q][q] - M[p][p]
        if abs(diff) < 1e-30:
            t = 1.0
        else:
            tau = diff / (2.0 * M[p][q])
            t = math.copysign(1.0 / (abs(tau) + math.sqrt(1.0 + tau * tau)), tau)
        c = 1.0 / math.sqrt(1.0 + t * t)
        s = t * c
        app = M[p][p] - t * M[p][q]
        aqq = M[q][q] + t * M[p][q]
        M[p][p] = app
        M[q][q] = aqq
        M[p][q] = M[q][p] = 0.0
        for r in range(n):
            if r != p and r != q:
                mrp, mrq = M[r][p], M[r][q]
                M[r][p] = M[p][r] = c * mrp - s * mrq
                M[r][q] = M[q][r] = s * mrp + c * mrq
    return sorted([M[i][i] for i in range(n)], reverse=True)


def majorizes_float(y: Sequence[float], x: Sequence[float], tol: float = 1e-8) -> bool:
    xs = sorted(x, reverse=True)
    ys = sorted(y, reverse=True)
    if abs(sum(xs) - sum(ys)) > tol:
        return False
    sx = sy = 0.0
    for a, b in zip(xs, ys):
        sx += a
        sy += b
        if sx > sy + tol:
            return False
    return True


# ---------------------------------------------------------------------------
# Verification suite
# ---------------------------------------------------------------------------

def check_nonvacuity() -> None:
    print("[1/5] Checking positive non-vacuity theorems...")

    # 1a. Opposite orderings collapse to the same element in the majorization poset
    vec = [Fraction(9), Fraction(4), Fraction(-1), Fraction(-5)]
    for p in itertools.permutations(vec):
        assert majorizes_exact(vec, p) and majorizes_exact(p, vec)
    print("  PASS: Opposite orderings l_down and l_up are majorization-equivalent across S_4.")

    # 1b. Schur Frobenius equality on symmetric matrices with diag(A) a permutation of lambda
    for sigma in itertools.permutations([Fraction(7), Fraction(3), Fraction(-2)]):
        D = diag_mat(sigma)
        assert is_symm(D)
        assert is_perm_similar(D, diag_mat([7, 3, -2]))
    print("  PASS: Symmetric Schur upper-endpoint equality realizes permutation similarity.")

    # 1c. Diagonal Lidskii case realizes both endpoints via P = I_n and P = P_rev
    a_diag = diag_mat([10, 4, 1])
    b_diag = diag_mat([8, 5, 0])
    p_id = mat_id(3)
    p_rev = to_mat_q([[0, 0, 1], [0, 1, 0], [1, 0, 0]])
    sum_up = mat_add(a_diag, mat_mul(mat_mul(p_id, b_diag), mat_trans(p_id)))
    sum_low = mat_add(a_diag, mat_mul(mat_mul(p_rev, b_diag), mat_trans(p_rev)))
    assert verify_spectrum_3x3(sum_up, (18, 9, 1))
    assert verify_spectrum_3x3(sum_low, (10, 9, 9))
    print("  PASS: Already-diagonal Lidskii sum endpoints are realized by permutation similarity.")


def check_reading_i_schur_horn() -> None:
    print("[2/5] Checking Reading I (Schur-Horn diagonal vs. spectrum majorization)...")

    # I-A (2x2): A_+ and A_- at spectrum (2, 0) and lower endpoint (1, 1)
    A_plus = to_mat_q([[1, 1], [1, 1]])
    A_minus = to_mat_q([[1, -1], [-1, 1]])
    D_20 = diag_mat([2, 0])

    assert is_symm(A_plus) and is_symm(A_minus)
    assert exact_eigvals_2x2(A_plus) == (Fraction(2), Fraction(0))
    assert exact_eigvals_2x2(A_minus) == (Fraction(2), Fraction(0))
    assert diag_vec(A_plus) == [Fraction(1), Fraction(1)]
    assert diag_vec(A_minus) == [Fraction(1), Fraction(1)]
    assert strict_majorizes_exact([2, 0], [1, 1])
    assert not is_perm_similar(A_plus, D_20)
    assert not is_perm_similar(A_minus, D_20)
    assert not is_perm_similar(A_plus, A_minus)
    print("  PASS: 2x2 symmetric lower-endpoint witnesses A_+ and A_- refute Reading I-A.")

    # I-A (3x3): J_3 and signed J_3' at spectrum (3, 0, 0) and lower endpoint (1, 1, 1)
    J3 = to_mat_q([[1, 1, 1], [1, 1, 1], [1, 1, 1]])
    J3_signed = to_mat_q([[1, 1, -1], [1, 1, -1], [-1, -1, 1]])
    D_300 = diag_mat([3, 0, 0])
    assert is_symm(J3) and is_symm(J3_signed)
    assert verify_spectrum_3x3(J3, (3, 0, 0))
    assert verify_spectrum_3x3(J3_signed, (3, 0, 0))
    assert diag_vec(J3) == [Fraction(1), Fraction(1), Fraction(1)]
    assert diag_vec(J3_signed) == [Fraction(1), Fraction(1), Fraction(1)]
    assert strict_majorizes_exact([3, 0, 0], [1, 1, 1])
    assert not is_perm_similar(J3, D_300)
    assert not is_perm_similar(J3_signed, D_300)
    assert not is_perm_similar(J3, J3_signed)
    print("  PASS: 3x3 symmetric lower-endpoint witnesses J_3 and J_3' refute Reading I-A.")

    # I-B: Non-Hermitian upper endpoint witnesses B_1 (diagonalizable) and B_2 (Jordan)
    B1 = to_mat_q([[1, 1], [0, 0]])
    B2 = to_mat_q([[1, 1], [0, 1]])
    S = to_mat_q([[1, -1], [0, 1]])
    S_inv = to_mat_q([[1, 1], [0, 1]])
    assert mat_mul(S, S_inv) == mat_id(2)
    assert mat_mul(mat_mul(S, diag_mat([1, 0])), S_inv) == B1
    assert exact_eigvals_2x2(B1) == (Fraction(1), Fraction(0))
    assert diag_vec(B1) == [Fraction(1), Fraction(0)]
    assert not is_perm_similar(B1, diag_mat([1, 0]))
    assert exact_eigvals_2x2(B2) == (Fraction(1), Fraction(1))
    assert diag_vec(B2) == [Fraction(1), Fraction(1)]
    assert not is_perm_similar(B2, diag_mat([1, 1]))

    B3 = to_mat_q([[3, 1, 2], [0, 2, 1], [0, 0, 1]])
    assert verify_spectrum_3x3(B3, (3, 2, 1))
    assert diag_vec(B3) == [Fraction(3), Fraction(2), Fraction(1)]
    assert not is_perm_similar(B3, diag_mat([3, 2, 1]))
    print("  PASS: Upper-triangular witnesses B_1, B_2, B_3 refute Reading I-B without symmetry.")


def check_reading_ii_lidskii() -> None:
    print("[3/5] Checking Reading II (Lidskii-Wielandt eigenvalue sum majorization)...")

    # Exact 2x2 all-integer symmetric counterexample
    A = to_mat_q([[25, 0], [0, 0]])
    B = to_mat_q([[9, 12], [12, 16]])
    U_up = to_mat_q([[Fraction(3, 5), Fraction(4, 5)], [Fraction(-4, 5), Fraction(3, 5)]])
    U_low = to_mat_q([[Fraction(-4, 5), Fraction(3, 5)], [Fraction(3, 5), Fraction(4, 5)]])

    assert is_symm(A) and is_symm(B)
    assert exact_eigvals_2x2(A) == (Fraction(25), Fraction(0))
    assert exact_eigvals_2x2(B) == (Fraction(25), Fraction(0))
    assert mat_mul(U_up, mat_trans(U_up)) == mat_id(2)
    assert mat_mul(U_low, mat_trans(U_low)) == mat_id(2)

    sum_orth_up = mat_add(A, mat_mul(mat_mul(U_up, B), mat_trans(U_up)))
    sum_orth_low = mat_add(A, mat_mul(mat_mul(U_low, B), mat_trans(U_low)))
    assert exact_eigvals_2x2(sum_orth_up) == (Fraction(50), Fraction(0))
    assert exact_eigvals_2x2(sum_orth_low) == (Fraction(25), Fraction(25))

    perm_spectra_2x2 = []
    for P in perm_matrices(2):
        S_perm = mat_add(A, mat_mul(mat_mul(P, B), mat_trans(P)))
        ev = exact_eigvals_2x2(S_perm)
        assert ev is not None
        perm_spectra_2x2.append(ev)
        assert strict_majorizes_exact(ev, [25, 25])
        assert strict_majorizes_exact([50, 0], ev)

    assert sorted(perm_spectra_2x2) == [
        (Fraction(40), Fraction(10)),
        (Fraction(45), Fraction(5)),
    ]
    assert strict_majorizes_exact([45, 5], [40, 10])
    print("  PASS: 2x2 rational-orthogonal vs. permutation-similarity Lidskii check passed.")
    print("        Chain: (25, 25) prec!= (40, 10) prec!= (45, 5) prec!= (50, 0).")

    # Exact 3x3 symmetric counterexample across all 3! = 6 permutation matrices
    A3 = diag_mat([25, 10, 0])
    B3 = to_mat_q([[9, 12, 0], [12, 16, 0], [0, 0, 5]])
    assert verify_spectrum_3x3(A3, (25, 10, 0))
    assert verify_spectrum_3x3(B3, (25, 5, 0))
    # Lidskii upper endpoint: (25+25, 10+5, 0+0) = (50, 15, 0)
    # Lidskii lower endpoint: sortDesc(25+0, 10+5, 0+25) = (25, 25, 15)
    for P in perm_matrices(3):
        S3 = mat_add(A3, mat_mul(mat_mul(P, B3), mat_trans(P)))
        assert not verify_spectrum_3x3(S3, (50, 15, 0))
        assert not verify_spectrum_3x3(S3, (25, 25, 15))
    print("  PASS: Exhaustive 3x3 S_3 check confirms neither Lidskii endpoint is permutation-realized.")


def check_reading_iii_poset_slices() -> None:
    print("[4/5] Checking Reading III (Poset of ordered spectra on fixed-trace and PSD slices)...")

    # Fixed-trace slice over R / Z has no upper endpoint
    for t in range(1, 6):
        assert strict_majorizes_exact([2 + t, -t], [2 + t - 1, -(t - 1)])

    # PSD fixed-trace slice S_{2,2}^+: min = (1, 1), max = (2, 0)
    I2 = mat_id(2)
    A_plus = to_mat_q([[1, 1], [1, 1]])
    D_20 = diag_mat([2, 0])
    assert exact_eigvals_2x2(I2) == (Fraction(1), Fraction(1))
    assert exact_eigvals_2x2(D_20) == (Fraction(2), Fraction(0))
    assert not is_perm_similar(I2, D_20)
    assert not is_perm_similar(A_plus, D_20)
    print("  PASS: Spectral poset slice unboundedness and PSD endpoint checks passed.")


def check_randomized_stress() -> None:
    print("[5/5] Running randomized stress checks (Schur-Horn & Lidskii, n = 2..5)...")
    rng = random.Random(202607173)

    for n in (2, 3, 4, 5):
        for _ in range(100):
            M1 = [[rng.gauss(0.0, 1.0) for _ in range(n)] for _ in range(n)]
            M2 = [[rng.gauss(0.0, 1.0) for _ in range(n)] for _ in range(n)]
            A = [[0.5 * (M1[i][j] + M1[j][i]) for j in range(n)] for i in range(n)]
            B = [[0.5 * (M2[i][j] + M2[j][i]) for j in range(n)] for i in range(n)]
            AB = [[A[i][j] + B[i][j] for j in range(n)] for i in range(n)]

            lam_A = jacobi_eigvalsh(A)
            lam_B = jacobi_eigvalsh(B)
            lam_AB = jacobi_eigvalsh(AB)
            d_A = [A[i][i] for i in range(n)]
            mean_A = [sum(lam_A) / n] * n

            # Schur-Horn bounds: mean_A prec diag(A) prec lam_A
            assert majorizes_float(d_A, mean_A)
            assert majorizes_float(lam_A, d_A)

            # Lidskii bounds: (lam_A_down + lam_B_up)_down prec lam(A+B) prec lam_A_down + lam_B_down
            low_lid = sorted([a + b for a, b in zip(lam_A, reversed(lam_B))], reverse=True)
            up_lid = [a + b for a, b in zip(lam_A, lam_B)]
            assert majorizes_float(lam_AB, low_lid)
            assert majorizes_float(up_lid, lam_AB)

            # For generic non-diagonal B (n <= 4), verify no permutation matrix hits up_lid
            if n <= 4:
                hit_upper = False
                for sigma in itertools.permutations(range(n)):
                    S_p = [
                        [A[i][j] + B[sigma[i]][sigma[j]] for j in range(n)]
                        for i in range(n)
                    ]
                    ev_p = jacobi_eigvalsh(S_p)
                    if max(abs(x - y) for x, y in zip(ev_p, up_lid)) < 1e-6:
                        hit_upper = True
                assert not hit_upper

    print("  PASS: 400 randomized trials across dimensions n = 2, 3, 4, 5 verified.")


def main() -> int:
    print("=" * 72)
    print("Verification Suite for Conjecture 00000007173")
    print("=" * 72)
    check_nonvacuity()
    check_reading_i_schur_horn()
    check_reading_ii_lidskii()
    check_reading_iii_poset_slices()
    check_randomized_stress()
    print("=" * 72)
    print("ALL VERIFICATION CHECKS PASSED (verdict: Conjecture 00000007173 is FALSE).")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    sys.exit(main())
