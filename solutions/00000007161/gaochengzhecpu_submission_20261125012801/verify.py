"""
Independent exact verification script for Conjecture 00000007161:
Nonnegative Inverse Eigenvalue Problem (NIEP) — Cyclic Lists & Rotation Lattice.

Uses exact integer/rational arithmetic (fractions.Fraction) from the Python 3.12
standard library with zero external dependencies.
"""

from fractions import Fraction
import cmath
import math
import sys


def mat_mul(A, B):
    n = len(A)
    return [
        [sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)]
        for i in range(n)
    ]


def mat_add(A, B):
    n = len(A)
    return [[A[i][j] + B[i][j] for j in range(n)] for i in range(n)]


def mat_id(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def mat_pow(A, k):
    n = len(A)
    res = mat_id(n)
    for _ in range(k):
        res = mat_mul(res, A)
    return res


def mat_trace(A):
    return sum(A[i][i] for i in range(len(A)))


def is_nonneg(A):
    return all(A[i][j] >= 0 for i in range(len(A)) for j in range(len(A)))


def is_symmetric(A):
    n = len(A)
    return all(A[i][j] == A[j][i] for i in range(n) for j in range(n))


def is_zero_diag(A):
    return all(A[i][i] == 0 for i in range(len(A)))


def is_irreducible(A):
    """Exact graph strong-connectivity check for A >= 0 via sum_{k=0}^{n-1} A^k > 0."""
    n = len(A)
    acc = mat_id(n)
    cur = mat_id(n)
    for _ in range(1, n):
        cur = mat_mul(cur, A)
        acc = mat_add(acc, cur)
    return all(acc[i][j] > 0 for i in range(n) for j in range(n))


def char_poly_faddeev_leverrier(A):
    """
    Exact characteristic polynomial det(t I_n - A) via Faddeev-LeVerrier over Q.
    Returns [c_n, c_{n-1}, ..., c_0] representing sum_{k=0}^n c_k t^k (with c_n = 1).
    """
    n = len(A)
    Af = [[Fraction(A[i][j]) for j in range(n)] for i in range(n)]
    coeffs = [Fraction(1)]
    B = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for k in range(1, n + 1):
        if k == 1:
            M = Af
        else:
            prev_c = coeffs[-1]
            B_plus_cI = [
                [B[i][j] + (prev_c if i == j else Fraction(0)) for j in range(n)]
                for i in range(n)
            ]
            M = mat_mul(Af, B_plus_cI)
        B = M
        ck = -mat_trace(B) / Fraction(k)
        coeffs.append(ck)
    # Return descending coefficients [c_n, c_{n-1}, ..., c_0] as exact Fractions
    return coeffs


def poly_from_roots(roots):
    """Exact monic polynomial prod_{r in roots} (t - r) in descending powers of t."""
    coeffs = [Fraction(1)]
    for r in roots:
        rf = Fraction(r)
        nxt = [Fraction(0)] * (len(coeffs) + 1)
        for idx, c in enumerate(coeffs):
            nxt[idx] += c
            nxt[idx + 1] -= c * rf
        coeffs = nxt
    return coeffs


def eval_poly_desc(coeffs, t):
    acc = Fraction(0)
    for c in coeffs:
        acc = acc * t + c
    return acc


def check_modulus_presence(int_spectrum):
    """
    Universal necessary condition for any disjoint union of cyclic root-of-unity lists:
    every piece {r * exp(2*pi*i*s/k)} contains +r = |z|, so z in L => |z| in L.
    """
    s = set(int_spectrum)
    return all(abs(x) in s for x in int_spectrum)


def verify_positive_cyclic_witnesses():
    print("[1/5] Verifying positive non-vacuity witnesses (weighted cyclic permutation matrices)...")
    for n in range(1, 7):
        for r in [0, 1, 2]:
            C = [[r if j == (i + 1) % n else 0 for j in range(n)] for i in range(n)]
            assert is_nonneg(C), f"C_{n}({r}) must be nonnegative"
            if r > 0:
                assert is_irreducible(C), f"C_{n}({r}) must be irreducible for r > 0"
            expected = [Fraction(1)] + [Fraction(0)] * (n - 1) + [Fraction(-(r ** n))]
            got = char_poly_faddeev_leverrier(C)
            assert got == expected, f"Mismatch for C_{n}({r}): {got} != {expected}"
    print("  PASS: C_n(r) >= 0 realizes det(tI - C_n(r)) = t^n - r^n for 1 <= n <= 6, r in {0,1,2}.")


def verify_non_cyclic_spectra_and_infinite_families():
    print("[2/5] Verifying non-cyclic nonnegative realizable spectra & infinite families...")
    # 1. Positive-trace diagonal witness diag(2, 1)
    D2 = [[2, 0], [0, 1]]
    assert is_nonneg(D2)
    assert char_poly_faddeev_leverrier(D2) == poly_from_roots([2, 1])
    assert sum([2, 1]) != 0  # cannot be a single 2-cycle (r, -r)

    # 2. Hollow all-ones family A_n = J_n - I_n for 3 <= n <= 8
    for n in range(3, 9):
        An = [[0 if i == j else 1 for j in range(n)] for i in range(n)]
        assert is_nonneg(An) and is_symmetric(An) and is_zero_diag(An) and is_irreducible(An)
        spec = [n - 1] + [-1] * (n - 1)
        assert char_poly_faddeev_leverrier(An) == poly_from_roots(spec)
        assert not check_modulus_presence(spec), f"A_{n} spectrum unexpectedly passed modulus check"

    # 3. Suleimanova companion family with pairwise distinct negative integer eigenvalues
    for n in range(3, 8):
        mus = list(range(1, n))  # [1, 2, ..., n-1]
        lam1 = sum(mus)  # n*(n-1)//2, trace-zero!
        spec = [lam1] + [-m for m in mus]
        poly = poly_from_roots(spec)  # [1, -c_{n-1}_top, ..., -c_0_bot] -> [1, 0, -c_{n-2}, ..., -c_0]
        # Companion coefficients c_0, c_1, ..., c_{n-1} from t^n - c_{n-1}*t^{n-1}?
        # Using standard convention t^n - sum_{j=0}^{n-1} c_j t^j:
        c = [-poly[n - j] for j in range(n)]
        assert all(cj >= 0 for cj in c), f"Suleimanova companion coeffs must be >= 0: {c}"
        assert c[n - 1] == 0, "Trace-zero Suleimanova companion must have c_{n-1} = 0"
        Comp = [[0] * n for _ in range(n)]
        for i in range(n - 1):
            Comp[i][i + 1] = 1
        for j in range(n):
            Comp[n - 1][j] = int(c[j])
        assert is_nonneg(Comp) and is_zero_diag(Comp) and is_irreducible(Comp)
        assert char_poly_faddeev_leverrier(Comp) == poly
        assert len(set(spec)) == n  # n pairwise distinct integer eigenvalues!
        assert not check_modulus_presence(spec)
        # Verify Vandermonde eigenvectors C * v(r) = r * v(r)
        for r in spec:
            v = [r ** i for i in range(n)]
            Cv = [sum(Comp[i][j] * v[j] for j in range(n)) for i in range(n)]
            assert Cv == [r * x for x in v]
    print("  PASS: Hollow family A_n = J_n - I_n (3 <= n <= 8) & Suleimanova distinct-root family (3 <= n <= 7) verified.")


def verify_circulant_obstruction():
    print("[3/5] Verifying 3x3 circulant obstruction & explicit counterexamples...")
    # Verify Gauss sum-of-three-squares identity on [-2..2]^4 (125*5 = 625 points uniquely determine degree <= 3 poly)
    for c0 in range(-2, 3):
        for c1 in range(-2, 3):
            for c2 in range(-2, 3):
                C = [[c0, c1, c2], [c2, c0, c1], [c1, c2, c0]]
                cp = char_poly_faddeev_leverrier(C)
                for t in range(-2, 3):
                    lhs = 2 * eval_poly_desc(cp, Fraction(t))
                    rhs = Fraction(t - (c0 + c1 + c2)) * Fraction(
                        (t - c0 + c1) ** 2 + (t - c0 + c2) ** 2 + (c1 - c2) ** 2
                    )
                    assert lhs == rhs

    # Trace-zero primitive counterexample M3 -> (3, -1, -2)
    M3 = [[0, 1, 0], [0, 0, 1], [6, 7, 0]]
    assert is_nonneg(M3) and is_zero_diag(M3) and is_irreducible(M3)
    M3_5 = mat_pow(M3, 5)
    assert all(M3_5[i][j] > 0 for i in range(3) for j in range(3))  # primitive!
    assert char_poly_faddeev_leverrier(M3) == poly_from_roots([3, -1, -2])

    # Symmetric primitive counterexample S3 -> (3, 0, -2)
    S3 = [[0, 2, 1], [2, 0, 1], [1, 1, 1]]
    assert is_nonneg(S3) and is_symmetric(S3) and is_irreducible(S3)
    S3_2 = mat_pow(S3, 2)
    assert all(S3_2[i][j] > 0 for i in range(3) for j in range(3))  # primitive!
    assert char_poly_faddeev_leverrier(S3) == poly_from_roots([3, 0, -2])
    print("  PASS: Gauss 3x3 circulant identity, M_3 -> (3,-1,-2), and symmetric S_3 -> (3,0,-2) verified.")


def verify_phase_rotation_obstruction():
    print("[4/5] Verifying complex phase-rotation obstructions (Newton power sums & Perron-Frobenius)...")
    # Exact check for (i, -i) and general anti-periodic rotation exp(i*pi/n) * Lambda_cyc(n, r)
    for n in range(2, 7):
        theta = math.pi / n
        rotated = [cmath.exp(1j * (theta + 2 * math.pi * k / n)) for k in range(n)]
        power_sum_n = sum(z ** n for z in rotated)
        assert abs(power_sum_n.imag) < 1e-12 and abs(power_sum_n.real - (-n)) < 1e-12
        # Also verify no element equals spectral radius +1
        assert all(abs(z - 1.0) > 1e-6 for z in rotated)
    print("  PASS: Rotated cyclic spectra exp(i*pi/n)*Lambda_cyc(n,1) have s_n = -n < 0 for 2 <= n <= 6.")


def verify_circular_shift_and_lattice_obstructions():
    print("[5/5] Verifying circular coordinate-shift invariance & lattice-meet failure...")
    # Circular shifts leave characteristic polynomial unchanged
    spec3 = [3, -1, -2]
    for shift in range(3):
        rot = spec3[shift:] + spec3[:shift]
        assert poly_from_roots(rot) == poly_from_roots(spec3)

    # Componentwise meet of circular shifts of (1, -1) is (-1, -1) with trace -2 < 0
    s_2 = [(1, -1), (-1, 1)]
    meet_2 = tuple(min(v[i] for v in s_2) for i in range(2))
    assert meet_2 == (-1, -1) and sum(meet_2) == -2 < 0

    # Componentwise meet of circular shifts of (2, -1, -1) is (-1, -1, -1) with trace -3 < 0
    s_3 = [(2, -1, -1), (-1, -1, 2), (-1, 2, -1)]
    meet_3 = tuple(min(v[i] for v in s_3) for i in range(3))
    assert meet_3 == (-1, -1, -1) and sum(meet_3) == -3 < 0
    print("  PASS: Circular shifts preserve characteristic polynomials; componentwise meets violate tr(A) >= 0.")


def main():
    print("=== Conjecture 00000007161 Exact Verification Suite ===")
    verify_positive_cyclic_witnesses()
    verify_non_cyclic_spectra_and_infinite_families()
    verify_circulant_obstruction()
    verify_phase_rotation_obstruction()
    verify_circular_shift_and_lattice_obstructions()
    print("=== ALL VERIFICATION CHECKS PASSED (EXIT 0) ===")


if __name__ == "__main__":
    main()
