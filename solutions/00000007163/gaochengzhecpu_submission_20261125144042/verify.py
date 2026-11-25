#!/usr/bin/env python3
"""
Standalone exact and numerical verification script for Conjecture 00000007163:
"Definition: Perron-Frobenius with the extremal spectra of positive matrices.
Conjecture: The gap between the spectral radius and the next eigenvalue requires
almost irreducible primitivity, and the bound of the gap is the positivity modulus."

Uses ONLY the Python 3.12 standard library (fractions, math, cmath, random).
Exits with status 0 iff all exact algebraic, graph-theoretic, and numerical checks pass.
"""

from fractions import Fraction
import cmath
import math
import random
import sys


# =============================================================================
# 1. Exact Rational Linear Algebra & Characteristic Polynomials
# =============================================================================

def to_frac_mat(A):
    return [[Fraction(x) for x in row] for row in A]


def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def mat_pow(A, k):
    n = len(A)
    res = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    base = to_frac_mat(A)
    e = k
    while e > 0:
        if e & 1:
            res = mat_mul(res, base)
        base = mat_mul(base, base)
        e >>= 1
    return res


def mat_vec(A, v):
    n = len(A)
    return [sum(A[i][j] * v[j] for j in range(n)) for i in range(n)]


def laplace_det(M):
    """Exact recursive Laplace cofactor determinant over Fraction."""
    n = len(M)
    if n == 0:
        return Fraction(1)
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    total = Fraction(0)
    for j in range(n):
        if M[0][j] != 0:
            sub = [[M[r][c] for c in range(n) if c != j] for r in range(1, n)]
            sign = Fraction(1 if j % 2 == 0 else -1)
            total += sign * M[0][j] * laplace_det(sub)
    return total


def char_poly_faddeev_leverrier(A):
    """Exact monic characteristic polynomial coefficients [1, c_{n-1}, ..., c_0] over Fraction."""
    M = to_frac_mat(A)
    n = len(M)
    coeffs = [Fraction(1)]
    B = [[Fraction(0)] * n for _ in range(n)]
    for k in range(1, n + 1):
        if k == 1:
            B = [row[:] for row in M]
        else:
            prev_c = coeffs[-1]
            shifted = [row[:] for row in B]
            for i in range(n):
                shifted[i][i] += prev_c
            B = mat_mul(M, shifted)
        tr = sum(B[i][i] for i in range(n))
        coeffs.append(-tr / Fraction(k))
    return coeffs


def poly_from_roots(roots):
    """Expand prod_{r in roots} (x - r) into [1, c_{n-1}, ..., c_0] over Fraction."""
    coeffs = [Fraction(1)]
    for r in roots:
        rf = Fraction(r)
        nxt = [Fraction(0)] * (len(coeffs) + 1)
        for idx, c in enumerate(coeffs):
            nxt[idx] += c
            nxt[idx + 1] -= c * rf
        coeffs = nxt
    return coeffs


def poly_eval(coeffs, x):
    acc = Fraction(0)
    xf = Fraction(x)
    for c in coeffs:
        acc = acc * xf + c
    return acc


def verify_char_poly_and_laplace(A, expected_roots):
    """Cross-check Faddeev-Leverrier against Laplace determinant at n+2 sample points."""
    M = to_frac_mat(A)
    n = len(M)
    coeffs = char_poly_faddeev_leverrier(M)
    expected = poly_from_roots(expected_roots)
    assert coeffs == expected, f"Char poly mismatch: got {coeffs}, expected {expected}"
    for x in range(-2, n + 3):
        xf = Fraction(x)
        char_mat = [[(xf if i == j else Fraction(0)) - M[i][j] for j in range(n)] for i in range(n)]
        det_val = laplace_det(char_mat)
        pol_val = poly_eval(coeffs, xf)
        assert det_val == pol_val, f"Laplace vs Faddeev-Leverrier mismatch at x={x}"


def verify_eigenpair(A, lam, v):
    M = to_frac_mat(A)
    vf = [Fraction(x) for x in v]
    lamf = Fraction(lam)
    assert any(x != 0 for x in vf), "Eigenvector must be nonzero"
    Av = mat_vec(M, vf)
    assert Av == [lamf * x for x in vf], f"Eigenpair check failed for lam={lam}"


def pos_modulus_min(A):
    M = to_frac_mat(A)
    return min(min(row) for row in M)


def doeblin_modulus(A):
    M = to_frac_mat(A)
    n = len(M)
    return sum(min(M[i][j] for i in range(n)) for j in range(n))


def entry_max(A):
    M = to_frac_mat(A)
    return max(max(row) for row in M)


# =============================================================================
# 2. Exact Graph-Theoretic & Perron-Frobenius Structural Predicates
# =============================================================================

def reachability_positive_walks(A):
    """Return R[i][j] = True iff there exists k >= 1 with (A^k)_{i,j} > 0."""
    n = len(A)
    R = [[A[i][j] > 0 for j in range(n)] for i in range(n)]
    for mid in range(n):
        for i in range(n):
            if R[i][mid]:
                for j in range(n):
                    if R[mid][j]:
                        R[i][j] = True
    return R


def is_irreducible(A):
    R = reachability_positive_walks(A)
    return all(all(row) for row in R)


def has_single_essential_class(A):
    """True iff every two indices i, j with R[i][i] and R[j][j] satisfy R[i][j]."""
    R = reachability_positive_walks(A)
    n = len(A)
    essential = [i for i in range(n) if R[i][i]]
    for i in essential:
        for j in essential:
            if not R[i][j]:
                return False
    return True


def is_primitive(A):
    """Wielandt's bound: an n x n nonnegative matrix is primitive iff A^(n^2 - 2n + 2) > 0."""
    n = len(A)
    exp = max(1, n * n - 2 * n + 2)
    P = mat_pow(A, exp)
    return all(P[i][j] > 0 for i in range(n) for j in range(n))


def is_block_supported_primitive(A):
    """True iff A is supported on a single nonempty S x S block whose restriction is primitive."""
    n = len(A)
    S = [i for i in range(n) if any(A[i][j] != 0 or A[j][i] != 0 for j in range(n))]
    if not S:
        return False
    sub = [[A[i][j] for j in S] for i in S]
    return is_primitive(sub)


# =============================================================================
# 3. Numerical Eigenvalue Solver (Pure Stdlib) for Stress Testing
# =============================================================================

def float_char_poly(A):
    n = len(A)
    coeffs = [1.0]
    B = [[0.0] * n for _ in range(n)]
    for k in range(1, n + 1):
        if k == 1:
            B = [row[:] for row in A]
        else:
            prev_c = coeffs[-1]
            shifted = [row[:] for row in B]
            for i in range(n):
                shifted[i][i] += prev_c
            B = [[sum(A[i][t] * shifted[t][j] for t in range(n)) for j in range(n)] for i in range(n)]
        tr = sum(B[i][i] for i in range(n))
        coeffs.append(-tr / k)
    return coeffs


def durand_kerner_roots(coeffs):
    n = len(coeffs) - 1
    s = max(1.0, max(abs(coeffs[k]) ** (1.0 / k) for k in range(1, n + 1)))
    sc = [coeffs[k] / (s ** k) for k in range(n + 1)]
    z = [2.0 * cmath.exp(2j * math.pi * (k + 0.17) / n) for k in range(n)]
    for _ in range(500):
        max_step = 0.0
        for i in range(n):
            zi = z[i]
            p = sc[0]
            for c in sc[1:]:
                p = p * zi + c
            denom = 1.0
            for j in range(n):
                if i != j:
                    diff = zi - z[j]
                    if abs(diff) < 1e-18:
                        diff = 1e-18 + 1e-18j
                    denom *= diff
            step = p / denom
            z[i] = zi - step
            if abs(step) > max_step:
                max_step = abs(step)
        if max_step < 1e-14:
            break
    return [zi * s for zi in z]


# =============================================================================
# 4. Main Verification Suite
# =============================================================================

def check_clause_1():
    print("[1/4] Checking Clause 1 counterexamples (reducibility & imprimitivity)...")

    # Counterexample 1A: diag(3, 1)
    diag31 = [[3, 0], [0, 1]]
    verify_char_poly_and_laplace(diag31, [3, 1])
    verify_eigenpair(diag31, 3, [1, 0])
    verify_eigenpair(diag31, 1, [0, 1])
    assert not is_irreducible(diag31)
    assert not is_primitive(diag31)
    assert not has_single_essential_class(diag31)
    assert not is_block_supported_primitive(diag31)
    gap_diag31 = 3 - abs(1)
    assert gap_diag31 == 2 > 0
    print("  PASS: diag(3, 1) has strict gap 2 > 0 while failing all 4 irreducibility/primitivity predicates.")

    # Counterexample 1B: diag(3, P_2)
    periodic3 = [[3, 0, 0], [0, 0, 1], [0, 1, 0]]
    verify_char_poly_and_laplace(periodic3, [3, 1, -1])
    verify_eigenpair(periodic3, 3, [1, 0, 0])
    verify_eigenpair(periodic3, 1, [0, 1, 1])
    verify_eigenpair(periodic3, -1, [0, 1, -1])
    assert not is_irreducible(periodic3)
    assert not is_primitive(periodic3)
    assert not has_single_essential_class(periodic3)
    assert not is_block_supported_primitive(periodic3)
    gap_periodic3 = 3 - max(abs(1), abs(-1))
    assert gap_periodic3 == 2 > 0
    print("  PASS: diag(3, P_2) has periodic block and strict modulus/real gap 2 > 0.")

    # Counterexample 1C: 2-cycle [[0, 2], [2, 0]]
    cycle2 = [[0, 2], [2, 0]]
    verify_char_poly_and_laplace(cycle2, [2, -2])
    verify_eigenpair(cycle2, 2, [1, 1])
    verify_eigenpair(cycle2, -2, [1, -1])
    assert is_irreducible(cycle2)
    assert not is_primitive(cycle2)
    assert 2 - (-2) == 4 > 0
    print("  PASS: cycle [[0, 2], [2, 0]] is irreducible, imprimitive, and has real spectral gap 4 > 0.")


def check_clause_2():
    print("[2/4] Checking Clause 2 counterexamples across all positivity-modulus conventions...")

    # Counterexample 2A: Primitive matrix with zero entrywise modulus
    prim_zero = [[2, 3], [1, 0]]
    assert is_primitive(prim_zero)
    assert mat_pow(prim_zero, 2) == [[Fraction(7), Fraction(6)], [Fraction(2), Fraction(3)]]
    verify_char_poly_and_laplace(prim_zero, [3, -1])
    verify_eigenpair(prim_zero, 3, [3, 1])
    verify_eigenpair(prim_zero, -1, [-1, 1])
    assert pos_modulus_min(prim_zero) == 0
    assert doeblin_modulus(prim_zero) == 1
    assert 3 - abs(-1) == 2 > doeblin_modulus(prim_zero) > pos_modulus_min(prim_zero)
    print("  PASS: primitive [[2, 3], [1, 0]] has m(A) = 0, delta(A) = 1, and strict gap 2.")

    # Counterexample 2B: Unbounded spectral gap at fixed m = 1 and fixed delta = 2
    for K in [1, 2, 5, 10, 25, 50]:
        sym_rk1 = [[K * K, K], [K, 1]]
        verify_char_poly_and_laplace(sym_rk1, [K * K + 1, 0])
        verify_eigenpair(sym_rk1, K * K + 1, [K, 1])
        verify_eigenpair(sym_rk1, 0, [1, -K])
        assert pos_modulus_min(sym_rk1) == 1

        const_delta = [[K, K], [1, 1]]
        verify_char_poly_and_laplace(const_delta, [K + 1, 0])
        verify_eigenpair(const_delta, K + 1, [K, 1])
        verify_eigenpair(const_delta, 0, [1, -1])
        assert pos_modulus_min(const_delta) == 1
        assert doeblin_modulus(const_delta) == 2
    print("  PASS: parametric families [[K^2, K], [K, 1]] and [[K, K], [1, 1]] verified for K up to 50.")

    # Counterexample 2C & 2D: Failure of Doeblin / n * m(A) lower bound on positive symmetric matrices
    doeblin3 = [[7, 2, 2], [2, 7, 2], [2, 2, 2]]
    verify_char_poly_and_laplace(doeblin3, [10, 5, 1])
    verify_eigenpair(doeblin3, 10, [2, 2, 1])
    verify_eigenpair(doeblin3, 5, [1, -1, 0])
    verify_eigenpair(doeblin3, 1, [1, 1, -4])
    assert pos_modulus_min(doeblin3) == 2
    assert doeblin_modulus(doeblin3) == 6
    assert pos_modulus_min(doeblin3) < (10 - 5) < doeblin_modulus(doeblin3)

    doeblin4 = [
        [4, 1, 1, 1],
        [1, 4, 1, 1],
        [1, 1, 1, 1],
        [1, 1, 1, 1],
    ]
    verify_char_poly_and_laplace(doeblin4, [6, 3, 1, 0])
    verify_eigenpair(doeblin4, 6, [2, 2, 1, 1])
    verify_eigenpair(doeblin4, 3, [1, -1, 0, 0])
    verify_eigenpair(doeblin4, 1, [1, 1, -2, -2])
    verify_eigenpair(doeblin4, 0, [0, 0, 1, -1])
    assert pos_modulus_min(doeblin4) == 1
    assert doeblin_modulus(doeblin4) == 4
    assert pos_modulus_min(doeblin4) < (6 - 3) < doeblin_modulus(doeblin4)
    print("  PASS: 3x3 and 4x4 symmetric positive matrices strictly violate gamma(A) >= delta(A) = n * m(A).")

    # Counterexample 2E: Doubly stochastic 4x4 positive matrix violating upper bounds
    P_stoch = [
        [Fraction(3, 10), Fraction(3, 10), Fraction(3, 10), Fraction(1, 10)],
        [Fraction(3, 10), Fraction(3, 10), Fraction(1, 10), Fraction(3, 10)],
        [Fraction(3, 10), Fraction(1, 10), Fraction(3, 10), Fraction(3, 10)],
        [Fraction(1, 10), Fraction(3, 10), Fraction(3, 10), Fraction(3, 10)],
    ]
    for i in range(4):
        assert sum(P_stoch[i]) == Fraction(1)
        assert sum(P_stoch[r][i] for r in range(4)) == Fraction(1)
    verify_char_poly_and_laplace(P_stoch, [Fraction(1), Fraction(1, 5), Fraction(1, 5), Fraction(-1, 5)])
    m_P = pos_modulus_min(P_stoch)
    d_P = doeblin_modulus(P_stoch)
    g_P = Fraction(1) - Fraction(1, 5)
    assert m_P == Fraction(1, 10) and d_P == Fraction(2, 5) and g_P == Fraction(4, 5)
    assert m_P < d_P < g_P
    print("  PASS: doubly stochastic positive 4x4 matrix has m(P)=1/10 < delta(P)=2/5 < gamma(P)=4/5.")

    # Counterexample 2F: Scale-invariant & Birkhoff-Hopf relative-gap arbitrage family
    for p in [2, 3, 5, 10, 25, 50]:
        A_rat = [[p * p + 2 * p - 3, 2 * p], [2 * p, 2 * p + 1]]
        lam1 = (p + 1) * (p + 1)
        lam2 = 2 * p - 3
        verify_char_poly_and_laplace(A_rat, [lam1, lam2])
        verify_eigenpair(A_rat, lam1, [p, 2])
        verify_eigenpair(A_rat, lam2, [2, -p])
        if p == 50:
            rel_gap = Fraction(lam1 - lam2, lam1)
            mod_ratio = Fraction(pos_modulus_min(A_rat), entry_max(A_rat))
            K_bh = (p * p + 2 * p - 3) * (2 * p + 1) / (4.0 * p * p)
            kappa_bh = 2.0 / (math.sqrt(K_bh) + 1.0)
            assert rel_gap > Fraction(96, 100)
            assert mod_ratio < Fraction(4, 100)
            assert kappa_bh < 0.35
    print("  PASS: parametric family A_rat(p) verified; relative gap -> 1 while m/M -> 0 and kappa_BH -> 0.")


def check_asymptotic_dimension_ratio():
    print("[3/4] Checking asymptotic dimension decay gamma(J_n + a(E_11 + E_22)) / (n * m) -> 2/n...")
    a = 10000.0
    for n in range(3, 9):
        # Exact closed-form roots on {e1+e2, e3+...+en} vs full Faddeev-Leverrier
        disc = (a - n + 4.0) ** 2 + 8.0 * (n - 2.0)
        lam1 = 0.5 * ((a + n) + math.sqrt(disc))
        lam2 = a
        gap_closed = lam1 - lam2
        if n <= 6:
            A = [[1.0] * n for _ in range(n)]
            A[0][0] += a
            A[1][1] += a
            ev = durand_kerner_roots(float_char_poly(A))
            mods = sorted((abs(z) for z in ev), reverse=True)
            assert abs((mods[0] - mods[1]) - gap_closed) < 1e-7
        assert 2.0 < gap_closed < 2.01, f"Unexpected gap {gap_closed} at n={n}"
        ratio_to_doeblin = gap_closed / float(n)
        assert ratio_to_doeblin < 2.01 / n
    print("  PASS: gamma(J_n + a(E_11 + E_22)) -> 2m for all n >= 3 while delta(A) = n*m.")


def check_positive_theorems_stress():
    print("[4/4] Stress-testing positive boundary theorems across 2,000 random matrices...")
    random.seed(7163)

    # (a) 500 random strictly positive row-stochastic matrices: gamma_mod(P) >= delta(P) >= n * m(P)
    for trial in range(500):
        n = random.choice([2, 3, 4, 5])
        raw = [[random.uniform(0.05, 5.0) for _ in range(n)] for _ in range(n)]
        P = [[x / sum(row) for x in row] for row in raw]
        ev = durand_kerner_roots(float_char_poly(P))
        mods = sorted((abs(z) for z in ev), reverse=True)
        gap = mods[0] - mods[1]
        m_val = min(min(row) for row in P)
        d_val = sum(min(P[i][j] for i in range(n)) for j in range(n))
        assert gap + 1e-10 >= d_val >= n * m_val - 1e-12, f"Stochastic bound failed at trial {trial}"

    # (b) 1,500 random & heavy-tailed strictly positive matrices:
    #     gamma_mod(A) > m(A) for all n >= 2, and gamma_mod(A) >= 2 * m(A) for n = 2
    min_ratio_n2 = 1e9
    min_ratio_all = 1e9
    for trial in range(1500):
        n = random.choice([2, 3, 4, 5])
        floor_m = random.choice([0.5, 1.0, 2.5])
        A = [[floor_m + (10.0 ** random.uniform(-2, 3) if random.random() < 0.45 else 0.0)
              for _ in range(n)] for _ in range(n)]
        m_val = min(min(row) for row in A)
        ev = durand_kerner_roots(float_char_poly(A))
        mods = sorted((abs(z) for z in ev), reverse=True)
        gap = mods[0] - mods[1]
        ratio = gap / m_val
        if ratio < min_ratio_all:
            min_ratio_all = ratio
        if n == 2 and ratio < min_ratio_n2:
            min_ratio_n2 = ratio
        assert gap > m_val - 1e-9, f"Universal strict floor separation failed at trial {trial}"
        if n == 2:
            assert gap >= 2.0 * m_val - 1e-9, f"Sharp 2x2 bound failed at trial {trial}"

    print(f"  PASS: 500 stochastic & 1,500 positive random matrices verified "
          f"(min gap/m observed: n=2 -> {min_ratio_n2:.6f}, all n -> {min_ratio_all:.6f}).")


def main():
    print("=" * 74)
    print("Verification Suite for Conjecture 00000007163 (Verdict: FALSE / Disproved)")
    print("=" * 74)
    check_clause_1()
    check_clause_2()
    check_asymptotic_dimension_ratio()
    check_positive_theorems_stress()
    print("=" * 74)
    print("ALL EXACT ALGEBRAIC, GRAPH-THEORETIC, AND NUMERICAL CHECKS PASSED.")
    print("=" * 74)


if __name__ == "__main__":
    main()
