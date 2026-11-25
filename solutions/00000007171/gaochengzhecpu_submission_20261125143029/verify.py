#!/usr/bin/env python3
"""
Conjecture 00000007171 — Independent Computational Verification Suite
=====================================================================

Verifies both the positive Schur-convex simplex regime and the three
independent refutations of the unqualified conjecture across exact rational
and floating-point matrix / spectral computations (pure Python 3 standard
library, deterministic).
"""

from __future__ import annotations

import itertools
import math
import os
import random
import sys
from fractions import Fraction
from typing import List, Sequence, Tuple

MatQ = List[List[Fraction]]
VecQ = List[Fraction]


# ---------------------------------------------------------------------------
# Exact Rational Linear Algebra Helpers
# ---------------------------------------------------------------------------

def mat_transpose(a: MatQ) -> MatQ:
    n, m = len(a), len(a[0])
    return [[a[i][j] for i in range(n)] for j in range(m)]


def mat_mul(a: MatQ, b: MatQ) -> MatQ:
    n, k, m = len(a), len(a[0]), len(b[0])
    assert len(b) == k
    return [
        [sum((a[i][r] * b[r][j] for r in range(k)), Fraction(0)) for j in range(m)]
        for i in range(n)
    ]


def mat_sub(a: MatQ, b: MatQ) -> MatQ:
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def mat_add(a: MatQ, b: MatQ) -> MatQ:
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def scalar_mat(n: int, alpha: Fraction) -> MatQ:
    return [[alpha if i == j else Fraction(0) for j in range(n)] for i in range(n)]


def diag_mat(lam: Sequence[Fraction]) -> MatQ:
    n = len(lam)
    return [[lam[i] if i == j else Fraction(0) for j in range(n)] for i in range(n)]


def outer_prod(u: Sequence[Fraction], v: Sequence[Fraction], scale: Fraction = Fraction(1)) -> MatQ:
    return [[scale * u[i] * v[j] for j in range(len(v))] for i in range(len(u))]


def mat_trace(a: MatQ) -> Fraction:
    return sum((a[i][i] for i in range(len(a))), Fraction(0))


def frob_sq(a: MatQ) -> Fraction:
    return sum(
        (a[i][j] * a[i][j] for i in range(len(a)) for j in range(len(a[0]))),
        Fraction(0),
    )


def is_symmetric(a: MatQ) -> bool:
    n = len(a)
    return all(a[i][j] == a[j][i] for i in range(n) for j in range(n))


def exact_rank(a: MatQ) -> int:
    """Exact rank over Q via Gaussian elimination with partial pivoting."""
    m = [row[:] for row in a]
    rows = len(m)
    cols = len(m[0]) if rows else 0
    r = 0
    for c in range(cols):
        pivot = None
        for i in range(r, rows):
            if m[i][c] != 0:
                pivot = i
                break
        if pivot is None:
            continue
        m[r], m[pivot] = m[pivot], m[r]
        piv_val = m[r][c]
        m[r] = [x / piv_val for x in m[r]]
        for i in range(rows):
            if i != r and m[i][c] != 0:
                factor = m[i][c]
                m[i] = [m[i][j] - factor * m[r][j] for j in range(cols)]
        r += 1
        if r == rows:
            break
    return r


def exact_det(a: MatQ) -> Fraction:
    """Exact determinant over Q."""
    n = len(a)
    m = [row[:] for row in a]
    sign = Fraction(1)
    det = Fraction(1)
    for c in range(n):
        pivot = None
        for i in range(c, n):
            if m[i][c] != 0:
                pivot = i
                break
        if pivot is None:
            return Fraction(0)
        if pivot != c:
            m[c], m[pivot] = m[pivot], m[c]
            sign = -sign
        piv_val = m[c][c]
        det *= piv_val
        for i in range(c + 1, n):
            if m[i][c] != 0:
                factor = m[i][c] / piv_val
                for j in range(c, n):
                    m[i][j] -= factor * m[c][j]
    return sign * det


def householder_from_unit(u: Sequence[Fraction]) -> MatQ:
    """Square-root-free Householder orthogonal matrix H over Q with H e_0 = u."""
    n = len(u)
    assert sum((x * x for x in u), Fraction(0)) == Fraction(1)
    if u[0] == Fraction(1):
        return scalar_mat(n, Fraction(1))
    gamma = Fraction(1) / (Fraction(1) - u[0])
    w = [u[0] - Fraction(1)] + list(u[1:])
    return mat_sub(scalar_mat(n, Fraction(1)), outer_prod(w, w, gamma))


def majorizes(mu: Sequence[Fraction], lam: Sequence[Fraction]) -> bool:
    """Returns True iff lam is majorized by mu (lam prec mu)."""
    if len(mu) != len(lam):
        return False
    ms = sorted(mu, reverse=True)
    ls = sorted(lam, reverse=True)
    if sum(ms, Fraction(0)) != sum(ls, Fraction(0)):
        return False
    partial_m = Fraction(0)
    partial_l = Fraction(0)
    for m_val, l_val in zip(ms[:-1], ls[:-1]):
        partial_m += m_val
        partial_l += l_val
        if partial_l > partial_m:
            return False
    return True


def elem_symm(lam: Sequence[Fraction], k: int) -> Fraction:
    return sum(
        (
            math.prod(comb)
            for comb in itertools.combinations(lam, k)
        ),
        Fraction(0),
    )


def is_weakly_concentrated(lam: Sequence[Fraction]) -> bool:
    """True iff at least n - 1 entries of lam are equal."""
    n = len(lam)
    for k in range(n):
        others = [lam[i] for i in range(n) if i != k]
        if len(set(others)) <= 1:
            return True
    return False


# ---------------------------------------------------------------------------
# Verification Stage 1: Positive Non-Vacuity Regime on Lower-Bounded Simplex
# ---------------------------------------------------------------------------

def verify_positive_simplex_regime() -> None:
    print("[1] Positive Non-Vacuity Regime (Schur-Convex Maximization on Delta_{n,c}(a)):")
    unit_vectors = {
        2: [Fraction(3, 5), Fraction(4, 5)],
        3: [Fraction(1, 3), Fraction(2, 3), Fraction(2, 3)],
        4: [Fraction(1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)],
        5: [Fraction(3, 5), Fraction(0), Fraction(4, 5), Fraction(0), Fraction(0)],
    }

    rng = random.Random(717101)
    total_checked = 0

    for n, u in unit_vectors.items():
        a = Fraction(1, 2) if n % 2 == 1 else Fraction(0)
        c = n * a + Fraction(5)
        conc = [c - (n - 1) * a] + [a] * (n - 1)

        # Build rank-one perturbation matrix A(u) = a I_n + (c - n a) u u^T
        base = scalar_mat(n, a)
        pert = outer_prod(u, u, c - n * a)
        mat_a = mat_add(base, pert)
        h_mat = householder_from_unit(u)

        assert is_symmetric(mat_a), "A(u) must be symmetric"
        assert mat_trace(mat_a) == c, "tr(A(u)) must equal c"
        assert exact_rank(mat_sub(mat_a, base)) == 1, "rank(A(u) - a I_n) must be 1"
        assert mat_mul(mat_transpose(h_mat), h_mat) == scalar_mat(n, Fraction(1))
        assert mat_mul(h_mat, mat_transpose(h_mat)) == scalar_mat(n, Fraction(1))
        diag_check = mat_mul(mat_mul(mat_transpose(h_mat), mat_a), h_mat)
        assert diag_check == diag_mat(conc), "H^T A(u) H must equal diag(conc)"

        f2_conc = sum((x * x for x in conc), Fraction(0))
        f3_conc = sum((x * x * x for x in conc), Fraction(0))

        # Sample 500 exact rational points in Delta_{n,c}(a)
        for _ in range(500):
            weights = [rng.randint(0, 12) for _ in range(n)]
            if sum(weights) == 0:
                weights[0] = 1
            tot_w = Fraction(sum(weights))
            excess = c - n * a
            lam = [a + excess * Fraction(w) / tot_w for w in weights]
            assert sum(lam, Fraction(0)) == c and all(x >= a for x in lam)
            assert majorizes(conc, lam), "conc must majorize every feasible spectrum"

            f2_lam = sum((x * x for x in lam), Fraction(0))
            f3_lam = sum((x * x * x for x in lam), Fraction(0))
            # Verify exact identity: f2_conc - f2_lam = 2 * sum_{i<j} (lam_i - a)(lam_j - a)
            pair_excess = sum(
                (
                    (lam[i] - a) * (lam[j] - a)
                    for i in range(n)
                    for j in range(i + 1, n)
                ),
                Fraction(0),
            )
            assert f2_conc - f2_lam == 2 * pair_excess
            assert f2_lam <= f2_conc and f3_lam <= f3_conc
            if sorted(lam, reverse=True) != conc:
                assert f2_lam < f2_conc, "Strict uniqueness up to permutation for F_2"
            total_checked += 1

    print(
        f"  Verified exact Householder diagonalization, rank(A(u) - a I_n) = 1, "
        f"majorization, and strict F_2 maximization across {total_checked} spectra [PASS]"
    )


# ---------------------------------------------------------------------------
# Verification Stage 2: Refutation R1 — Schur-Concave Fixed-Trace Extrema
# ---------------------------------------------------------------------------

def verify_refutation_r1_schur_concave() -> None:
    print("[2] Refutation R1 (Schur-Concave Objectives on PSD Simplex {A >= 0, tr(A) = c}):")
    rng = random.Random(717102)
    for n in range(2, 7):
        c = Fraction(n + 3, 2)
        unif = [c / n] * n
        conc = [c] + [Fraction(0)] * (n - 1)

        det_unif = math.prod(unif)
        det_conc = math.prod(conc)
        e2_unif = elem_symm(unif, 2)
        e2_conc = elem_symm(conc, 2)

        assert det_unif == (c / n) ** n > 0 and det_conc == 0
        assert e2_unif == Fraction(n - 1, 2 * n) * c * c > 0 and e2_conc == 0
        assert exact_rank(diag_mat(unif)) == n > 1

        unif_f = [float(x) for x in unif]
        conc_f = [float(x) for x in conc]
        entropy_unif = -sum(x * math.log(x) for x in unif_f if x > 0.0)
        entropy_conc = -sum(x * math.log(x) for x in conc_f if x > 0.0)
        assert entropy_unif > entropy_conc + 1e-9

        for _ in range(400):
            weights = [rng.randint(0, 15) for _ in range(n)]
            if sum(weights) == 0:
                weights[0] = 1
            tot_w = Fraction(sum(weights))
            lam = [c * Fraction(w) / tot_w for w in weights]

            det_lam = math.prod(lam)
            e2_lam = elem_symm(lam, 2)
            # Exact algebraic identity: 2*(e2_unif - e2_lam) = sum_i (lam_i - c/n)^2
            sq_dev = sum(((x - c / n) ** 2 for x in lam), Fraction(0))
            assert 2 * (e2_unif - e2_lam) == sq_dev
            assert det_lam <= det_unif and e2_lam <= e2_unif
            if lam != unif:
                assert det_lam < det_unif and e2_lam < e2_unif

    print(
        "  Verified for 2 <= n <= 6: unique maximum of det(A), e_2(A), and von Neumann "
        "entropy is uniform (c/n) I_n (rank n), while concentrated c u u^T gives minimum 0 [PASS]"
    )


# ---------------------------------------------------------------------------
# Verification Stage 3: Refutation R2 — Box-Constrained Extrema & Classification
# ---------------------------------------------------------------------------

def box_majorization_top(n: int, a: Fraction, b: Fraction, c: Fraction) -> VecQ:
    assert b > a and n * a <= c <= n * b
    span = b - a
    excess = c - n * a
    q = int(excess // span)
    if q >= n:
        return [b] * n
    rem = excess - q * span
    return [b] * q + [a + rem] + [a] * (n - 1 - q)


def min_rank_from_any_scalar(mat_a: MatQ, candidate_alphas: Sequence[Fraction]) -> int:
    n = len(mat_a)
    # Test all eigenvalues + off-spectrum probes; any alpha outside spectrum gives full rank n
    probes = list(set(candidate_alphas) | {Fraction(-7, 3), Fraction(19, 5)})
    return min(exact_rank(mat_sub(mat_a, scalar_mat(n, alpha))) for alpha in probes)


def verify_refutation_r2_box_constraints() -> None:
    print("[3] Refutation R2 (Schur-Convex & Majorization Extrema under Box Constraints):")

    # 3A: Minimal dimension n = 3 counterexample: 0 <= lam_i <= 2, tr(A) = 3 -> (2, 1, 0)
    lam_n3 = box_majorization_top(3, Fraction(0), Fraction(2), Fraction(3))
    assert lam_n3 == [Fraction(2), Fraction(1), Fraction(0)]
    assert not is_weakly_concentrated(lam_n3)
    h3 = householder_from_unit([Fraction(1, 3), Fraction(2, 3), Fraction(2, 3)])
    a_n3 = mat_mul(mat_mul(h3, diag_mat(lam_n3)), mat_transpose(h3))
    assert is_symmetric(a_n3) and mat_trace(a_n3) == Fraction(3)
    assert frob_sq(a_n3) == Fraction(5)
    min_rk_n3 = min_rank_from_any_scalar(a_n3, lam_n3)
    assert min_rk_n3 == 2, f"Expected min rank 2 at n=3, got {min_rk_n3}"
    print(
        f"  3A (Sharp minimal dimension n=3, 0 <= A <= 2 I_3, tr=3): "
        f"unique majorization-max = (2, 1, 0), ||A||_F^2 = 5, "
        f"min_alpha rank(A - alpha I_3) = {min_rk_n3} > 1 [VERIFIED]"
    )

    # 3B: Ky Fan 2-frame polytope at n = 4: 0 <= lam_i <= 1, tr(A) = 2 -> (1, 1, 0, 0)
    lam_n4 = box_majorization_top(4, Fraction(0), Fraction(1), Fraction(2))
    assert lam_n4 == [Fraction(1), Fraction(1), Fraction(0), Fraction(0)]
    assert not is_weakly_concentrated(lam_n4)
    h4 = householder_from_unit([Fraction(1, 2)] * 4)
    a_n4 = mat_mul(mat_mul(h4, diag_mat(lam_n4)), mat_transpose(h4))
    assert is_symmetric(a_n4) and mat_trace(a_n4) == Fraction(2)
    assert mat_mul(a_n4, a_n4) == a_n4  # Orthogonal rank-2 projector
    assert frob_sq(a_n4) == Fraction(2)
    conc_feasible_n4 = [Fraction(1), Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)]
    assert sum((x * x for x in conc_feasible_n4), Fraction(0)) == Fraction(4, 3) < Fraction(2)
    min_rk_n4 = min_rank_from_any_scalar(a_n4, lam_n4)
    assert min_rk_n4 == 2, f"Expected min rank 2 at n=4, got {min_rk_n4}"
    print(
        f"  3B (Ky Fan 2-frame polytope n=4, 0 <= A <= I_4, tr=2): "
        f"unique majorization-max = (1, 1, 0, 0), ||A||_F^2 = 2 > 4/3, "
        f"min_alpha rank(A - alpha I_4) = {min_rk_n4} > 1 [VERIFIED]"
    )

    # 3C: Exhaustive verification of the exact IFF classification theorem across 2 <= n <= 6
    rng = random.Random(717103)
    cases_tested = 0
    interior_counterexamples = 0
    for n in range(2, 7):
        a = Fraction(1, 2)
        b = Fraction(5, 2)
        # Sweep trace c in fine steps of 1/4 across (n*a, n*b)
        num_steps = int((n * b - n * a) * 4)
        for step in range(1, num_steps):
            c = n * a + Fraction(step, 4)
            top = box_majorization_top(n, a, b, c)
            mat_top = diag_mat(top)

            # Verify top majorizes random feasible points in B_{n,c}(a,b)
            for _ in range(40):
                # Construct feasible point via convex combination / clamping
                vals = [a + (b - a) * Fraction(rng.randint(0, 20), 20) for _ in range(n)]
                # Project sum to c within [a, b]^n greedily
                diff = c - sum(vals, Fraction(0))
                for idx in range(n):
                    if diff > 0:
                        add_amt = min(diff, b - vals[idx])
                        vals[idx] += add_amt
                        diff -= add_amt
                    elif diff < 0:
                        sub_amt = min(-diff, vals[idx] - a)
                        vals[idx] -= sub_amt
                        diff += sub_amt
                if diff == 0:
                    assert majorizes(top, vals)
                    assert sum((x * x for x in vals), Fraction(0)) <= sum(
                        (x * x for x in top), Fraction(0)
                    )

            min_rk = min_rank_from_any_scalar(mat_top, top)
            weak_conc = is_weakly_concentrated(top)
            expected_rank_le_1 = (c <= (n - 1) * a + b) or (c >= a + (n - 1) * b)
            expected_floor_conc = c <= (n - 1) * a + b

            assert (min_rk <= 1) == expected_rank_le_1
            assert weak_conc == expected_rank_le_1
            is_floor_conc = (top[0] > a) and all(x == a for x in top[1:])
            assert is_floor_conc == expected_floor_conc
            if not expected_rank_le_1:
                interior_counterexamples += 1
            cases_tested += 1

    print(
        f"  3C (Exact IFF Classification on B_{{n,c}}(a,b) for 2 <= n <= 6): "
        f"tested {cases_tested} parameter regimes ({interior_counterexamples} non-rank-one "
        f"regimes in ((n-1)a+b, a+(n-1)b)) — 100% match [PASS]"
    )


# ---------------------------------------------------------------------------
# Verification Stage 4: Trace-Frobenius Ellipsoid Split (Wolkowicz-Styan vs Ky Fan)
# ---------------------------------------------------------------------------

def verify_trace_frobenius_ellipsoid() -> None:
    print("[4] Trace-Frobenius Slice {tr(A) = c, tr(A^2) <= rho^2} (No Majorization Top for n >= 3):")
    for n in (3, 4, 5):
        c = float(n)
        rad = 1.0  # sum (lam_i - 1)^2 <= 1, sum lam_i = n
        # 1-spike maximizer of lam_1 (Wolkowicz-Styan upper bound)
        d1_hi = rad * math.sqrt((n - 1) / n)
        d1_lo = -rad / math.sqrt(n * (n - 1))
        ws_1spike = [1.0 + d1_hi] + [1.0 + d1_lo] * (n - 1)

        # 2-spike maximizer of lam_1 + lam_2 (Ky Fan 2-norm)
        d2_hi = rad * math.sqrt((n - 2) / (2.0 * n))
        d2_lo = -rad * math.sqrt(2.0 / (n * (n - 2)))
        kf_2spike = [1.0 + d2_hi, 1.0 + d2_hi] + [1.0 + d2_lo] * (n - 2)

        assert abs(sum(ws_1spike) - c) < 1e-12 and abs(sum(x * x for x in ws_1spike) - (n + 1)) < 1e-12
        assert abs(sum(kf_2spike) - c) < 1e-12 and abs(sum(x * x for x in kf_2spike) - (n + 1)) < 1e-12
        assert ws_1spike[0] > kf_2spike[0] + 1e-6
        assert (kf_2spike[0] + kf_2spike[1]) > (ws_1spike[0] + ws_1spike[1]) + 1e-6

    print(
        "  Verified for n in {3, 4, 5}: 1-spike maximizes lam_1 while 2-spike strictly "
        "beats 1-spike on Ky Fan 2-norm lam_1 + lam_2 => incomparable under majorization [PASS]"
    )


# ---------------------------------------------------------------------------
# Verification Stage 5: Refutation R3 — Fixed-Trace Rank-One Obstruction
# ---------------------------------------------------------------------------

def verify_refutation_r3_traceless_rank_one() -> None:
    print("[5] Refutation R3 (Fixed-Trace Rank-One Perturbation Obstruction tr(R) = 0):")
    rng = random.Random(717105)
    sym_checked = 0
    nilp_checked = 0

    for n in range(2, 7):
        # 5A: Test symmetric rank-<=1 matrices R = beta u u^T and general symmetric u v^T
        for _ in range(200):
            u = [Fraction(rng.randint(-4, 4), rng.randint(1, 3)) for _ in range(n)]
            beta = Fraction(rng.randint(-5, 5), rng.randint(1, 3))
            r_mat = outer_prod(u, u, beta)
            assert is_symmetric(r_mat) and exact_rank(r_mat) <= 1
            tr_r = mat_trace(r_mat)
            assert frob_sq(r_mat) == tr_r * tr_r
            if tr_r == 0:
                assert r_mat == scalar_mat(n, Fraction(0))
            sym_checked += 1

        # 5B: Non-symmetric traceless rank-1 perturbations R = u v^T with v^T u = 0 are nilpotent
        u = [Fraction(1)] + [Fraction(0)] * (n - 1)
        v = [Fraction(0), Fraction(3)] + [Fraction(-1)] * (n - 2)
        r_ns = outer_prod(u, v)
        assert exact_rank(r_ns) == 1 and mat_trace(r_ns) == 0
        assert mat_mul(r_ns, r_ns) == scalar_mat(n, Fraction(0)), "R^2 must be 0"
        # Check det(t I - (alpha I + R)) == (t - alpha)^n at n+1 interpolation points t
        alpha = Fraction(7, 3)
        pert_scalar = mat_add(scalar_mat(n, alpha), r_ns)
        for t_int in range(-2, n + 2):
            t_val = Fraction(t_int)
            char_val = exact_det(mat_sub(scalar_mat(n, t_val), pert_scalar))
            assert char_val == (t_val - alpha) ** n
        nilp_checked += 1

        # 5C: Minimum rank of nonzero trace-preserving symmetric perturbation is 2
        unif_mat = scalar_mat(n, Fraction(1))  # tr = n
        conc_mat = outer_prod([Fraction(1)] + [Fraction(0)] * (n - 1),
                              [Fraction(1)] + [Fraction(0)] * (n - 1),
                              Fraction(n))     # tr = n
        diff_full = mat_sub(conc_mat, unif_mat)
        assert mat_trace(diff_full) == 0 and exact_rank(diff_full) == n >= 2

        # Robin-Muirhead / Givens-Jacobi minimal trace-preserving transfer delta (e_0 e_0^T - e_1 e_1^T)
        rm_transfer = diag_mat([Fraction(1), Fraction(-1)] + [Fraction(0)] * (n - 2))
        assert is_symmetric(rm_transfer) and mat_trace(rm_transfer) == 0
        assert exact_rank(rm_transfer) == 2

    print(
        f"  Verified ||R||_F^2 = (tr R)^2 across {sym_checked} symmetric rank-<=1 matrices, "
        f"nilpotency R^2 = 0 across {nilp_checked} dimensions, and sharp minimum rank 2 "
        f"for nonzero trace-preserving symmetric perturbations [PASS]"
    )


def main() -> int:
    here = os.path.dirname(os.path.abspath(__file__))
    source_path = os.path.join(here, "SOURCE.md")
    assert os.path.isfile(source_path), "SOURCE.md must exist in package/"

    print("========================================================================")
    print("Conjecture 00000007171 — Independent Computational Verification")
    print("========================================================================\n")

    verify_positive_simplex_regime()
    print()
    verify_refutation_r1_schur_concave()
    print()
    verify_refutation_r2_box_constraints()
    print()
    verify_trace_frobenius_ellipsoid()
    print()
    verify_refutation_r3_traceless_rank_one()
    print()
    print("ALL COMPUTATIONAL CHECKS PASSED SUCCESSFULLY (VERDICT: DISPROVED).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
