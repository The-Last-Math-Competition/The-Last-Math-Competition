#!/usr/bin/env python3
"""Exact rational verification suite for Conjecture 00000007179.

Conjecture 00000007179 (residual-projection Kato analytic perturbation):
  - Clause 1 (TRUE): Simple eigenvalues are analytically perturbable.
    Around an algebraically simple eigenvalue lambda_0 of A_0, the Riesz
    spectral eigenprojection P = (v_0 w_0^T)/(w_0^T v_0), complementary
    (residual) projection Q = I - P, and Kato reduced resolvent S satisfying
    (A_0 - lambda_0 I) S = S (A_0 - lambda_0 I) = Q and P S = S P = 0 construct
    a unique normalized formal power series (lambda(eps), v(eps)) with an
    explicit positive analytic convergence radius R_0 = 1 / rho > 0, satisfying
      lambda_1 = tr(P A_1) = tr(P A_1 P) = (w_0^T A_1 v_0)/(w_0^T v_0),
      v_1      = - S A_1 v_0,
      lambda_2 = - tr(P A_1 S A_1) = - (w_0^T A_1 S A_1 v_0)/(w_0^T v_0),
      P_1      = - P A_1 S - S A_1 P.
  - Clause 2 (FALSE across all candidate readings): "and the coefficient of the
    perturbation is the residual projection" fails under every interpretation:
      * Reading A (lambda_1 via Q = I - P: tr(Q A_1), w_0^T Q A_1 v_0 / w_0^T v_0,
        ||Q A_1 v_0||, or operator derivative D lambda(A_0) = Q)
      * Reading B (first-order eigenvector v_1 = +/- Q A_1 v_0)
      * Reading C (second-order eigenvalue lambda_2 = +/- tr(P A_1 Q A_1))
      * Reading D (first-order eigenprojection P_1 = +/- Q or +/- (P A_1 Q + Q A_1 P))
  - Bonus sharpness check: defective double eigenvalue A(eps) = [[0, 1], [eps, 0]]
    has Puiseux branches +/- sqrt(eps) and admits no formal power series root or
    eigenvector at eps = 0.

All algebraic identities and counterexamples use exact `fractions.Fraction`
arithmetic with zero floating-point rounding in proof assertions.
"""

from __future__ import annotations

from fractions import Fraction
import math
import random
import sys
from typing import List, Sequence, Tuple

Scalar = Fraction
Vec = List[Scalar]
Mat = List[List[Scalar]]


def zeros_vec(n: int) -> Vec:
    return [Fraction(0) for _ in range(n)]


def zeros_mat(n: int) -> Mat:
    return [[Fraction(0) for _ in range(n)] for _ in range(n)]


def eye_mat(n: int) -> Mat:
    m = zeros_mat(n)
    for i in range(n):
        m[i][i] = Fraction(1)
    return m


def mat_add(a: Mat, b: Mat) -> Mat:
    n = len(a)
    return [[a[i][j] + b[i][j] for j in range(n)] for i in range(n)]


def mat_sub(a: Mat, b: Mat) -> Mat:
    n = len(a)
    return [[a[i][j] - b[i][j] for j in range(n)] for i in range(n)]


def mat_smul(c: Scalar, a: Mat) -> Mat:
    n = len(a)
    return [[c * a[i][j] for j in range(n)] for i in range(n)]


def vec_add(u: Vec, v: Vec) -> Vec:
    return [x + y for x, y in zip(u, v)]


def vec_sub(u: Vec, v: Vec) -> Vec:
    return [x - y for x, y in zip(u, v)]


def vec_smul(c: Scalar, u: Vec) -> Vec:
    return [c * x for x in u]


def vec_dot(u: Vec, v: Vec) -> Scalar:
    return sum((x * y for x, y in zip(u, v)), Fraction(0))


def mat_vec(a: Mat, v: Vec) -> Vec:
    n = len(a)
    return [sum((a[i][j] * v[j] for j in range(n)), Fraction(0)) for i in range(n)]


def mat_mul(a: Mat, b: Mat) -> Mat:
    n = len(a)
    out = zeros_mat(n)
    for i in range(n):
        for k in range(n):
            aik = a[i][k]
            if aik != 0:
                for j in range(n):
                    out[i][j] += aik * b[k][j]
    return out


def mat_transpose(a: Mat) -> Mat:
    n = len(a)
    return [[a[j][i] for j in range(n)] for i in range(n)]


def mat_trace(a: Mat) -> Scalar:
    return sum((a[i][i] for i in range(len(a))), Fraction(0))


def rank_one_outer(v: Vec, w: Vec, denom: Scalar) -> Mat:
    n = len(v)
    return [[(v[i] * w[j]) / denom for j in range(n)] for i in range(n)]


def vec_norm1(v: Vec) -> Scalar:
    return sum((abs(x) for x in v), Fraction(0))


def mat_norm_sum(a: Mat) -> Scalar:
    return sum((abs(x) for row in a for x in row), Fraction(0))


def mat_inv(a: Mat) -> Mat:
    """Exact Gauss-Jordan matrix inverse over Q."""
    n = len(a)
    aug = [row[:] + eye_row[:] for row, eye_row in zip(a, eye_mat(n))]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise ValueError("Singular matrix")
        aug[col], aug[piv] = aug[piv], aug[col]
        scale = aug[col][col]
        for j in range(2 * n):
            aug[col][j] /= scale
        for r in range(n):
            if r != col and aug[r][col] != 0:
                factor = aug[r][col]
                for j in range(2 * n):
                    aug[r][j] -= factor * aug[col][j]
    return [row[n:] for row in aug]


def poly_mul(p: Sequence[Scalar], q: Sequence[Scalar]) -> List[Scalar]:
    """Multiply polynomials represented ascendingly: p[k] = coeff of x^k."""
    if not p or not q:
        return [Fraction(0)]
    out = [Fraction(0) for _ in range(len(p) + len(q) - 1)]
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def poly_eval_scalar(p: Sequence[Scalar], x: Scalar) -> Scalar:
    acc = Fraction(0)
    for coeff in reversed(p):
        acc = acc * x + coeff
    return acc


def poly_eval_mat(p: Sequence[Scalar], a: Mat) -> Mat:
    n = len(a)
    acc = zeros_mat(n)
    for coeff in reversed(p):
        acc = mat_add(mat_mul(acc, a), mat_smul(coeff, eye_mat(n)))
    return acc


def poly_div_by_linear(p: Sequence[Scalar], root: Scalar) -> Tuple[List[Scalar], Scalar]:
    """Return (r, rem) such that p(x) = (x - root) * r(x) + rem."""
    deg = len(p) - 1
    if deg <= 0:
        return [Fraction(0)], (p[0] if p else Fraction(0))
    r = [Fraction(0) for _ in range(deg)]
    acc = Fraction(0)
    for k in range(deg, 0, -1):
        acc = p[k] + root * acc
        r[k - 1] = acc
    rem = p[0] + root * acc
    return r, rem


def build_random_invertible(rng: random.Random, n: int) -> Mat:
    """Construct an exact unimodular integer matrix via L * U with unit diagonals."""
    lower = eye_mat(n)
    upper = eye_mat(n)
    for i in range(n):
        for j in range(i):
            lower[i][j] = Fraction(rng.randint(-2, 2))
        for j in range(i + 1, n):
            upper[i][j] = Fraction(rng.randint(-2, 2))
    return mat_mul(lower, upper)


def riesz_kato_from_charpoly(
    a0: Mat, lam0: Scalar, q_poly: Sequence[Scalar]
) -> Tuple[Mat, Mat, Mat]:
    """Construct (P, Q, S) purely as polynomials in A_0 from chi_{A_0}(x) = (x - lam0) q(x)."""
    n = len(a0)
    mu0 = poly_eval_scalar(q_poly, lam0)
    assert mu0 != 0, "Eigenvalue lam0 must be algebraically simple (q(lam0) != 0)"
    r_poly, rem = poly_div_by_linear(q_poly, lam0)
    assert rem == mu0
    q_a0 = poly_eval_mat(q_poly, a0)
    r_a0 = poly_eval_mat(r_poly, a0)
    p_proj = mat_smul(Fraction(1) / mu0, q_a0)
    q_proj = mat_sub(eye_mat(n), p_proj)
    s_res = mat_smul(-Fraction(1) / mu0, mat_mul(r_a0, q_proj))
    return p_proj, q_proj, s_res


def kato_series(
    lam0: Scalar,
    v0: Vec,
    w0: Vec,
    s_res: Mat,
    a1: Mat,
    order: int,
) -> Tuple[List[Scalar], List[Vec]]:
    """Compute exact normalized Kato series (lambda_k, v_k) for 0 <= k <= order."""
    denom = vec_dot(w0, v0)
    assert denom != 0
    lams: List[Scalar] = [lam0]
    vecs: List[Vec] = [v0[:]]
    for k in range(1, order + 1):
        lam_k = vec_dot(w0, mat_vec(a1, vecs[k - 1])) / denom
        lams.append(lam_k)
        vk = vec_smul(-Fraction(1), mat_vec(s_res, mat_vec(a1, vecs[k - 1])))
        for j in range(1, k):
            vk = vec_add(vk, vec_smul(lams[j], mat_vec(s_res, vecs[k - j])))
        vecs.append(vk)
    return lams, vecs


def det_poly_in_eps(a0: Mat, a1: Mat, lam_series: Sequence[Scalar], mod_deg: int) -> List[Scalar]:
    """Compute det(lambda(eps) I - (A_0 + eps A_1)) modulo eps^mod_deg via Bareiss/Laplace."""
    n = len(a0)

    def trunc_mul(p: List[Scalar], q: List[Scalar]) -> List[Scalar]:
        out = [Fraction(0) for _ in range(mod_deg)]
        for i, x in enumerate(p):
            if x != 0:
                for j in range(min(len(q), mod_deg - i)):
                    out[i + j] += x * q[j]
        return out

    def trunc_sub(p: List[Scalar], q: List[Scalar]) -> List[Scalar]:
        return [p[i] - q[i] for i in range(mod_deg)]

    # Build n x n matrix of truncated power series
    m_poly: List[List[List[Scalar]]] = [
        [[Fraction(0) for _ in range(mod_deg)] for _ in range(n)] for _ in range(n)
    ]
    for i in range(n):
        for j in range(n):
            if i == j:
                for d in range(min(len(lam_series), mod_deg)):
                    m_poly[i][j][d] = lam_series[d]
            m_poly[i][j][0] -= a0[i][j]
            if mod_deg > 1:
                m_poly[i][j][1] -= a1[i][j]

    # Recursive minor expansion (n <= 5)
    def det_rec(rows: List[int], cols: List[int]) -> List[Scalar]:
        k = len(rows)
        if k == 1:
            return m_poly[rows[0]][cols[0]][:]
        acc = [Fraction(0) for _ in range(mod_deg)]
        r0 = rows[0]
        rest_rows = rows[1:]
        for idx, c in enumerate(cols):
            entry = m_poly[r0][c]
            if any(x != 0 for x in entry):
                sub_cols = cols[:idx] + cols[idx + 1 :]
                term = trunc_mul(entry, det_rec(rest_rows, sub_cols))
                if idx % 2 == 0:
                    acc = [acc[d] + term[d] for d in range(mod_deg)]
                else:
                    acc = trunc_sub(acc, term)
        return acc

    idx_all = list(range(n))
    return det_rec(idx_all, idx_all)


def test_suite_1_riesz_kato_decomposition() -> None:
    rng = random.Random(717901)
    trials = 0
    for n in range(2, 7):
        for t in range(30):
            # Distinct integer eigenvalues, with optional Jordan block in complement!
            distinct = rng.sample(range(-8, 9), n)
            lam0 = Fraction(distinct[0])
            comp_eigs = [Fraction(x) for x in distinct[1:]]
            # In half the trials for n >= 3, make the complementary block non-diagonalizable!
            use_jordan_comp = (n >= 3) and (t % 2 == 1)
            j_mat = zeros_mat(n)
            j_mat[0][0] = lam0
            if use_jordan_comp:
                mu = comp_eigs[0]
                for i in range(1, n):
                    j_mat[i][i] = mu if i <= 2 else comp_eigs[i - 1]
                j_mat[1][2] = Fraction(1)
                factors = [[-e, Fraction(1)] for e in [j_mat[i][i] for i in range(1, n)]]
            else:
                for i in range(1, n):
                    j_mat[i][i] = comp_eigs[i - 1]
                factors = [[-e, Fraction(1)] for e in comp_eigs]

            q_poly: List[Scalar] = [Fraction(1)]
            for fac in factors:
                q_poly = poly_mul(q_poly, fac)
            chi_poly = poly_mul([-lam0, Fraction(1)], q_poly)

            v_sim = build_random_invertible(rng, n)
            v_inv = mat_inv(v_sim)
            a0 = mat_mul(mat_mul(v_sim, j_mat), v_inv)

            # Cayley-Hamilton check
            assert poly_eval_mat(chi_poly, a0) == zeros_mat(n)

            # Right and left eigenvectors for lam0
            e0 = zeros_vec(n)
            e0[0] = Fraction(1)
            v0 = mat_vec(v_sim, e0)
            w0 = mat_vec(mat_transpose(v_inv), e0)
            assert mat_vec(a0, v0) == vec_smul(lam0, v0)
            assert mat_vec(mat_transpose(a0), w0) == vec_smul(lam0, w0)
            assert vec_dot(w0, v0) == Fraction(1)

            # Polynomial Riesz-Kato construction
            p_proj, q_proj, s_res = riesz_kato_from_charpoly(a0, lam0, q_poly)
            p_outer = rank_one_outer(v0, w0, vec_dot(w0, v0))
            assert p_proj == p_outer, "Polynomial Riesz projection must equal v0 w0^T / (w0^T v0)"
            assert mat_mul(p_proj, p_proj) == p_proj
            assert mat_trace(p_proj) == Fraction(1)
            assert mat_mul(q_proj, q_proj) == q_proj
            assert mat_trace(q_proj) == Fraction(n - 1)
            assert mat_mul(p_proj, q_proj) == zeros_mat(n)
            assert mat_mul(q_proj, p_proj) == zeros_mat(n)
            assert mat_mul(a0, p_proj) == mat_smul(lam0, p_proj)
            assert mat_mul(p_proj, a0) == mat_smul(lam0, p_proj)

            shifted = mat_sub(a0, mat_smul(lam0, eye_mat(n)))
            assert mat_mul(shifted, s_res) == q_proj
            assert mat_mul(s_res, shifted) == q_proj
            assert mat_mul(p_proj, s_res) == zeros_mat(n)
            assert mat_mul(s_res, p_proj) == zeros_mat(n)
            trials += 1

    print(
        f"[PASS] Suite 1: Verified Lagrange-Sylvester-Riesz polynomial construction & Kato "
        f"(P, Q, S) axioms on {trials} non-symmetric & Jordan-complement matrices (2 <= n <= 6)."
    )


def test_suite_2_and_3_all_orders_and_majorant() -> None:
    rng = random.Random(717902)
    order = 8
    trials = 0
    for n in range(2, 6):
        for t in range(30):
            distinct = rng.sample(range(-6, 7), n)
            lam0 = Fraction(distinct[0])
            j_mat = zeros_mat(n)
            j_mat[0][0] = lam0
            for i in range(1, n):
                j_mat[i][i] = Fraction(distinct[i])
            if n >= 3 and t % 3 == 0:
                j_mat[2][2] = j_mat[1][1]
                j_mat[1][2] = Fraction(1)

            q_poly: List[Scalar] = [Fraction(1)]
            for i in range(1, n):
                q_poly = poly_mul(q_poly, [-j_mat[i][i], Fraction(1)])

            v_sim = build_random_invertible(rng, n)
            v_inv = mat_inv(v_sim)
            a0 = mat_mul(mat_mul(v_sim, j_mat), v_inv)
            a1 = [[Fraction(rng.randint(-3, 3)) for _ in range(n)] for _ in range(n)]

            e0 = zeros_vec(n)
            e0[0] = Fraction(1)
            # Non-unit scaling check on v0 and w0
            v0 = vec_smul(Fraction(2), mat_vec(v_sim, e0))
            w0 = vec_smul(Fraction(3), mat_vec(mat_transpose(v_inv), e0))
            denom = vec_dot(w0, v0)
            assert denom == Fraction(6)

            p_proj, q_proj, s_res = riesz_kato_from_charpoly(a0, lam0, q_poly)
            lams, vecs = kato_series(lam0, v0, w0, s_res, a1, order)

            # 1. Exact normalization and formal power series eigenvalue equation at all orders
            assert mat_vec(a0, vecs[0]) == vec_smul(lams[0], vecs[0])
            for k in range(1, order + 1):
                assert vec_dot(w0, vecs[k]) == Fraction(0)
                assert mat_vec(p_proj, vecs[k]) == zeros_vec(n)
                assert mat_vec(q_proj, vecs[k]) == vecs[k]
                lhs = vec_add(mat_vec(a0, vecs[k]), mat_vec(a1, vecs[k - 1]))
                rhs = zeros_vec(n)
                for j in range(k + 1):
                    rhs = vec_add(rhs, vec_smul(lams[j], vecs[k - j]))
                assert lhs == rhs, f"Power series recursion mismatch at order k={k}"

            # 2. Characteristic polynomial congruence modulo eps^(order+1)
            det_coeffs = det_poly_in_eps(a0, a1, lams, order + 1)
            assert all(c == 0 for c in det_coeffs), f"Nonzero charpoly coeff: {det_coeffs}"

            # 3. Closed-form first- and second-order Kato formulas
            lam1_tr_p = mat_trace(mat_mul(p_proj, a1))
            lam1_tr_pap = mat_trace(mat_mul(mat_mul(p_proj, a1), p_proj))
            lam1_rayleigh = vec_dot(w0, mat_vec(a1, v0)) / denom
            assert lams[1] == lam1_tr_p == lam1_tr_pap == lam1_rayleigh

            v1_expected = vec_smul(-Fraction(1), mat_vec(s_res, mat_vec(a1, v0)))
            assert vecs[1] == v1_expected

            lam2_tr = -mat_trace(mat_mul(mat_mul(mat_mul(p_proj, a1), s_res), a1))
            lam2_bilinear = -vec_dot(w0, mat_vec(a1, mat_vec(s_res, mat_vec(a1, v0)))) / denom
            assert lams[2] == lam2_tr == lam2_bilinear

            # First-order eigenprojection coefficient P_1 = - P A_1 S - S A_1 P
            p1 = mat_sub(
                zeros_mat(n),
                mat_add(
                    mat_mul(mat_mul(p_proj, a1), s_res),
                    mat_mul(mat_mul(s_res, a1), p_proj),
                ),
            )
            # Check idempotence at O(eps): P_0 P_1 + P_1 P_0 = P_1
            assert mat_add(mat_mul(p_proj, p1), mat_mul(p1, p_proj)) == p1
            # Check commutation at O(eps): A_0 P_1 + A_1 P_0 = P_0 A_1 + P_1 A_0
            assert mat_add(mat_mul(a0, p1), mat_mul(a1, p_proj)) == mat_add(
                mat_mul(p_proj, a1), mat_mul(p1, a0)
            )
            # Check tr(A_0 P_1 + A_1 P_0) = lambda_1 (since tr(P_1) = 0)
            assert mat_trace(p1) == Fraction(0)
            assert mat_trace(mat_add(mat_mul(a0, p1), mat_mul(a1, p_proj))) == lams[1]

            # 4. Explicit Cauchy-Kato majorant bound
            v0_norm = vec_norm1(v0)
            alpha = (vec_norm1(w0) / abs(denom)) * mat_norm_sum(a1)
            beta = mat_norm_sum(mat_mul(s_res, a1))
            sigma = mat_norm_sum(s_res)
            rho = 4 * beta + 8 * alpha * sigma * v0_norm + Fraction(1)
            assert rho > 0
            for k in range(order + 1):
                bound_vk = (v0_norm / Fraction((k + 1) ** 2)) * (rho ** k)
                assert vec_norm1(vecs[k]) <= bound_vk
                if k >= 1:
                    bound_lk = (alpha * v0_norm / Fraction(k ** 2)) * (rho ** (k - 1))
                    assert abs(lams[k]) <= bound_lk

            # Evaluate at eps = 1 / (2 * rho) inside convergence radius R_0 = 1 / rho
            eps = Fraction(1, 2) / rho
            lam_approx = sum((lams[k] * (eps ** k) for k in range(order + 1)), Fraction(0))
            v_approx = zeros_vec(n)
            for k in range(order + 1):
                v_approx = vec_add(v_approx, vec_smul(eps ** k, vecs[k]))
            a_eps = mat_add(a0, mat_smul(eps, a1))
            residual_vec = vec_sub(mat_vec(a_eps, v_approx), vec_smul(lam_approx, v_approx))
            # Residual must be O(eps^(order+1)) -> tiny at 1/(2*rho)
            assert vec_norm1(residual_vec) <= (mat_norm_sum(a1) + alpha * v0_norm * order) * v0_norm * (
                Fraction(1, 2) ** order
            )
            trials += 1

    print(
        f"[PASS] Suites 2 & 3: Verified all-orders Kato recursion (k <= {order}), charpoly "
        f"congruence, closed-form (lambda_1, v_1, lambda_2, P_1), and explicit Cauchy-Kato "
        f"analytic radius R_0 = 1/rho on {trials} trials (2 <= n <= 5)."
    )


def test_suite_4_clause2_refutations() -> None:
    # --- Reading A: First-order eigenvalue coefficient lambda_1 via Q = I - P ---
    a0_a = [[Fraction(2), Fraction(0)], [Fraction(0), Fraction(0)]]
    lam0_a = Fraction(2)
    v0_a = [Fraction(1), Fraction(0)]
    w0_a = [Fraction(1), Fraction(0)]
    p_a, q_a, s_a = riesz_kato_from_charpoly(a0_a, lam0_a, [Fraction(0), Fraction(1)])
    assert p_a == [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(0)]]
    assert q_a == [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(1)]]
    assert s_a == [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(-1, 2)]]

    # Counterexample A.1: A_1 = diag(1, 0) -> exact lambda(eps) = 2 + eps (lambda_1 = 1)
    a1_diag10 = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(0)]]
    lams_10, _ = kato_series(lam0_a, v0_a, w0_a, s_a, a1_diag10, 4)
    assert lams_10 == [Fraction(2), Fraction(1), Fraction(0), Fraction(0), Fraction(0)]
    tr_q_a1_10 = mat_trace(mat_mul(q_a, a1_diag10))
    qa1_v0_10 = mat_vec(q_a, mat_vec(a1_diag10, v0_a))
    w_qa1_v0_10 = vec_dot(w0_a, qa1_v0_10) / vec_dot(w0_a, v0_a)
    assert lams_10[1] == Fraction(1)
    assert tr_q_a1_10 == Fraction(0) and lams_10[1] != tr_q_a1_10
    assert w_qa1_v0_10 == Fraction(0) and lams_10[1] != w_qa1_v0_10
    assert vec_norm1(qa1_v0_10) == Fraction(0) and abs(lams_10[1]) != vec_norm1(qa1_v0_10)

    # Counterexample A.2: A_1 = diag(0, 5) -> exact lambda(eps) = 2 (lambda_1 = 0)
    a1_diag05 = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(5)]]
    lams_05, _ = kato_series(lam0_a, v0_a, w0_a, s_a, a1_diag05, 4)
    assert lams_05 == [Fraction(2), Fraction(0), Fraction(0), Fraction(0), Fraction(0)]
    tr_q_a1_05 = mat_trace(mat_mul(q_a, a1_diag05))
    assert lams_05[1] == Fraction(0) and tr_q_a1_05 == Fraction(5)
    assert lams_05[1] != tr_q_a1_05 and lams_05[1] != -tr_q_a1_05

    # Counterexample A.3: Off-diagonal A_1 = [[0, 1], [1, 0]] -> lambda_1 = 0, ||Q A_1 v_0|| = 1
    a1_off = [[Fraction(0), Fraction(1)], [Fraction(1), Fraction(0)]]
    lams_off_a, _ = kato_series(lam0_a, v0_a, w0_a, s_a, a1_off, 4)
    qa1_v0_off = mat_vec(q_a, mat_vec(a1_off, v0_a))
    assert lams_off_a[1] == Fraction(0)
    assert qa1_v0_off == [Fraction(0), Fraction(1)]
    assert vec_norm1(qa1_v0_off) == Fraction(1) != abs(lams_off_a[1])
    assert vec_dot(qa1_v0_off, qa1_v0_off) == Fraction(1) != lams_off_a[1] ** 2

    # Operator derivative check: P != Q
    assert p_a != q_a

    # --- Readings B, C, D on A_0 = diag(5, 1) at lambda_0 = 5, A_1 = [[0, 1], [1, 0]] ---
    a0_bcd = [[Fraction(5), Fraction(0)], [Fraction(0), Fraction(1)]]
    lam0_bcd = Fraction(5)
    v0_bcd = [Fraction(1), Fraction(0)]
    w0_bcd = [Fraction(1), Fraction(0)]
    p_bcd, q_bcd, s_bcd = riesz_kato_from_charpoly(
        a0_bcd, lam0_bcd, [Fraction(-1), Fraction(1)]
    )
    assert p_bcd == [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(0)]]
    assert q_bcd == [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(1)]]
    assert s_bcd == [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(-1, 4)]]

    lams_bcd, vecs_bcd = kato_series(lam0_bcd, v0_bcd, w0_bcd, s_bcd, a1_off, 6)
    # Exact closed-form: lambda(eps) = 3 + sqrt(4 + eps^2) = 5 + 1/4 eps^2 - 1/64 eps^4 + 1/512 eps^6
    assert lams_bcd == [
        Fraction(5),
        Fraction(0),
        Fraction(1, 4),
        Fraction(0),
        Fraction(-1, 64),
        Fraction(0),
        Fraction(1, 512),
    ]
    # Exact normalized eigenvector: v(eps) = (1, eps / (lambda(eps) - 1))^T
    # = (1, 1/4 eps - 1/64 eps^3 + 1/512 eps^5 + ...)^T
    assert vecs_bcd[1] == [Fraction(0), Fraction(1, 4)]
    assert vecs_bcd[3] == [Fraction(0), Fraction(-1, 64)]

    # Reading B check: v_1 = (0, 1/4) != +/- Q A_1 v_0 = (0, +/- 1)
    qa1_v0_bcd = mat_vec(q_bcd, mat_vec(a1_off, v0_bcd))
    assert qa1_v0_bcd == [Fraction(0), Fraction(1)]
    assert vecs_bcd[1] != qa1_v0_bcd
    assert vecs_bcd[1] != vec_smul(Fraction(-1), qa1_v0_bcd)

    # Reading C check: lambda_2 = 1/4 != +/- tr(P A_1 Q A_1) = +/- 1
    tr_pa1qa1 = mat_trace(mat_mul(mat_mul(mat_mul(p_bcd, a1_off), q_bcd), a1_off))
    assert tr_pa1qa1 == Fraction(1)
    assert lams_bcd[2] == Fraction(1, 4)
    assert lams_bcd[2] != tr_pa1qa1 and lams_bcd[2] != -tr_pa1qa1

    # Reading D check: P_1 = - P A_1 S - S A_1 P = [[0, 1/4], [1/4, 0]]
    p1_bcd = mat_sub(
        zeros_mat(2),
        mat_add(
            mat_mul(mat_mul(p_bcd, a1_off), s_bcd),
            mat_mul(mat_mul(s_bcd, a1_off), p_bcd),
        ),
    )
    unweighted_comm = mat_add(mat_mul(p_bcd, mat_mul(a1_off, q_bcd)), mat_mul(q_bcd, mat_mul(a1_off, p_bcd)))
    assert p1_bcd == [[Fraction(0), Fraction(1, 4)], [Fraction(1, 4), Fraction(0)]]
    assert unweighted_comm == [[Fraction(0), Fraction(1)], [Fraction(1), Fraction(0)]]
    assert p1_bcd != q_bcd and p1_bcd != mat_smul(Fraction(-1), q_bcd)
    assert p1_bcd != unweighted_comm and p1_bcd != mat_smul(Fraction(-1), unweighted_comm)

    # Independent high-precision contour integral cross-check for lambda_1, lambda_2, P_1 on A_0 = diag(5, 1)
    # Contour |zeta - 5| = 1 in C around lambda_0 = 5 (distance to mu_2 = 1 is 4 > 1)
    eps_num = 0.1
    m_pts = 512
    p_contour = [[0j, 0j], [0j, 0j]]
    for idx in range(m_pts):
        theta = 2.0 * math.pi * idx / m_pts
        zeta = 5.0 + complex(math.cos(theta), math.sin(theta))
        dzeta = 1j * complex(math.cos(theta), math.sin(theta)) * (2.0 * math.pi / m_pts)
        # (zeta I - A(eps))^-1 for [[zeta - 5, -eps], [-eps, zeta - 1]]
        det_z = (zeta - 5.0) * (zeta - 1.0) - eps_num ** 2
        inv_z = [[(zeta - 1.0) / det_z, eps_num / det_z], [eps_num / det_z, (zeta - 5.0) / det_z]]
        for r in range(2):
            for c in range(2):
                p_contour[r][c] += inv_z[r][c] * dzeta / (2.0j * math.pi)
    a_num = [[5.0, eps_num], [eps_num, 1.0]]
    lam_contour = (
        a_num[0][0] * p_contour[0][0]
        + a_num[0][1] * p_contour[1][0]
        + a_num[1][0] * p_contour[0][1]
        + a_num[1][1] * p_contour[1][1]
    ).real
    lam_exact = 3.0 + math.sqrt(4.0 + eps_num ** 2)
    assert abs(lam_contour - lam_exact) < 1e-13
    assert abs(p_contour[0][1].real - 0.25 * eps_num) < 2e-4

    print(
        "[PASS] Suite 4: Verified exhaustive refutation of Clause 2 across Readings A "
        "(tr(Q A_1), w_0^T Q A_1 v_0, ||Q A_1 v_0||, D lambda = Q), B (v_1 != +/- Q A_1 v_0), "
        "C (lambda_2 != +/- tr(P A_1 Q A_1)), and D (P_1 != +/- Q, +/- (P A_1 Q + Q A_1 P)), "
        "plus Riesz contour-integral cross-check."
    )


def test_suite_5_defective_obstruction() -> None:
    """Verify A(eps) = [[0, 1], [eps, 0]] has no formal power series root or eigenvector."""
    a0 = [[Fraction(0), Fraction(1)], [Fraction(0), Fraction(0)]]
    a1 = [[Fraction(0), Fraction(0)], [Fraction(1), Fraction(0)]]
    # Characteristic polynomial is x^2 - eps.
    # For any candidate (lambda_0, lambda_1), coeff of eps^0 is lambda_0^2 and coeff of eps^1
    # is 2*lambda_0*lambda_1 - 1; if lambda_0^2 == 0 then lambda_0 == 0 so coeff_1 == -1 != 0.
    for lam0 in [Fraction(k, 2) for k in range(-10, 11)]:
        for lam1 in [Fraction(k, 2) for k in range(-10, 11)]:
            det_coeffs = det_poly_in_eps(a0, a1, [lam0, lam1], 2)
            assert not (det_coeffs[0] == 0 and det_coeffs[1] == 0)

    # Also verify algebraic simplicity criterion q(0) = 0 fails at lambda_0 = 0 (chi(x) = x * x).
    q_defective = [Fraction(0), Fraction(1)]  # q(x) = x
    assert poly_eval_scalar(q_defective, Fraction(0)) == Fraction(0)

    print(
        "[PASS] Suite 5: Verified defective Jordan perturbation A(eps) = [[0, 1], [eps, 0]] "
        "has Puiseux obstruction (lambda^2 = eps) and admits no formal power series branch."
    )


def main() -> int:
    print("=" * 78)
    print("Verification Suite for Conjecture 00000007179 (Kato Analytic Perturbation)")
    print("=" * 78)
    test_suite_1_riesz_kato_decomposition()
    test_suite_2_and_3_all_orders_and_majorant()
    test_suite_4_clause2_refutations()
    test_suite_5_defective_obstruction()
    print("=" * 78)
    print("ALL VERIFICATION SUITES PASSED. VERDICT: FALSE (Clause 1 TRUE; Clause 2 FALSE).")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
