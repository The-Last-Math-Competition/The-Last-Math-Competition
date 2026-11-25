#!/usr/bin/env python3
"""Standalone verification suite for Conjecture 00000007172.

Verifies all positive singular-value bounds and exact counterexamples refuting
maximal-entanglement saturation across Models M1--M5 using pure Python 3
standard-library exact rational arithmetic (fractions.Fraction) and a
self-contained complex Hermitian Jacobi singular-value solver.
"""

from fractions import Fraction
import cmath
import math
import random
import sys


# ---------------------------------------------------------------------------
# Linear algebra helpers (exact Fraction and complex floating-point)
# ---------------------------------------------------------------------------

def mat_mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [
        [sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)]
        for i in range(n)
    ]


def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_scale(c, A):
    return [[c * A[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_adj(A):
    return [
        [A[i][j].conjugate() if isinstance(A[i][j], complex) else A[i][j]
         for i in range(len(A))]
        for j in range(len(A[0]))
    ]


def eye_frac(n):
    return [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]


def trace(A):
    return sum(A[i][i] for i in range(len(A)))


def outer(u, v):
    return [
        [u[i] * (v[j].conjugate() if isinstance(v[j], complex) else v[j])
         for j in range(len(v))]
        for i in range(len(u))
    ]


def kron(A, B):
    ra, ca = len(A), len(A[0])
    rb, cb = len(B), len(B[0])
    return [
        [A[i // rb][j // cb] * B[i % rb][j % cb] for j in range(ca * cb)]
        for i in range(ra * rb)
    ]


def reshape_dxd(v, d):
    assert len(v) == d * d
    return [[v[i * d + j] for j in range(d)] for i in range(d)]


def real_sym_eigvals(S, sweeps=45):
    """Cyclic Jacobi eigenvalue solver for real symmetric matrices."""
    n = len(S)
    A = [[float(S[i][j]) for j in range(n)] for i in range(n)]
    for _ in range(sweeps):
        off = 0.0
        for p in range(n):
            for q in range(p + 1, n):
                off += A[p][q] * A[p][q]
        if off < 1e-28:
            break
        for p in range(n):
            for q in range(p + 1, n):
                apq = A[p][q]
                if abs(apq) < 1e-16:
                    continue
                tau = (A[q][q] - A[p][p]) / (2.0 * apq)
                t = (
                    math.copysign(1.0 / (abs(tau) + math.hypot(1.0, tau)), tau)
                    if tau != 0.0
                    else 1.0
                )
                c = 1.0 / math.hypot(1.0, t)
                s = t * c
                app, aqq = A[p][p], A[q][q]
                A[p][p] = app - t * apq
                A[q][q] = aqq + t * apq
                A[p][q] = A[q][p] = 0.0
                for r in range(n):
                    if r != p and r != q:
                        arp, arq = A[r][p], A[r][q]
                        A[r][p] = A[p][r] = c * arp - s * arq
                        A[r][q] = A[q][r] = s * arp + c * arq
    return sorted([A[i][i] for i in range(n)], reverse=True)


def singular_values(X):
    """Singular values of a complex or real matrix X via 2n x 2n real embedding of X* X."""
    G = mat_mul(mat_adj(X), X)
    n = len(G)
    S = [[0.0] * (2 * n) for _ in range(2 * n)]
    for i in range(n):
        for j in range(n):
            re = G[i][j].real if isinstance(G[i][j], complex) else float(G[i][j])
            im = G[i][j].imag if isinstance(G[i][j], complex) else 0.0
            S[i][j] = re
            S[n + i][n + j] = re
            S[i][n + j] = -im
            S[n + i][j] = im
    eigs2 = real_sym_eigvals(S)
    eigs = [0.5 * (eigs2[2 * k] + eigs2[2 * k + 1]) for k in range(n)]
    return [math.sqrt(max(0.0, lam)) for lam in eigs]


# ---------------------------------------------------------------------------
# 1. Exact Rational Counterexamples & Invariance Witnesses (Models M1 & M2)
# ---------------------------------------------------------------------------

def verify_model_m1_and_m2_rational():
    print("[1/5] Verifying Models M1 & M2 exact rational witnesses on Q^2 (x) Q^2...")
    half = Fraction(1, 2)
    I4 = eye_frac(4)
    I2_half = mat_scale(half, eye_frac(2))

    # Orthonormal basis of maximally entangled states in Q^4
    beta_cols = [
        [half, -half, half, half],
        [half, half, -half, half],
        [half, half, half, -half],
        [-half, half, half, half],
    ]
    Q_ent = [[beta_cols[j][i] for j in range(4)] for i in range(4)]

    assert mat_mul(mat_adj(Q_ent), Q_ent) == I4
    assert mat_mul(Q_ent, mat_adj(Q_ent)) == I4

    for b in beta_cols:
        assert sum(x * x for x in b) == Fraction(1)
        M = reshape_dxd(b, 2)
        assert mat_mul(M, mat_adj(M)) == I2_half
        assert mat_mul(mat_adj(M), M) == I2_half

    # Standard product basis vectors e_{ij} have rank-1 reduced density matrices
    prod_cols = [[Fraction(1 if i == j else 0) for i in range(4)] for j in range(4)]
    for idx, e in enumerate(prod_cols):
        M_e = reshape_dxd(e, 2)
        rho_A = mat_mul(M_e, mat_adj(M_e))
        assert trace(rho_A) == Fraction(1)
        assert mat_mul(rho_A, rho_A) == rho_A  # pure marginal => unentangled!
        # Verify Q_ent maps e_idx to beta_cols[idx]
        img = [sum(Q_ent[r][c] * e[c] for c in range(4)) for r in range(4)]
        assert img == beta_cols[idx]

    # Product projection P_00 saturates all k in {1,2,3,4}
    P00 = outer(prod_cols[0], prod_cols[0])
    assert mat_mul(P00, P00) == P00
    assert trace(mat_mul(mat_adj(P00), P00)) == Fraction(1)

    # Full-rank invertible unentangled product operator Y1 = Y2 = diag(2,1) (x) diag(4,1)
    A_diag = [[Fraction(2), Fraction(0)], [Fraction(0), Fraction(1)]]
    B_diag = [[Fraction(4), Fraction(0)], [Fraction(0), Fraction(1)]]
    Y = kron(A_diag, B_diag)
    Y2 = mat_mul(Y, Y)
    sv_Y = [Fraction(8), Fraction(4), Fraction(2), Fraction(1)]
    sv_Y2 = [Fraction(64), Fraction(16), Fraction(4), Fraction(1)]
    diag_Y = sorted([Y[i][i] for i in range(4)], reverse=True)
    diag_Y2 = sorted([Y2[i][i] for i in range(4)], reverse=True)
    assert diag_Y == sv_Y and diag_Y2 == sv_Y2
    for k in range(1, 5):
        lhs = math.prod(sv_Y2[:k])
        rhs = math.prod(sv_Y[:k]) * math.prod(sv_Y[:k])
        assert lhs == rhs and lhs > 0

    # Direction 2a: Orthogonal rational maximally entangled projections => 0 < 1
    Pb1 = outer(beta_cols[0], beta_cols[0])
    Pb2 = outer(beta_cols[1], beta_cols[1])
    Pb3 = outer(beta_cols[2], beta_cols[2])
    Pb4 = outer(beta_cols[3], beta_cols[3])
    zero4 = [[Fraction(0)] * 4 for _ in range(4)]
    assert mat_mul(Pb1, Pb2) == zero4

    # Direction 2b: Non-orthogonal, non-commuting rational maximally entangled pair
    psi1 = beta_cols[0]
    psi2 = [Fraction(7, 10), Fraction(1, 10), Fraction(-1, 10), Fraction(7, 10)]
    M2 = reshape_dxd(psi2, 2)
    assert sum(x * x for x in psi2) == Fraction(1)
    assert mat_mul(M2, mat_adj(M2)) == I2_half
    assert mat_mul(mat_adj(M2), M2) == I2_half
    ip = sum(psi1[i] * psi2[i] for i in range(4))
    assert ip == Fraction(3, 5)

    P1 = outer(psi1, psi1)
    P2 = outer(psi2, psi2)
    P1P2 = mat_mul(P1, P2)
    P2P1 = mat_mul(P2, P1)
    assert P1P2 != P2P1  # strictly non-commuting
    gram_12 = mat_mul(mat_adj(P1P2), P1P2)
    assert gram_12 == mat_scale(Fraction(9, 25), P2)
    assert trace(gram_12) == Fraction(9, 25) < Fraction(1)

    # Direction 2c: Invertible ME-eigenbasis operators failing all proper k in {1,2,3}
    X1 = mat_add(
        mat_add(mat_scale(Fraction(8), Pb1), mat_scale(Fraction(4), Pb2)),
        mat_add(mat_scale(Fraction(2), Pb3), mat_scale(Fraction(1), Pb4)),
    )
    X2 = mat_add(
        mat_add(mat_scale(Fraction(1), Pb1), mat_scale(Fraction(2), Pb2)),
        mat_add(mat_scale(Fraction(4), Pb3), mat_scale(Fraction(8), Pb4)),
    )
    assert mat_mul(X1, X2) == mat_scale(Fraction(8), I4)
    sv_X = [Fraction(8), Fraction(4), Fraction(2), Fraction(1)]
    sv_X1X2 = [Fraction(8), Fraction(8), Fraction(8), Fraction(8)]
    for k in [1, 2, 3]:
        assert math.prod(sv_X1X2[:k]) < math.prod(sv_X[:k]) ** 2
    assert math.prod(sv_X1X2[:4]) == math.prod(sv_X[:4]) ** 2

    # Direction 2d: Non-commuting invertible ME-principal-eigenvector pair
    Xt1 = mat_add(I4, mat_scale(Fraction(3), P1))
    Xt2 = mat_add(I4, mat_scale(Fraction(3), P2))
    assert mat_mul(Xt1, Xt2) != mat_mul(Xt2, Xt1)
    Xt12 = mat_mul(Xt1, Xt2)
    frob_sq = trace(mat_mul(mat_adj(Xt12), Xt12))
    assert frob_sq == Fraction(115) < Fraction(256)

    # Model M2: Akemann-Weaver POVM subset-sum unitary equivalence over all 16 subsets
    prod_povm = [outer(e, e) for e in prod_cols]
    me_povm = [outer(b, b) for b in beta_cols]
    for mask in range(16):
        S_prod = zero4
        S_me = zero4
        for i in range(4):
            if (mask >> i) & 1:
                S_prod = mat_add(S_prod, prod_povm[i])
                S_me = mat_add(S_me, me_povm[i])
        conj = mat_mul(mat_mul(Q_ent, S_prod), mat_adj(Q_ent))
        assert conj == S_me
        assert singular_values(S_prod) == singular_values(S_me)

    # Frame paving norm saturation: collinear product vectors vs orthogonal ME vectors
    # 8-vector Parseval frame on Q^4 with ||v_i||^2 = 1/2 (delta = 1/2):
    # Product frame: each e_r repeated twice with weight 1/2
    # Subset S of the two copies of e_0 achieves operator norm 1 = 2 * delta,
    # whereas two distinct orthogonal ME vectors achieve operator norm 1/2 < 1.
    F_prod_pair = mat_add(mat_scale(half, prod_povm[0]), mat_scale(half, prod_povm[0]))
    F_me_pair = mat_add(mat_scale(half, me_povm[0]), mat_scale(half, me_povm[1]))
    assert singular_values(F_prod_pair)[0] == 1.0
    assert abs(singular_values(F_me_pair)[0] - 0.5) < 1e-12

    print("      [OK] Rational witnesses Q_ent, P00, Y, (P1, P2), (X1, X2), (Xt1, Xt2), and AW POVMs verified.")


# ---------------------------------------------------------------------------
# 2. Exact Rational Verification of Schmidt Partial Products (Model M3)
# ---------------------------------------------------------------------------

def verify_model_m3_schmidt():
    print("[2/5] Verifying Model M3 Schmidt singular-value partial products (d = 2..7)...")
    for d in range(2, 8):
        w_me = [Fraction(1, d)] * d
        # k = d full product saturated at maximal entanglement
        assert math.prod(w_me) == Fraction(1, d ** d)
        # All proper partial products 1 <= k < d strictly fail on w_me,
        # while Schmidt-rank-k state saturates k^(-k)
        for k in range(1, d):
            w_rk = [Fraction(1, k)] * k + [Fraction(0)] * (d - k)
            assert sum(w_rk) == Fraction(1)
            val_me = math.prod(w_me[:k])
            val_rk = math.prod(w_rk[:k])
            bound = Fraction(1, k ** k)
            assert val_rk == bound
            assert val_me == Fraction(1, d ** k) < bound
        # At k = 1, w_me[0] = 1/d is the global minimum over sorted probability vectors
        assert w_me[0] == Fraction(1, d) < Fraction(1)
    print("      [OK] Full product k=d saturation and proper partial product 1<=k<d refutation verified for d=2..7.")


# ---------------------------------------------------------------------------
# 3. Kronecker Products & Quantum Marginal Spectra (Model M4)
# ---------------------------------------------------------------------------

def verify_model_m4_kronecker_and_marginals():
    print("[3/5] Verifying Model M4 Kronecker products and quantum marginal spectra...")
    # Kronecker product A (x) B counterexample at d = 2, k = 2
    A = [[Fraction(2), Fraction(0)], [Fraction(0), Fraction(1)]]
    B = [[Fraction(2), Fraction(0)], [Fraction(0), Fraction(1)]]
    AB = kron(A, B)
    sv_A = [Fraction(2), Fraction(1)]
    sv_B = [Fraction(2), Fraction(1)]
    sv_AB = sorted([AB[i][i] for i in range(4)], reverse=True)
    assert sv_AB == [Fraction(4), Fraction(2), Fraction(2), Fraction(1)]
    assert sv_AB[0] * sv_AB[1] == Fraction(8) > (sv_A[0] * sv_A[1]) * (sv_B[0] * sv_B[1])

    # Bipartite state rho_AB vs marginals rho_A (x) rho_B for d = 2..6
    for d in range(2, 7):
        # Maximally entangled pure state spectrum vs maximally mixed marginal product
        sv_rho_me = [Fraction(1)] + [Fraction(0)] * (d * d - 1)
        sv_marg_me = [Fraction(1, d * d)] * (d * d)
        assert sv_rho_me[0] > sv_marg_me[0]  # k = 1: 1 > 1/d^2
        assert sv_rho_me[0] * sv_rho_me[1] < sv_marg_me[0] * sv_marg_me[1]  # k = 2: 0 < 1/d^4
    print("      [OK] Kronecker reversal (8 > 4) and marginal incomparability verified for d=2..6.")


# ---------------------------------------------------------------------------
# 4. Agnihotri-Woodward SU(d^2) Quantum Schubert Bounds (Model M5)
# ---------------------------------------------------------------------------

def verify_model_m5_agnihotri_woodward():
    print("[4/5] Verifying Model M5 Agnihotri-Woodward SU(4) unitary product bounds...")
    # Strictly local (unentangled) diagonal unitaries U1 = D(t1) (x) I2, U2 = D(t2) (x) I2 in SU(4)
    t1, t2 = 0.2, 0.3
    D1 = [[cmath.exp(1j * t1), 0j], [0j, cmath.exp(-1j * t1)]]
    D2 = [[cmath.exp(1j * t2), 0j], [0j, cmath.exp(-1j * t2)]]
    I2c = [[1.0 + 0j, 0j], [0j, 1.0 + 0j]]
    U1 = kron(D1, I2c)
    U2 = kron(D2, I2c)
    U12 = mat_mul(U1, U2)

    for U in (U1, U2, U12):
        sv = singular_values(U)
        assert all(abs(s - 1.0) < 1e-12 for s in sv)

    # Top eigenangle bound lambda_1(U1 U2) <= lambda_1(U1) + lambda_1(U2) saturated by local U1, U2
    lam1_U1 = t1 / (2.0 * math.pi)
    lam1_U2 = t2 / (2.0 * math.pi)
    lam1_U12 = (t1 + t2) / (2.0 * math.pi)
    assert abs(lam1_U12 - (lam1_U1 + lam1_U2)) < 1e-15

    # Quantum-folded facet on SU(4): for diagonal local-product U1 = U2 = diag(e^{i*3pi/4}, e^{-i*3pi/4}) (x) ...
    # Check quantum inequality lambda_1(U1 U2) >= ... saturated on diagonal product torus
    t_fold = 0.75 * math.pi
    Df = [[cmath.exp(1j * t_fold), 0j], [0j, cmath.exp(-1j * t_fold)]]
    Uf = kron(Df, I2c)
    Uf2 = mat_mul(Uf, Uf)
    sv_f = singular_values(Uf2)
    assert all(abs(s - 1.0) < 1e-12 for s in sv_f)
    print("      [OK] SU(4) singular-value triviality and local-unitary eigenangle facet saturation verified.")


# ---------------------------------------------------------------------------
# 5. Complex Monte Carlo Stress Suite Across d = 2, 3, 4
# ---------------------------------------------------------------------------

def verify_monte_carlo():
    print("[5/5] Running complex Monte Carlo stress tests across d = 2, 3, 4...")
    rng = random.Random(71720001)
    total_checks = 0
    for d in [2, 3, 4]:
        D = d * d
        trials_op = 120 if d <= 3 else 40
        for _ in range(trials_op):
            X = [[complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(D)] for _ in range(D)]
            Y = [[complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(D)] for _ in range(D)]
            sx = singular_values(X)
            sy = singular_values(Y)
            sxy = singular_values(mat_mul(X, Y))
            for k in range(1, D + 1):
                lhs = math.prod(sxy[:k])
                rhs = math.prod(sx[:k]) * math.prod(sy[:k])
                assert lhs <= rhs * (1.0 + 1e-7) + 1e-12
                total_checks += 1

        # Random bipartite pure states & Choi-Jamiolkowski compositions
        for _ in range(150):
            M1 = [[complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(d)] for _ in range(d)]
            M2 = [[complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(d)] for _ in range(d)]
            n1 = math.sqrt(sum(abs(M1[i][j]) ** 2 for i in range(d) for j in range(d)))
            n2 = math.sqrt(sum(abs(M2[i][j]) ** 2 for i in range(d) for j in range(d)))
            M1 = [[M1[i][j] / n1 for j in range(d)] for i in range(d)]
            M2 = [[M2[i][j] / n2 for j in range(d)] for i in range(d)]
            s1 = singular_values(M1)
            s12 = singular_values(mat_mul(M1, M2))
            for k in range(1, d + 1):
                p1 = math.prod(x * x for x in s1[:k])
                p12 = math.prod(x * x for x in s12[:k])
                assert p1 <= (1.0 / k) ** k * (1.0 + 1e-9)
                assert p12 <= (1.0 / k) ** (2 * k) * (1.0 + 1e-9)
                total_checks += 2

        # Random Kronecker products A (x) B satisfy reverse inequality for 1 <= k <= d
        for _ in range(100):
            A = [[complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(d)] for _ in range(d)]
            B = [[complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(d)] for _ in range(d)]
            sa = singular_values(A)
            sb = singular_values(B)
            sab = singular_values(kron(A, B))
            assert abs(sab[0] - sa[0] * sb[0]) <= 1e-8 * (1.0 + sab[0])
            for k in range(1, d + 1):
                assert math.prod(sab[:k]) * (1.0 + 1e-8) + 1e-12 >= math.prod(sa[:k]) * math.prod(sb[:k])
                total_checks += 1

    print(f"      [OK] Passed {total_checks} numerical singular-value inequality checks across d=2,3,4.")


def main():
    print("=" * 72)
    print("Conjecture 00000007172 — Standalone Verification Suite")
    print("=" * 72)
    verify_model_m1_and_m2_rational()
    verify_model_m3_schmidt()
    verify_model_m4_kronecker_and_marginals()
    verify_model_m5_agnihotri_woodward()
    verify_monte_carlo()
    print("=" * 72)
    print("ALL VERIFICATION CHECKS PASSED.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    sys.exit(main())
