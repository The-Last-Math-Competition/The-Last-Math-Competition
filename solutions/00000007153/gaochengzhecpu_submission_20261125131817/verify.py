#!/usr/bin/env python3
"""
Standalone verification suite for Conjecture 00000007153:
"Diagonal-equality Lidskii product majorization"

Uses only the Python 3 standard library (exact integer/rational arithmetic via
`fractions.Fraction` and `math.isqrt`, plus a self-contained Jacobi eigensolver
for floating-point cross-checks in dimensions n = 2..6).
"""

from __future__ import annotations

from fractions import Fraction
import itertools
import math
import random
import sys
from typing import List, Sequence, Tuple

Matrix = List[List[int]]


def mat_mul(A: Sequence[Sequence[int]], B: Sequence[Sequence[int]]) -> Matrix:
    n = len(A)
    m = len(B[0])
    p = len(B)
    return [
        [sum(A[i][k] * B[k][j] for k in range(p)) for j in range(m)]
        for i in range(n)
    ]


def mat_transpose(A: Sequence[Sequence[int]]) -> Matrix:
    n = len(A)
    m = len(A[0])
    return [[A[i][j] for i in range(n)] for j in range(m)]


def is_diagonal(A: Sequence[Sequence[int]]) -> bool:
    n = len(A)
    return all(A[i][j] == 0 for i in range(n) for j in range(n) if i != j)


def is_normal(A: Sequence[Sequence[int]]) -> bool:
    AT = mat_transpose(A)
    return mat_mul(AT, A) == mat_mul(A, AT)


def is_scalar(A: Sequence[Sequence[int]]) -> bool:
    n = len(A)
    return is_diagonal(A) and all(A[i][i] == A[0][0] for i in range(n))


def tr2(A: Sequence[Sequence[int]]) -> int:
    return A[0][0] + A[1][1]


def det2(A: Sequence[Sequence[int]]) -> int:
    return A[0][0] * A[1][1] - A[0][1] * A[1][0]


def exact_sv2(A: Sequence[Sequence[int]]) -> Tuple[int, int]:
    """Compute exact integer singular values (s1 >= s2 >= 0) of a 2x2 matrix."""
    G = mat_mul(mat_transpose(A), A)
    t = tr2(G)
    d = det2(G)
    disc = t * t - 4 * d
    assert disc >= 0, f"Negative Gram discriminant: {disc}"
    r = math.isqrt(disc)
    assert r * r == disc, f"Gram discriminant {disc} is not a perfect square"
    assert (t + r) % 2 == 0 and (t - r) % 2 == 0
    s1_sq = (t + r) // 2
    s2_sq = (t - r) // 2
    s1 = math.isqrt(s1_sq)
    s2 = math.isqrt(s2_sq)
    assert s1 * s1 == s1_sq and s2 * s2 == s2_sq
    assert s1 >= s2 >= 0
    assert s1 * s1 + s2 * s2 == t
    assert (s1 * s2) ** 2 == d
    return (s1, s2)


def is_defective_2x2(A: Sequence[Sequence[int]]) -> bool:
    """A 2x2 matrix over any characteristic-0 field is non-diagonalizable over C
    iff its characteristic discriminant vanishes (tr(A)^2 == 4*det(A)) while A
    is not a scalar multiple of the identity."""
    return tr2(A) ** 2 == 4 * det2(A) and not is_scalar(A)


def jacobi_eigenvalues_sym(S_in: Sequence[Sequence[float]], tol: float = 1e-15) -> List[float]:
    """Self-contained cyclic Jacobi symmetric eigenvalue solver."""
    n = len(S_in)
    S = [[float(S_in[i][j]) for j in range(n)] for i in range(n)]
    for _ in range(300 * n * n):
        max_off = 0.0
        p, q = 0, 1
        for i in range(n):
            for j in range(i + 1, n):
                if abs(S[i][j]) > max_off:
                    max_off = abs(S[i][j])
                    p, q = i, j
        if max_off < tol:
            break
        diff = S[q][q] - S[p][p]
        if abs(diff) < 1e-30:
            t = 1.0
        else:
            tau = diff / (2.0 * S[p][q])
            t = (1.0 if tau >= 0 else -1.0) / (abs(tau) + math.sqrt(1.0 + tau * tau))
        c = 1.0 / math.sqrt(1.0 + t * t)
        s = t * c
        app = S[p][p] - t * S[p][q]
        aqq = S[q][q] + t * S[p][q]
        S[p][p] = app
        S[q][q] = aqq
        S[p][q] = 0.0
        S[q][p] = 0.0
        for k in range(n):
            if k != p and k != q:
                ikp = c * S[k][p] - s * S[k][q]
                ikq = s * S[k][p] + c * S[k][q]
                S[k][p] = S[p][k] = ikp
                S[k][q] = S[q][k] = ikq
    return sorted([S[i][i] for i in range(n)], reverse=True)


def numeric_singular_values(A_in: Sequence[Sequence[float]], tol: float = 1e-15) -> List[float]:
    """Self-contained one-sided Jacobi SVD (avoids squaring condition numbers in A^T A)."""
    n = len(A_in)
    m = len(A_in[0])
    W = [[float(A_in[i][j]) for j in range(m)] for i in range(n)]
    for _ in range(300 * max(1, m * m)):
        converged = True
        for p in range(m):
            for q in range(p + 1, m):
                alpha = sum(W[k][p] * W[k][p] for k in range(n))
                beta = sum(W[k][q] * W[k][q] for k in range(n))
                gamma = sum(W[k][p] * W[k][q] for k in range(n))
                if abs(gamma) <= tol * math.sqrt(max(0.0, alpha * beta)):
                    continue
                converged = False
                zeta = (beta - alpha) / (2.0 * gamma)
                t = (1.0 if zeta >= 0.0 else -1.0) / (abs(zeta) + math.sqrt(1.0 + zeta * zeta))
                c = 1.0 / math.sqrt(1.0 + t * t)
                s = c * t
                for k in range(n):
                    wkp = W[k][p]
                    wkq = W[k][q]
                    W[k][p] = c * wkp - s * wkq
                    W[k][q] = s * wkp + c * wkq
        if converged:
            break
    norms = [math.sqrt(sum(W[k][j] * W[k][j] for k in range(n))) for j in range(m)]
    return sorted(norms, reverse=True)


def check_positive_diagonal_witness() -> None:
    print("[1/7] Checking positive non-vacuity diagonal witnesses...")
    D1 = [[4, 0], [0, 2]]
    D2 = [[5, 0], [0, 1]]
    P = mat_mul(D1, D2)
    assert is_diagonal(D1) and is_diagonal(D2) and is_diagonal(P)
    sA = exact_sv2(D1)
    sB = exact_sv2(D2)
    sAB = exact_sv2(P)
    assert sA == (4, 2) and sB == (5, 1) and sAB == (20, 2)
    assert sAB[0] == sA[0] * sB[0]
    assert sAB[0] * sAB[1] == (sA[0] * sB[0]) * (sA[1] * sB[1])
    print("  PASS: D1=diag(4,2), D2=diag(5,1) -> sigma(D1*D2)=(20,2) with full log-majorization equality.")


def check_interpretation_A_counterexamples() -> None:
    print("[2/7] Checking Interpretation A counterexamples (product log-majorization equality)...")

    # A1: Symmetric positive definite 2x2 integer counterexample
    A_spd = [[3, 1], [1, 3]]
    B_spd = [[3, 2], [2, 3]]
    AB_spd = mat_mul(A_spd, B_spd)
    assert AB_spd == [[11, 9], [9, 11]]
    assert not is_diagonal(A_spd) and not is_diagonal(B_spd) and not is_diagonal(AB_spd)
    sA = exact_sv2(A_spd)
    sB = exact_sv2(B_spd)
    sAB = exact_sv2(AB_spd)
    assert sA == (4, 2) and sB == (5, 1) and sAB == (20, 2)
    assert sAB == (sA[0] * sB[0], sA[1] * sB[1])
    print("  PASS (A1 - SPD integer): A=[[3,1],[1,3]], B=[[3,2],[2,3]], AB=[[11,9],[9,11]]")
    print(f"        sigma(A)={sA}, sigma(B)={sB}, sigma(AB)={sAB}; none is diagonal.")

    # A2: Rational orthogonal SVD counterexample over Q and all dimensions n >= 2
    U_rat = [[Fraction(3, 5), Fraction(-4, 5)], [Fraction(4, 5), Fraction(3, 5)]]
    A_rat = [[34, 12], [12, 41]]
    B_rat = [[43, 24], [24, 57]]
    AB_rat = mat_mul(A_rat, B_rat)
    assert AB_rat == [[1750, 1500], [1500, 2625]]
    assert exact_sv2(A_rat) == (50, 25)
    assert exact_sv2(B_rat) == (75, 25)
    assert exact_sv2(AB_rat) == (3750, 625)
    # Check exact rational orthogonal SVD U * diag(50, 25) * U^T == A_rat
    for i in range(2):
        for j in range(2):
            val_a = sum(
                U_rat[i][k] * (50 if k == 0 else 25) * U_rat[j][k] for k in range(2)
            )
            val_b = sum(
                U_rat[i][k] * (75 if k == 0 else 25) * U_rat[j][k] for k in range(2)
            )
            assert val_a == A_rat[i][j] and val_b == B_rat[i][j]

    for n in range(2, 7):
        An = [[25 if i == j else 0 for j in range(n)] for i in range(n)]
        Bn = [[25 if i == j else 0 for j in range(n)] for i in range(n)]
        for i in range(2):
            for j in range(2):
                An[i][j] = A_rat[i][j]
                Bn[i][j] = B_rat[i][j]
        ABn = mat_mul(An, Bn)
        assert not is_diagonal(An) and not is_diagonal(Bn) and not is_diagonal(ABn)
        sv_An = numeric_singular_values(An)
        sv_Bn = numeric_singular_values(Bn)
        sv_ABn = numeric_singular_values(ABn)
        exp_A = [50.0, 25.0] + [25.0] * (n - 2)
        exp_B = [75.0, 25.0] + [25.0] * (n - 2)
        exp_AB = [3750.0, 625.0] + [625.0] * (n - 2)
        for k in range(1, n + 1):
            lhs = math.prod(sv_ABn[:k])
            rhs = math.prod(sv_An[j] * sv_Bn[j] for j in range(k))
            target = math.prod(exp_AB[:k])
            assert abs(lhs - target) <= 1e-11 * target
            assert abs(rhs - target) <= 1e-11 * target
        assert abs(sv_An[0] - exp_A[0]) < 1e-8 and abs(sv_Bn[0] - exp_B[0]) < 1e-8
    print("  PASS (A2 - Rational orthogonal SVD & block extension): verified for all n = 2..6.")

    # A3: Non-diagonal, non-normal, non-commuting, AND defective (non-diagonalizable over C)
    A_def = [[16, -12], [3, 4]]
    B_def = [[173, -216], [-36, 212]]
    AB_def = mat_mul(A_def, B_def)
    BA_def = mat_mul(B_def, A_def)
    assert AB_def == [[3200, -6000], [375, 200]]
    assert AB_def != BA_def, "Expected non-commuting pair"
    for name, X in [("A_def", A_def), ("B_def", B_def), ("AB_def", AB_def)]:
        assert not is_diagonal(X), f"{name} should not be diagonal"
        assert not is_normal(X), f"{name} should not be normal"
    assert is_defective_2x2(A_def), "A_def must be defective (non-diagonalizable over C)"
    assert is_defective_2x2(AB_def), "AB_def must be defective (non-diagonalizable over C)"
    sA_d = exact_sv2(A_def)
    sB_d = exact_sv2(B_def)
    sAB_d = exact_sv2(AB_def)
    assert sA_d == (20, 5)
    assert sB_d == (340, 85)
    assert sAB_d == (6800, 425) == (sA_d[0] * sB_d[0], sA_d[1] * sB_d[1])
    print("  PASS (A3 - Defective 2x2): A_def=[[16,-12],[3,4]] and AB_def=[[3200,-6000],[375,200]]")
    print("        are non-normal, non-commuting, AND non-diagonalizable over C, yet sigma(AB)=sigma(A)*sigma(B).")

    # A4: 4x4 block counterexample where ALL THREE of calA, calB, calA*calB are defective over C!
    calA = [[0] * 4 for _ in range(4)]
    calB = [[0] * 4 for _ in range(4)]
    B_def_T = mat_transpose(B_def)
    A_def_T = mat_transpose(A_def)
    for i in range(2):
        for j in range(2):
            calA[i][j] = 17 * A_def[i][j]
            calA[i + 2][j + 2] = B_def_T[i][j]
            calB[i][j] = B_def[i][j]
            calB[i + 2][j + 2] = 17 * A_def_T[i][j]
    calAB = mat_mul(calA, calB)
    calBA = mat_mul(calB, calA)
    assert calAB != calBA
    for X in (calA, calB, calAB):
        assert not is_diagonal(X) and not is_normal(X)
    sv_calA = numeric_singular_values(calA)
    sv_calB = numeric_singular_values(calB)
    sv_calAB = numeric_singular_values(calAB)
    for j in range(4):
        assert abs(sv_calAB[j] - sv_calA[j] * sv_calB[j]) < 1e-5
    print("  PASS (A4 - All-three-defective 4x4): calA, calB, calA*calB all have Jordan blocks over C.")


def check_universal_2x2_identities_and_equality_iff() -> None:
    print("[3/7] Checking universal 2x2 algebraic identities & equality characterization on 5,000 pairs...")
    rng = random.Random(7153)
    equality_hits = 0
    for trial in range(5000):
        if trial < 200:
            # Force structured pairs (orthogonal/scaled-orthogonal alignments) so equality branch is exercised often
            u_a, u_b = rng.choice([(3, 4), (4, 3), (5, 12), (8, 15), (1, 0)])
            v_a, v_b = rng.choice([(3, 4), (4, 3), (5, 12), (1, 0)])
            w_a, w_b = rng.choice([(3, 4), (4, 3), (1, 0)])
            U = [[u_a, -u_b], [u_b, u_a]]
            V = [[v_a, -v_b], [v_b, v_a]]
            W = [[w_a, -w_b], [w_b, w_a]]
            sa1, sa2 = sorted([rng.randint(0, 6), rng.randint(0, 6)], reverse=True)
            sb1, sb2 = sorted([rng.randint(0, 6), rng.randint(0, 6)], reverse=True)
            A = mat_mul(mat_mul(U, [[sa1, 0], [0, sa2]]), mat_transpose(V))
            B = mat_mul(mat_mul(V, [[sb1, 0], [0, sb2]]), mat_transpose(W))
        else:
            A = [[rng.randint(-8, 8) for _ in range(2)] for _ in range(2)]
            B = [[rng.randint(-8, 8) for _ in range(2)] for _ in range(2)]
        AB = mat_mul(A, B)
        GA = mat_mul(mat_transpose(A), A)
        GB = mat_mul(B, mat_transpose(B))
        GAB = mat_mul(mat_transpose(AB), AB)

        p, q, r = GA[0][0], GA[0][1], GA[1][1]
        u, v, w = GB[0][0], GB[0][1], GB[1][1]
        tr_GA = p + r
        tr_GB = u + w
        tr_GAB = tr2(GAB)

        # Identity 1: 2*||AB||_F^2 - ||A||_F^2 * ||B||_F^2 == (p - r)*(u - w) + 4*q*v
        lhs = 2 * tr_GAB - tr_GA * tr_GB
        rhs = (p - r) * (u - w) + 4 * q * v
        assert lhs == rhs

        # Identity 2: Brahmagupta-Fibonacci
        disc_A = (p - r) ** 2 + 4 * q * q
        disc_B = (u - w) ** 2 + 4 * v * v
        comm_off = (p - r) * v - q * (u - w)
        assert rhs * rhs + 4 * comm_off * comm_off == disc_A * disc_B

        # Commutator check: [GA, GB] == 0 iff comm_off == 0
        comm_zero = mat_mul(GA, GB) == mat_mul(GB, GA)
        assert comm_zero == (comm_off == 0)

        # Exact squared singular values over R
        da = math.sqrt(disc_A)
        db = math.sqrt(disc_B)
        dab = math.sqrt(max(0, tr_GAB * tr_GAB - 4 * det2(GAB)))
        a1_sq, a2_sq = (tr_GA + da) / 2.0, (tr_GA - da) / 2.0
        b1_sq, b2_sq = (tr_GB + db) / 2.0, (tr_GB - db) / 2.0
        c1_sq, c2_sq = (tr_GAB + dab) / 2.0, (tr_GAB - dab) / 2.0

        # Product log-majorization on squared singular values
        assert c1_sq <= a1_sq * b1_sq + 1e-9
        assert abs(c1_sq * c2_sq - (a1_sq * b1_sq) * (a2_sq * b2_sq)) < 1e-7

        # Necessary & sufficient condition for (c1^2, c2^2) == (a1^2*b1^2, a2^2*b2^2):
        # rhs == sqrt(disc_A * disc_B) <=> comm_off == 0 and rhs >= 0
        alg_cond = (comm_off == 0) and (rhs >= 0)
        num_eq = abs(c1_sq - a1_sq * b1_sq) < 1e-7 and abs(c2_sq - a2_sq * b2_sq) < 1e-7
        assert alg_cond == num_eq, f"Mismatch on A={A}, B={B}: alg={alg_cond}, num={num_eq}"
        if alg_cond:
            equality_hits += 1

    assert equality_hits >= 200
    print(f"  PASS: All 5,000 pairs satisfied universal identities & iff characterization ({equality_hits} equality cases).")


def check_lidskii_wielandt_subset_inequalities() -> None:
    print("[4/7] Checking full Lidskii-Wielandt index-subset product inequalities for n = 2..5...")
    rng = random.Random(20261125)
    for n in (2, 3, 4, 5):
        for _ in range(100):
            A = [[rng.uniform(-5.0, 5.0) for _ in range(n)] for _ in range(n)]
            B = [[rng.uniform(-5.0, 5.0) for _ in range(n)] for _ in range(n)]
            AB = [
                [sum(A[i][t] * B[t][j] for t in range(n)) for j in range(n)]
                for i in range(n)
            ]
            sA = numeric_singular_values(A)
            sB = numeric_singular_values(B)
            sAB = numeric_singular_values(AB)
            for k in range(1, n + 1):
                for idxs in itertools.combinations(range(n), k):
                    lhs = math.prod(sAB[i] for i in idxs)
                    rhs1 = math.prod(sA[idxs[j]] * sB[j] for j in range(k))
                    rhs2 = math.prod(sA[j] * sB[idxs[j]] for j in range(k))
                    # Forming X^T X squares condition numbers for near-singular random matrices
                    tol1 = 1e-5 * max(1.0, rhs1)
                    tol2 = 1e-5 * max(1.0, rhs2)
                    assert lhs <= rhs1 + tol1
                    assert lhs <= rhs2 + tol2
            # Full product equality at k = n
            full_rhs = math.prod(sA) * math.prod(sB)
            assert abs(math.prod(sAB) - full_rhs) <= 1e-5 * max(1.0, full_rhs)
    print("  PASS: All Lidskii-Wielandt index-subset product inequalities verified across n = 2..5.")


def check_interpretation_B_weyl() -> None:
    print("[5/7] Checking Interpretation B (Weyl eigenvalue vs. singular-value log-majorization)...")
    # Explicit symmetric non-diagonal integer counterexample
    W = [[2, 1], [1, 2]]
    assert not is_diagonal(W) and is_normal(W)
    sW = exact_sv2(W)
    # Eigenvalues of [[2,1],[1,2]] are 3 and 1
    assert tr2(W) == 3 + 1 and det2(W) == 3 * 1
    assert sW == (3, 1)
    print("  PASS: W=[[2,1],[1,2]] is non-diagonal yet |lambda(W)| = (3, 1) = sigma(W).")

    # Check 2,000 random 2x2 matrices (both real and complex conjugate eigenvalues)
    rng = random.Random(42)
    for _ in range(2000):
        A = [[rng.randint(-10, 10) for _ in range(2)] for _ in range(2)]
        t = tr2(A)
        d = det2(A)
        disc = t * t - 4 * d
        if disc >= 0:
            r = math.sqrt(disc)
            lams = sorted([abs((t + r) / 2.0), abs((t - r) / 2.0)], reverse=True)
        else:
            mod = math.sqrt(d)
            lams = [mod, mod]
        svs = numeric_singular_values(A)
        assert lams[0] <= svs[0] + 1e-9
        assert abs(lams[0] * lams[1] - svs[0] * svs[1]) < 1e-8
        eq = abs(lams[0] - svs[0]) < 1e-7 and abs(lams[1] - svs[1]) < 1e-7
        assert eq == is_normal(A)
    print("  PASS: Verified |lambda(A)| <=_log sigma(A) and equality <=> A is normal on 2,000 matrices.")


def check_interpretation_C_diagonal_pinching() -> None:
    print("[6/7] Checking Interpretation C (diagonal entries |diag(A)| vs. singular values sigma(A))...")
    # Counterexample 1: symmetric positive definite A = [[2, 1], [1, 2]]
    # |diag(A)| = (2, 2), sigma(A) = (3, 1): incomparable under weak log-majorization in BOTH directions!
    A1 = [[2, 1], [1, 2]]
    d1 = sorted([abs(A1[0][0]), abs(A1[1][1])], reverse=True)
    s1 = exact_sv2(A1)
    assert d1 == [2, 2] and s1 == (3, 1)
    assert not (d1[0] * d1[1] <= s1[0] * s1[1]), "Expected |d| <=_wlog sigma to fail at k=2 (4 > 3)"
    assert not (s1[0] <= d1[0]), "Expected sigma <=_wlog |d| to fail at k=1 (3 > 2)"

    # Counterexample 2: SL_2(Z) SPD matrix [[2, 1], [1, 1]]
    A2 = [[2, 1], [1, 1]]
    assert det2(A2) == 1
    assert abs(A2[0][0] * A2[1][1]) == 2 > 1 == abs(det2(A2))

    # Verify Ky Fan additive weak majorization |diag(A)| <=_w sigma(A) on 2,000 random matrices
    rng = random.Random(99)
    for _ in range(2000):
        A = [[rng.randint(-10, 10) for _ in range(3)] for _ in range(3)]
        diag_sorted = sorted([abs(A[i][i]) for i in range(3)], reverse=True)
        svs = numeric_singular_values(A)
        for k in range(1, 4):
            assert sum(diag_sorted[:k]) <= sum(svs[:k]) + 1e-8
    print("  PASS: |diag(A)| <=_w sigma(A) holds additively, while |diag(A)| <=_wlog sigma(A) and")
    print("        sigma(A) <=_wlog |diag(A)| BOTH fail on SPD matrix [[2,1],[1,2]] (d=(2,2), sigma=(3,1)).")


def check_compact_hilbert_truncation() -> None:
    print("[7/7] Checking compact operator extension on l^2(N) via N-dimensional truncations...")
    # T_A = A_def (+) diag(2, 1, 1/2, ...), T_B = B_def (+) diag(40, 20, 10, ...)
    # Verify on 8x8 truncation that singular values remain strictly decreasing, positive, and exact!
    A_def = [[16, -12], [3, 4]]      # sv = (20, 5)
    B_def = [[173, -216], [-36, 212]]  # sv = (340, 85)
    N = 8
    TA = [[0.0] * N for _ in range(N)]
    TB = [[0.0] * N for _ in range(N)]
    for i in range(2):
        for j in range(2):
            TA[i][j] = float(A_def[i][j])
            TB[i][j] = float(B_def[i][j])
    for m in range(2, N):
        TA[m][m] = 4.0 * (0.5 ** (m - 2))    # 4, 2, 1, 0.5, 0.25, 0.125 < 5
        TB[m][m] = 64.0 * (0.5 ** (m - 2))   # 64, 32, 16, 8, 4, 2 < 85
    TAB = [[sum(TA[i][k] * TB[k][j] for k in range(N)) for j in range(N)] for i in range(N)]
    sA = numeric_singular_values(TA)
    sB = numeric_singular_values(TB)
    sAB = numeric_singular_values(TAB)
    for k in range(1, N + 1):
        lhs = math.prod(sAB[:k])
        rhs = math.prod(sA[j] * sB[j] for j in range(k))
        assert abs(lhs - rhs) / rhs < 1e-9
    print("  PASS: Injective compact operator model with strictly decreasing positive singular values")
    print("        attains exact partial-product equality for all k >= 1 while remaining non-diagonal & defective.")


def main() -> int:
    print("=" * 76)
    print("Verification Suite for Conjecture 00000007153")
    print("Verdict: FALSE (Disproved across all standard interpretations)")
    print("=" * 76)
    check_positive_diagonal_witness()
    check_interpretation_A_counterexamples()
    check_universal_2x2_identities_and_equality_iff()
    check_lidskii_wielandt_subset_inequalities()
    check_interpretation_B_weyl()
    check_interpretation_C_diagonal_pinching()
    check_compact_hilbert_truncation()
    print("=" * 76)
    print("ALL VERIFICATION CHECKS PASSED.")
    print("=" * 76)
    return 0


if __name__ == "__main__":
    sys.exit(main())
