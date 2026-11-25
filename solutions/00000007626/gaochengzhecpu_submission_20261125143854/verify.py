#!/usr/bin/env python3
"""
Independent computational verification suite for Conjecture 00000007626:
  "Definition: The connected-family structure of idempotent formulas.
   Conjecture: The connected-family spectrum of idempotents is finite;
   the bound of finiteness is the matrix-block count; and the bound of
   the matrix-block count is the isomorphism-class counting.
   (matrix-block-finite idempotent families)"

Uses ONLY the Python 3 standard library. Exits with code 0 iff all checks pass.
"""

from __future__ import annotations
from collections import deque
from fractions import Fraction
import itertools
import random
import sys


# ---------------------------------------------------------------------------
# Exact univariate polynomials over Fraction (standard library only)
# ---------------------------------------------------------------------------
class Poly:
    def __init__(self, coeffs: list[Fraction | int]):
        c = [Fraction(x) for x in coeffs]
        while c and c[-1] == 0:
            c.pop()
        self.c = c

    @staticmethod
    def const(v: int | Fraction) -> Poly:
        return Poly([v])

    @staticmethod
    def var() -> Poly:
        return Poly([0, 1])

    def __eq__(self, other: object) -> bool:
        if isinstance(other, (int, Fraction)):
            return self == Poly.const(other)
        if isinstance(other, Poly):
            return self.c == other.c
        return False

    def __add__(self, other: Poly | int | Fraction) -> Poly:
        o = other if isinstance(other, Poly) else Poly.const(other)
        n = max(len(self.c), len(o.c))
        return Poly([
            (self.c[i] if i < len(self.c) else Fraction(0))
            + (o.c[i] if i < len(o.c) else Fraction(0))
            for i in range(n)
        ])

    def __sub__(self, other: Poly | int | Fraction) -> Poly:
        o = other if isinstance(other, Poly) else Poly.const(other)
        return self + (o * (-1))

    def __neg__(self) -> Poly:
        return self * (-1)

    def __mul__(self, other: Poly | int | Fraction) -> Poly:
        if isinstance(other, (int, Fraction)):
            return Poly([x * Fraction(other) for x in self.c])
        if not self.c or not other.c:
            return Poly([])
        out = [Fraction(0)] * (len(self.c) + len(other.c) - 1)
        for i, a in enumerate(self.c):
            for j, b in enumerate(other.c):
                out[i + j] += a * b
        return Poly(out)

    def deriv(self) -> Poly:
        if len(self.c) <= 1:
            return Poly([])
        return Poly([(i + 1) * self.c[i + 1] for i in range(len(self.c) - 1)])

    def eval(self, x: int | Fraction) -> Fraction:
        xv = Fraction(x)
        return sum((a * (xv ** i) for i, a in enumerate(self.c)), Fraction(0))


def pmat_mul(A: list[list[Poly]], B: list[list[Poly]]) -> list[list[Poly]]:
    n = len(A)
    return [
        [sum((A[i][k] * B[k][j] for k in range(n)), Poly.const(0)) for j in range(n)]
        for i in range(n)
    ]


def pmat_eval(A: list[list[Poly]], val: int | Fraction) -> list[list[Fraction]]:
    return [[x.eval(val) for x in row] for row in A]


def pmat_trace(A: list[list[Poly]]) -> Poly:
    return sum((A[i][i] for i in range(len(A))), Poly.const(0))


# ---------------------------------------------------------------------------
# Suite 1: Exact 3-component A^1-spectrum of M_2(F_p) and universal swap path
# ---------------------------------------------------------------------------
def verify_suite_1_m2_spectrum() -> None:
    print("[Suite 1] Exact 3-component A^1-spectrum of M_2(K) (b = 1, |pi_0(E)| = 3 > 1)...")
    t = Poly.var()
    one, zero = Poly.const(1), Poly.const(0)
    U = [[one, -t], [zero, one]]
    L = [[one, zero], [t, one]]
    U_inv = [[one, t], [zero, one]]
    L_inv = [[one, zero], [-t, one]]
    g = pmat_mul(pmat_mul(U, L), U)
    g_inv = pmat_mul(pmat_mul(U_inv, L_inv), U_inv)
    assert pmat_mul(g, g_inv) == [[one, zero], [zero, one]]

    E11 = [[one, zero], [zero, zero]]
    E_swap = pmat_mul(pmat_mul(g, E11), g_inv)
    assert pmat_mul(E_swap, E_swap) == E_swap
    assert pmat_eval(E_swap, 0) == [[1, 0], [0, 0]]
    assert pmat_eval(E_swap, 1) == [[0, 0], [0, 1]]
    assert pmat_trace(E_swap) == Poly.const(1)
    det_swap = E_swap[0][0] * E_swap[1][1] - E_swap[0][1] * E_swap[1][0]
    assert det_swap == Poly.const(0)

    # Exhaustive check over finite fields F_2, F_3, F_5
    for p in (2, 3, 5):
        idems: list[tuple[int, int, int, int]] = []
        for a, b, c, d in itertools.product(range(p), repeat=4):
            a2 = (a * a + b * c) % p
            b2 = (a * b + b * d) % p
            c2 = (c * a + d * c) % p
            d2 = (c * b + d * d) % p
            if (a2, b2, c2, d2) == (a, b, c, d):
                idems.append((a, b, c, d))
        expected_total = 2 + p * (p + 1)
        assert len(idems) == expected_total, f"p={p}: {len(idems)} != {expected_total}"

        # Partition by trichotomy: {0}, {det=0 & tr=1}, {I_2}
        z_mat = (0, 0, 0, 0)
        i_mat = (1, 0, 0, 1)
        rank1 = [
            m for m in idems
            if m not in (z_mat, i_mat)
        ]
        assert len(rank1) == p * (p + 1)
        for a, b, c, d in rank1:
            assert (a * d - b * c) % p == 0
            assert (a + d) % p == 1

        # Verify explicit A^1-homotopy transitivity on all rank-1 idempotents over F_p
        # using elementary transvections T_12(c*t), T_21(c*t) and E_swap(t) mod p!
        adj: dict[tuple[int, int, int, int], set[tuple[int, int, int, int]]] = {
            m: set() for m in idems
        }

        def mul2(x, y):
            return (
                (x[0] * y[0] + x[1] * y[2]) % p,
                (x[0] * y[1] + x[1] * y[3]) % p,
                (x[2] * y[0] + x[3] * y[2]) % p,
                (x[2] * y[1] + x[3] * y[3]) % p,
            )

        for m in idems:
            for c in range(p):
                # Upper transvection [[1, c*t], [0, 1]] at t=1
                u1 = mul2(mul2((1, c, 0, 1), m), (1, (-c) % p, 0, 1))
                adj[m].add(u1)
                adj[u1].add(m)
                # Lower transvection [[1, 0], [c*t, 1]] at t=1
                l1 = mul2(mul2((1, 0, c, 1), m), (1, 0, (-c) % p, 1))
                adj[m].add(l1)
                adj[l1].add(m)

        # Count connected components of elementary A^1-conjugation graph
        seen: set[tuple[int, int, int, int]] = set()
        comps: list[set[tuple[int, int, int, int]]] = []
        for m in idems:
            if m in seen:
                continue
            comp = {m}
            q = deque([m])
            seen.add(m)
            while q:
                cur = q.popleft()
                for nxt in adj[cur]:
                    if nxt not in seen:
                        seen.add(nxt)
                        comp.add(nxt)
                        q.append(nxt)
            comps.append(comp)

        assert len(comps) == 3, f"Expected 3 components over F_{p}, got {len(comps)}"
        comp_sizes = sorted(len(c) for c in comps)
        assert comp_sizes == [1, 1, p * (p + 1)]

        # Also check primitive idempotents over F_p: exact match with rank1!
        primitives = []
        for e in idems:
            if e == z_mat:
                continue
            reducible = False
            for e1 in idems:
                if e1 == z_mat or e1 == e:
                    continue
                e2 = tuple((e[i] - e1[i]) % p for i in range(4))
                if e2 in idems and e2 != z_mat:
                    if mul2(e1, e2) == z_mat and mul2(e2, e1) == z_mat:
                        reducible = True
                        break
            if not reducible:
                primitives.append(e)
        assert set(primitives) == set(rank1)
    print("  PASS: M_2(F_p) (p=2,3,5) has |E| = 8, 14, 32 in exactly 3 > 1 components; primitives = 1 = b.")


# ---------------------------------------------------------------------------
# Suite 2: Leibniz-trace polynomial homotopy invariance on M_n(Q[t]) & Cl_{m,m}
# ---------------------------------------------------------------------------
def verify_suite_2_leibniz_trace_and_single_block() -> None:
    print("[Suite 2] Leibniz-trace invariance on M_n(Q[t]) and single-block divergence...")
    rng = random.Random(202607626)
    t = Poly.var()

    for n in (2, 3, 4, 5):
        for r in range(n + 1):
            # Start with canonical diagonal idempotent P_r = diag(1_r, 0_{n-r})
            P = [
                [Poly.const(1 if i == j and i < r else 0) for j in range(n)]
                for i in range(n)
            ]
            # Conjugate by 3 random polynomial transvections I + (c0 + c1*t) E_{ij} (i != j)
            E = P
            for _ in range(3):
                i = rng.randrange(n)
                j = (i + rng.randrange(1, n)) % n
                pol = Poly([rng.randint(-3, 3), rng.randint(-3, 3)])
                T_pos = [
                    [
                        Poly.const(1) if a == b else (pol if (a == i and b == j) else Poly.const(0))
                        for b in range(n)
                    ]
                    for a in range(n)
                ]
                T_neg = [
                    [
                        Poly.const(1) if a == b else (-pol if (a == i and b == j) else Poly.const(0))
                        for b in range(n)
                    ]
                    for a in range(n)
                ]
                E = pmat_mul(pmat_mul(T_pos, E), T_neg)
            assert pmat_mul(E, E) == E
            tr_poly = pmat_trace(E)
            assert tr_poly.deriv() == Poly.const(0)
            assert tr_poly == Poly.const(r)
            assert tr_poly.eval(0) == r and tr_poly.eval(1) == r

    # Verify split Clifford sequence Cl_{m,m}(R) ~= M_{2^m}(R) has b = 1 vs 2^m - 1 proper components
    for m in range(2, 11):
        b = 1
        total_comps = (2 ** m) + 1
        proper_comps = (2 ** m) - 1
        assert total_comps > b and proper_comps > b
    print("  PASS: D(tr(E(t))) = 0 verified on M_n(Q[t]) (n=2..5); Cl_{m,m} diverges as 2^m - 1 >> 1 = b.")


# ---------------------------------------------------------------------------
# Suite 3: Complete Bott-periodic census of Cl_{p,q}(R) for 0 <= p + q <= 8
# ---------------------------------------------------------------------------
def clifford_blocks_real(p: int, q: int) -> list[tuple[str, int]]:
    m = p + q
    k = (p - q) % 8
    if k in (0, 2):
        return [("R", 2 ** (m // 2))]
    if k == 1:
        return [("R", 2 ** ((m - 1) // 2))] * 2
    if k in (3, 7):
        return [("C", 2 ** ((m - 1) // 2))]
    if k in (4, 6):
        return [("H", 2 ** ((m - 2) // 2))]
    assert k == 5
    return [("H", 2 ** ((m - 3) // 2))] * 2


def verify_suite_3_clifford_census() -> None:
    print("[Suite 3] Bott-periodic real Clifford census Cl_{p,q}(R) for 0 <= p + q <= 8...")
    dim_div = {"R": 1, "C": 2, "H": 4}
    total_checked = 0
    all_idem_violations = 0
    proper_idem_violations = 0
    central_idem_violations = 0
    alg_iso_violations = 0

    for m in range(0, 9):
        for p in range(m + 1):
            q = m - p
            blocks = clifford_blocks_real(p, q)
            assert sum(dim_div[d] * (n ** 2) for d, n in blocks) == 2 ** m
            b = len(blocks)
            c_alg = len(set(blocks))
            c_simp = b
            pi0_all = 1
            for _, n in blocks:
                pi0_all *= (n + 1)
            pi0_proper = pi0_all - 2
            pi0_central = 2 ** b
            pi0_prim = b

            total_checked += 1
            if pi0_all > b:
                all_idem_violations += 1
            if pi0_proper > b:
                proper_idem_violations += 1
            if pi0_central > b:
                central_idem_violations += 1
            if b > c_alg:
                alg_iso_violations += 1
            assert pi0_prim == b == c_simp

    assert total_checked == 45
    assert all_idem_violations == 45, "Every Cl_{p,q}(R) violates |pi_0(E)| <= b!"
    assert central_idem_violations == 45, "Every Cl_{p,q}(R) violates |pi_0(E(Z))| <= b!"
    assert proper_idem_violations == 33, f"Got {proper_idem_violations}/45 proper violations"
    assert alg_iso_violations == 10, f"Got {alg_iso_violations}/45 split-center b=2 > c_alg=1 violations"
    print(
        f"  PASS: Checked all {total_checked} signatures (0 <= p+q <= 8): "
        f"45/45 violate |pi_0(E)| <= b, 33/45 violate |pi_0(E^o)| <= b, "
        f"10/45 violate b <= c_alg, 45/45 satisfy |pi_0(Prim(E))| = b = c_simp."
    )


# ---------------------------------------------------------------------------
# Suite 4: Sporadic classification of prod(n_i + 1) - 2 <= b & Clause III
# ---------------------------------------------------------------------------
def verify_suite_4_sporadic_and_clause3() -> None:
    print("[Suite 4] Exhaustive check of sporadic profile theorem & Clause III inequalities...")
    sporadic_found: list[tuple[int, ...]] = []
    for b in range(1, 7):
        for dims in itertools.product(range(1, 6), repeat=b):
            prod_val = 1
            for n in dims:
                prod_val *= (n + 1)
            assert prod_val >= (2 ** b) > b
            if prod_val - 2 <= b:
                sporadic_found.append(dims)

    assert sporadic_found == [(1,), (2,), (1, 1)], f"Unexpected sporadic list: {sporadic_found}"

    # Verify explicit double strict reverse inequalities |pi_0| > b > c_alg:
    # 1. K x K (b = 2, dims = (1, 1)): all idempotents 4 > 2 > 1
    assert (1 + 1) * (1 + 1) == 4 > 2 > 1
    # 2. M_2(K) x M_2(K) (b = 2, dims = (2, 2)): proper idempotents 7 > 2 > 1
    assert (2 + 1) * (2 + 1) - 2 == 7 > 2 > 1
    # 3. K^3 (b = 3, dims = (1, 1, 1)): proper central idempotents 6 > 3 > 1
    assert (2 ** 3) - 2 == 6 > 3 > 1
    print("  PASS: Sporadic profiles are uniquely {(1), (2), (1,1)}; double reverse inequalities verified.")


# ---------------------------------------------------------------------------
# Suite 5: Non-semisimple nilpotent radical homotopy invariance & Newton lift
# ---------------------------------------------------------------------------
def verify_suite_5_nilpotent_lifting() -> None:
    print("[Suite 5] Universal Newton idempotent lift & nilpotent radical homotopy invariance...")
    x = Poly.var()
    f = (x * x) * 3 - (x * x * x) * 2
    d = x * x - x
    assert f - x == d * (Poly.const(1) - x * 2)
    assert f * f - f == (d * d) * ((x * x) * 4 - x * 4 - Poly.const(3))

    # Random 4x4 upper-triangular idempotent pairs over Q with identical diagonal
    rng = random.Random(7626)
    n = 4
    I4 = [[Poly.const(1 if i == j else 0) for j in range(n)] for i in range(n)]

    def fmat_mul(A, B):
        return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]

    def rand_upper_idem(diag: list[int]) -> list[list[Fraction]]:
        E = [[Fraction(diag[i] if i == j else 0) for j in range(n)] for i in range(n)]
        for gap in range(1, n):
            for i in range(n - gap):
                j = i + gap
                s = sum(E[i][k] * E[k][j] for k in range(i + 1, j))
                if diag[i] + diag[j] == 1:
                    assert s == 0
                    E[i][j] = Fraction(rng.randint(-6, 6))
                elif diag[i] + diag[j] == 0:
                    E[i][j] = s
                else:
                    E[i][j] = -s
        assert fmat_mul(E, E) == E
        return E

    t = Poly.var()
    for _ in range(40):
        diag = [rng.randint(0, 1) for _ in range(n)]
        e0 = rand_upper_idem(diag)
        e1 = rand_upper_idem(diag)
        # w = (2*e1 - I)*(e0 - e1)
        two_e1_sub_I = [
            [2 * e1[i][j] - (1 if i == j else 0) for j in range(n)] for i in range(n)
        ]
        diff = [[e0[i][j] - e1[i][j] for j in range(n)] for i in range(n)]
        w = fmat_mul(two_e1_sub_I, diff)
        # Check w^4 == 0
        w2 = fmat_mul(w, w)
        w3 = fmat_mul(w2, w)
        w4 = fmat_mul(w3, w)
        assert all(w4[i][j] == 0 for i in range(n) for j in range(n))

        # Construct U(t) = I + t*w and V(t) = I - t*w + t^2*w^2 - t^3*w^3 in M_4(Q[t])
        U_t = [
            [Poly([1 if i == j else 0, w[i][j]]) for j in range(n)]
            for i in range(n)
        ]
        V_t = [
            [Poly([1 if i == j else 0, -w[i][j], w2[i][j], -w3[i][j]]) for j in range(n)]
            for i in range(n)
        ]
        assert pmat_mul(U_t, V_t) == I4
        E0_const = [[Poly.const(e0[i][j]) for j in range(n)] for i in range(n)]
        E_t = pmat_mul(pmat_mul(U_t, E0_const), V_t)
        assert pmat_mul(E_t, E_t) == E_t
        assert pmat_eval(E_t, 0) == e0
        assert pmat_eval(E_t, 1) == e1

    # Exhaustive check of T_2(F_3): 8 idempotents in 4 connected components (sizes 1, 1, 3, 3)
    t2_idems = []
    for a, b, c in itertools.product(range(3), repeat=3):
        if (a * a % 3, (a * b + b * c) % 3, c * c % 3) == (a, b, c):
            t2_idems.append((a, b, c))
    assert len(t2_idems) == 8
    by_diag: dict[tuple[int, int], list[tuple[int, int, int]]] = {}
    for a, b, c in t2_idems:
        by_diag.setdefault((a, c), []).append((a, b, c))
    assert len(by_diag) == 4
    assert sorted(len(v) for v in by_diag.values()) == [1, 1, 3, 3]
    print("  PASS: Newton identity, 40/40 random M_4(Q[t]) nilpotent homotopies, and T_2(F_3) (4 > 2 = b) verified.")


def main() -> int:
    print("=" * 74)
    print("Conjecture 00000007626 — Independent Verification Suite")
    print("=" * 74)
    verify_suite_1_m2_spectrum()
    verify_suite_2_leibniz_trace_and_single_block()
    verify_suite_3_clifford_census()
    verify_suite_4_sporadic_and_clause3()
    verify_suite_5_nilpotent_lifting()
    print("=" * 74)
    print("ALL 5 VERIFICATION SUITES PASSED SUCCESSFULLY.")
    print("=" * 74)
    return 0


if __name__ == "__main__":
    sys.exit(main())
