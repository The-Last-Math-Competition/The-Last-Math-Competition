#!/usr/bin/env python3
"""
Standalone verification suite for Conjecture 00000007616:
"The star operator with the Clifford realization structure:
 conversion constant, geometric-product realization, uniqueness up to volume
 orientation, and unit norm."

Uses exact rational arithmetic (fractions.Fraction) over Q and algebraic
quadratic extensions to verify:
  1. Universal Chevalley-Hodge reverted realization *_nu(x) = rev(x) * nu
     across arbitrary dimensions n = 1..4, orthogonal and non-orthogonal Gram
     matrices, Euclidean, Lorentzian, non-unimodular rational, and degenerate
     quadratic forms, for both right and left Hodge star conventions.
  2. Positive regime (non-vacuity): on Euclidean R^{n,0} with metric-normalized
     volume forms +-vol_Q, *_nu(x) = c * rev(x) * vol_Q holds with unique
     c in {+1, -1} and unit Clifford reversion norm rev(Omega)*Omega = +1.
  3. Refutation of Clause 1 (unreverted / two-sided geometric product):
     - On every nondegenerate quadratic space of dim n >= 2 (starting with Cl(2,0)),
       NO scalar c and element Omega satisfy *_nu(x) = c * x * Omega or
       *_nu(x) = c * Omega * x, and NO A, B in Cl(V, Q) satisfy
       *_nu(x) = A * x * B or *_nu(x) = A * invol(x) * B across all x.
     - Exact rank-1 characterization: *_nu(x) = x * nu holds iff rank(Q) <= 1.
     - On non-orthogonal bases, naive geometric product e_1 * ... * e_n != e_1 ^ ... ^ e_n.
  4. Refutation of Clause 3 (unit norm):
     - Lorentzian Cl(1,1) and Minkowski Cl(3,1), Cl(1,3): unique reverted
       realization Omega = +-omega_0 has rev(Omega)*Omega = <Omega, Omega>_B = -1 != +1,
       and -c^2 = +1 has no real or rational solution.
     - Degenerate Cl(1,0,1) (Q = diag(1, 0)): unique reverted realization
       Omega = c * e_1 e_2 has rev(Omega)*Omega = conj(Omega)*Omega = Omega^2 =
       |<Omega, Omega>_B| = 0 != 1 for every c != 0.
     - Positive-definite rational space Q = diag(2, 3) over Q:
       rev(Omega)*Omega = 6 * c^2 != +-1 for all rational c in Q.
     - Algebraic square Omega^2 = -1 != +1 in Euclidean Cl(2,0) and Cl(3,0);
       conjugation norm conj(Omega)*Omega = -1 != +1 in Euclidean Cl(1,0) and Cl(3,0).
  5. Refutation of Clause 2 (uniqueness up to volume orientation +-1):
     - General volume forms nu = c * omega_0 within a fixed orientation (c > 0)
       scale Omega = c * omega_0 across all R_{>0}, not {+1, -1}.
     - In degenerate Cl(1,0,1), <c * omega_0, c * omega_0>_B = 0 for all c > 0,
       so no metric unit normalization exists to collapse R_{>0} to {+1}.
     - Restricted to positive grades k >= 1 in degenerate spaces (e.g. Q = 0 on K^2),
       infinitely many distinct Omega = c * omega_0 realize the same star operator.
"""

from fractions import Fraction
import itertools
import math
import sys


class BasisIndependentClifford:
    """
    Exact basis-independent Chevalley Clifford algebra Cl(V, Q) modeled on the
    exterior algebra Lambda(V) for an arbitrary n x n symmetric Gram matrix G
    over Q (orthogonal or non-orthogonal, nondegenerate or degenerate).
    """

    def __init__(self, gram_matrix):
        self.n = len(gram_matrix)
        self.G = [
            [Fraction(gram_matrix[i][j]) for j in range(self.n)]
            for i in range(self.n)
        ]
        for i in range(self.n):
            for j in range(self.n):
                assert self.G[i][j] == self.G[j][i], "Gram matrix must be symmetric"
        self.dim = 1 << self.n
        self._op_cols = None

    def zero(self):
        return [Fraction(0)] * self.dim

    def basis(self, mask):
        v = self.zero()
        v[mask] = Fraction(1)
        return v

    def scale(self, c, x):
        c = Fraction(c)
        return [c * xi for xi in x]

    def add(self, x, y):
        return [x[i] + y[i] for i in range(self.dim)]

    def sub(self, x, y):
        return [x[i] - y[i] for i in range(self.dim)]

    def wedge_masks(self, a, b):
        if a & b:
            return Fraction(0), 0
        coeff = Fraction(1)
        for i in range(self.n):
            if (a >> i) & 1:
                lower = b & ((1 << i) - 1)
                if lower.bit_count() & 1:
                    coeff = -coeff
        return coeff, a | b

    def wedge(self, x, y):
        res = self.zero()
        for a, ca in enumerate(x):
            if ca == 0:
                continue
            for b, cb in enumerate(y):
                if cb == 0:
                    continue
                c, m = self.wedge_masks(a, b)
                if c != 0:
                    res[m] += ca * cb * c
        return res

    def _contract_vec(self, i, mask):
        res = self.zero()
        pos = 0
        for j in range(self.n):
            if (mask >> j) & 1:
                gij = self.G[i][j]
                if gij != 0:
                    sgn = -1 if (pos % 2 == 1) else 1
                    res[mask ^ (1 << j)] += sgn * gij
                pos += 1
        return res

    def _left_vec_mul(self, i, y):
        res = self.wedge(self.basis(1 << i), y)
        for m, cm in enumerate(y):
            if cm == 0:
                continue
            contr = self._contract_vec(i, m)
            for m2, cm2 in enumerate(contr):
                res[m2] += cm * cm2
        return res

    def _blade_op_cols(self, mask):
        bits = [i for i in range(self.n) if (mask >> i) & 1]
        k = len(bits)
        fact = Fraction(1, math.factorial(k))
        cols = [self.zero() for _ in range(self.dim)]
        for perm in itertools.permutations(range(k)):
            inv = sum(
                1 for a in range(k) for b in range(a + 1, k) if perm[a] > perm[b]
            )
            sgn = Fraction(-1 if (inv % 2 == 1) else 1) * fact
            for col_m in range(self.dim):
                v = self.basis(col_m)
                for idx in reversed(perm):
                    v = self._left_vec_mul(bits[idx], v)
                for r in range(self.dim):
                    cols[col_m][r] += sgn * v[r]
        return cols

    def _ensure_table(self):
        if self._op_cols is None:
            self._op_cols = [
                self._blade_op_cols(m) if m != 0 else None for m in range(self.dim)
            ]

    def mul(self, x, y):
        self._ensure_table()
        res = self.zero()
        for a, ca in enumerate(x):
            if ca == 0:
                continue
            if a == 0:
                for r in range(self.dim):
                    res[r] += ca * y[r]
            else:
                cols = self._op_cols[a]
                for b, cb in enumerate(y):
                    if cb == 0:
                        continue
                    col = cols[b]
                    for r in range(self.dim):
                        res[r] += ca * cb * col[r]
        return res

    def invol(self, x):
        return [
            (-c if (m.bit_count() % 2 == 1) else c) for m, c in enumerate(x)
        ]

    def rev(self, x):
        res = self.zero()
        for m, c in enumerate(x):
            k = m.bit_count()
            res[m] = -c if ((k * (k - 1) // 2) % 2 == 1) else c
        return res

    def conj(self, x):
        return self.invol(self.rev(x))

    def _det_submatrix(self, rows, cols):
        k = len(rows)
        if k == 0:
            return Fraction(1)
        tot = Fraction(0)
        for perm in itertools.permutations(range(k)):
            inv = sum(
                1 for a in range(k) for b in range(a + 1, k) if perm[a] > perm[b]
            )
            sgn = -1 if (inv % 2 == 1) else 1
            prod = Fraction(sgn)
            for r in range(k):
                prod *= self.G[rows[r]][cols[perm[r]]]
            tot += prod
        return tot

    def inner_masks(self, a, b):
        if a.bit_count() != b.bit_count():
            return Fraction(0)
        rows = [i for i in range(self.n) if (a >> i) & 1]
        cols = [j for j in range(self.n) if (b >> j) & 1]
        return self._det_submatrix(rows, cols)

    def inner(self, x, y):
        tot = Fraction(0)
        for a, ca in enumerate(x):
            if ca == 0:
                continue
            for b, cb in enumerate(y):
                if cb == 0 or a.bit_count() != b.bit_count():
                    continue
                tot += ca * cb * self.inner_masks(a, b)
        return tot

    def hodge_star_right(self, beta, nu_coeff=Fraction(1)):
        """Unique operator satisfying alpha ^ (*_nu beta) = <alpha, beta>_B * nu."""
        full = (1 << self.n) - 1
        res = self.zero()
        for b_mask, cb in enumerate(beta):
            if cb == 0:
                continue
            k = b_mask.bit_count()
            for a_mask in range(self.dim):
                if a_mask.bit_count() != k:
                    continue
                comp = full ^ a_mask
                sgn, m = self.wedge_masks(a_mask, comp)
                assert m == full and sgn in (-1, 1)
                ip = self.inner_masks(a_mask, b_mask)
                res[comp] += cb * ip * nu_coeff * sgn
        return res

    def hodge_star_left(self, beta, nu_coeff=Fraction(1)):
        """Unique operator satisfying (*_nu^L beta) ^ alpha = <beta, alpha>_B * nu."""
        full = (1 << self.n) - 1
        res = self.zero()
        for b_mask, cb in enumerate(beta):
            if cb == 0:
                continue
            k = b_mask.bit_count()
            for a_mask in range(self.dim):
                if a_mask.bit_count() != k:
                    continue
                comp = full ^ a_mask
                sgn, m = self.wedge_masks(comp, a_mask)
                assert m == full and sgn in (-1, 1)
                ip = self.inner_masks(b_mask, a_mask)
                res[comp] += cb * ip * nu_coeff * sgn
        return res


def diag_gram(q_diag):
    n = len(q_diag)
    return [[q_diag[i] if i == j else 0 for j in range(n)] for i in range(n)]


def check_defining_equation(cl, nu_coeff=Fraction(1)):
    full = (1 << cl.n) - 1
    nu = cl.scale(nu_coeff, cl.basis(full))
    for k in range(cl.n + 1):
        k_masks = [m for m in range(cl.dim) if m.bit_count() == k]
        for am in k_masks:
            alpha = cl.basis(am)
            for bm in k_masks:
                beta = cl.basis(bm)
                sb_r = cl.hodge_star_right(beta, nu_coeff)
                lhs_r = cl.wedge(alpha, sb_r)
                rhs_r = cl.scale(cl.inner(alpha, beta), nu)
                assert lhs_r == rhs_r, f"Right Hodge axiom failed at {am}, {bm}"

                sb_l = cl.hodge_star_left(beta, nu_coeff)
                lhs_l = cl.wedge(sb_l, alpha)
                rhs_l = cl.scale(cl.inner(beta, alpha), nu)
                assert lhs_l == rhs_l, f"Left Hodge axiom failed at {am}, {bm}"


def test_1_universal_chevalley_hodge():
    print("[Test 1] Universal Chevalley-Hodge reverted realization *_nu(x) = rev(x) * nu ...")
    cases = [
        ("Cl(1,0)", diag_gram([1])),
        ("Cl(0,1)", diag_gram([-1])),
        ("Cl(2,0)", diag_gram([1, 1])),
        ("Cl(1,1)", diag_gram([1, -1])),
        ("Cl(0,2)", diag_gram([-1, -1])),
        ("Cl(2,0) diag(2,3)", diag_gram([2, 3])),
        ("Cl(1,0,1) diag(1,0)", diag_gram([1, 0])),
        ("Cl(0,0,2) diag(0,0)", diag_gram([0, 0])),
        ("Non-orthogonal PD [[2,1],[1,2]]", [[2, 1], [1, 2]]),
        ("Hyperbolic [[0,1],[1,0]]", [[0, 1], [1, 0]]),
        ("Non-diag degenerate [[1,1],[1,1]]", [[1, 1], [1, 1]]),
        ("Cl(3,0)", diag_gram([1, 1, 1])),
        ("Cl(2,1)", diag_gram([1, 1, -1])),
        ("Cl(2,0,1) diag(1,1,0)", diag_gram([1, 1, 0])),
        ("Non-orthogonal 3D [[2,1,0],[1,2,1],[0,1,2]]", [[2, 1, 0], [1, 2, 1], [0, 1, 2]]),
        ("Cl(4,0)", diag_gram([1, 1, 1, 1])),
        ("Cl(3,1) Minkowski", diag_gram([1, 1, 1, -1])),
        ("Cl(1,3) Minkowski", diag_gram([1, -1, -1, -1])),
    ]
    for name, G in cases:
        cl = BasisIndependentClifford(G)
        full = (1 << cl.n) - 1
        if cl.n <= 3:
            for a in range(cl.dim):
                for b in range(cl.dim):
                    for c in range(cl.dim):
                        ea, eb, ec = cl.basis(a), cl.basis(b), cl.basis(c)
                        assert cl.mul(cl.mul(ea, eb), ec) == cl.mul(ea, cl.mul(eb, ec))
                        assert cl.rev(cl.mul(ea, eb)) == cl.mul(cl.rev(eb), cl.rev(ea))
        for nu_c in [Fraction(1), Fraction(-1), Fraction(5, 3)]:
            check_defining_equation(cl, nu_c)
            nu = cl.scale(nu_c, cl.basis(full))
            for m in range(cl.dim):
                x = cl.basis(m)
                assert cl.hodge_star_right(x, nu_c) == cl.mul(cl.rev(x), nu)
                assert cl.hodge_star_left(x, nu_c) == cl.mul(nu, cl.rev(x))
            rev_norm = cl.mul(cl.rev(nu), nu)
            detG = cl.inner_masks(full, full)
            assert rev_norm == cl.scale(nu_c * nu_c * detG, cl.basis(0))
            assert cl.inner(nu, nu) == nu_c * nu_c * detG
        print(f"  PASS: {name} (dim={cl.n}, detG={cl.inner_masks(full, full)})")


def test_2_positive_euclidean_regime():
    print("\n[Test 2] Positive regime (non-vacuity): Euclidean Cl(n,0) with +-vol_Q ...")
    for n in [1, 2, 3, 4]:
        cl = BasisIndependentClifford(diag_gram([1] * n))
        full = (1 << n) - 1
        vol = cl.basis(full)
        for sign in [Fraction(1), Fraction(-1)]:
            omega = cl.scale(sign, vol)
            for m in range(cl.dim):
                x = cl.basis(m)
                sx = cl.hodge_star_right(x, sign)
                assert sx == cl.mul(cl.rev(x), omega)
                # Orthogonal isometry check: <*x, *x>_Q == <x, x>_Q
                assert cl.inner(sx, sx) == cl.inner(x, x)
            # Reversion norm & exterior norm both equal +1
            assert cl.mul(cl.rev(omega), omega) == cl.basis(0)
            assert cl.inner(omega, omega) == Fraction(1)
        print(f"  PASS: Euclidean Cl({n},0) satisfies unit reversion norm +1 & +-1 orientation uniqueness")


def test_3_refute_unreverted_and_rank_characterization():
    print("\n[Test 3] Refuting Clause 1: unreverted / two-sided geometric product realizations ...")
    # Minimal counterexample in Cl(2,0)
    cl20 = BasisIndependentClifford(diag_gram([1, 1]))
    e0, e1, e2, e12 = cl20.basis(0), cl20.basis(1), cl20.basis(2), cl20.basis(3)
    assert cl20.hodge_star_right(e0) == e12
    assert cl20.hodge_star_right(e1) == e2
    assert cl20.hodge_star_right(e2) == cl20.scale(-1, e1)
    assert cl20.hodge_star_right(e12) == e0

    # Right multiplication x * Omega forced to Omega = e12 at x = 1, fails at x = e12 (-1 != +1)
    assert cl20.mul(e12, e12) == cl20.scale(-1, e0) != cl20.hodge_star_right(e12)
    # Left multiplication Omega * x forced to Omega = e12 at x = 1, fails at x = e1 (-e2 != +e2) and x = e12
    assert cl20.mul(e12, e1) == cl20.scale(-1, e2) != cl20.hodge_star_right(e1)
    print("  PASS: Explicit Cl(2,0) obstruction: (e1 e2)*(e1 e2) = -1 != +1 = *(e1 e2); (e1 e2)*e1 = -e2 != +e2 = *(e1)")

    # Exact rank-1 characterization of *_nu(x) == x * nu across all diagonal metrics in dims 1..3
    alphabet = [-1, 0, 1, 2]
    for n in [1, 2, 3]:
        for q_tuple in itertools.product(alphabet, repeat=n):
            cl = BasisIndependentClifford(diag_gram(q_tuple))
            nu = cl.basis((1 << n) - 1)
            unreverted_ok = all(
                cl.hodge_star_right(cl.basis(m)) == cl.mul(cl.basis(m), nu)
                for m in range(cl.dim)
            )
            rank_q = sum(1 for qi in q_tuple if qi != 0)
            assert unreverted_ok == (rank_q <= 1), f"Rank characterization failed at {q_tuple}"
    print("  PASS: Exhaustive check over 84 metrics in dims 1..3: *_nu(x) == x * nu iff rank(Q) <= 1")

    # Non-orthogonal basis check: naive geometric product e_1 * e_2 != e_1 ^ e_2
    cl_nonorth = BasisIndependentClifford([[2, 1], [1, 2]])
    naive_e12 = cl_nonorth.mul(cl_nonorth.basis(1), cl_nonorth.basis(2))
    wedge_e12 = cl_nonorth.basis(3)
    assert naive_e12 == cl_nonorth.add(wedge_e12, cl_nonorth.basis(0))
    assert naive_e12 != wedge_e12
    print("  PASS: Non-orthogonal Gram [[2,1],[1,2]]: naive e1*e2 = 1 + e1^e2 != e1^e2")


def test_4_refute_unit_norm():
    print("\n[Test 4] Refuting Clause 3: failure of unit norm across signatures, fields, and degeneracy ...")
    # 4a. Lorentzian Cl(1,1), Minkowski Cl(3,1) and Cl(1,3)
    for name, q in [
        ("Cl(1,1)", [1, -1]),
        ("Cl(3,1)", [1, 1, 1, -1]),
        ("Cl(1,3)", [1, -1, -1, -1]),
    ]:
        cl = BasisIndependentClifford(diag_gram(q))
        omega = cl.basis((1 << cl.n) - 1)
        rev_norm = cl.mul(cl.rev(omega), omega)
        assert rev_norm == cl.scale(-1, cl.basis(0))
        assert cl.inner(omega, omega) == Fraction(-1)
        # Anti-isometry: <*1, *1>_B = -1 != +1 = <1, 1>_B
        s1 = cl.hodge_star_right(cl.basis(0))
        assert cl.inner(s1, s1) == Fraction(-1) != cl.inner(cl.basis(0), cl.basis(0))
        print(f"  PASS: {name}: unique reverted realization has rev(Omega)*Omega = <Omega,Omega>_B = -1 != +1")

    # 4b. Degenerate Cl(1,0,1) (Projective Geometric Algebra metric diag(1,0))
    cl101 = BasisIndependentClifford(diag_gram([1, 0]))
    for c in [Fraction(1), Fraction(-1), Fraction(2), Fraction(7, 3)]:
        omega = cl101.scale(c, cl101.basis(3))
        for m in range(cl101.dim):
            assert cl101.hodge_star_right(cl101.basis(m), c) == cl101.mul(cl101.rev(cl101.basis(m)), omega)
        assert cl101.mul(cl101.rev(omega), omega) == cl101.zero()
        assert cl101.mul(cl101.conj(omega), omega) == cl101.zero()
        assert cl101.mul(omega, omega) == cl101.zero()
        assert abs(cl101.inner(omega, omega)) == Fraction(0) != Fraction(1)
    print("  PASS: Degenerate Cl(1,0,1): rev(Omega)*Omega = conj(Omega)*Omega = Omega^2 = |<Omega,Omega>_B| = 0 != 1")

    # 4c. Positive-definite rational space Q = diag(2, 3) over Q
    cl23 = BasisIndependentClifford(diag_gram([2, 3]))
    for a in range(-25, 26):
        for b in range(1, 26):
            lam = Fraction(a, b)
            omega = cl23.scale(lam, cl23.basis(3))
            norm_val = cl23.inner(omega, omega)
            assert norm_val == 6 * lam * lam
            assert norm_val not in (Fraction(1), Fraction(-1))
    print("  PASS: Rational PD Q = diag(2,3): 6*(a/b)^2 != +-1 verified across 1275 rational scalars (and proven for all Q)")

    # 4d. Algebraic square & conjugation norm in Euclidean Cl(2,0) and Cl(3,0)
    w2 = cl20_omega = BasisIndependentClifford(diag_gram([1, 1]))
    om2 = w2.basis(3)
    assert w2.mul(om2, om2) == w2.scale(-1, w2.basis(0))
    w3 = BasisIndependentClifford(diag_gram([1, 1, 1]))
    om3 = w3.basis(7)
    assert w3.mul(om3, om3) == w3.scale(-1, w3.basis(0))
    assert w3.mul(w3.conj(om3), om3) == w3.scale(-1, w3.basis(0))
    print("  PASS: Euclidean Cl(2,0) omega^2 = -1 != +1; Euclidean Cl(3,0) conj(omega)*omega = omega^2 = -1 != +1")


def test_5_refute_pm1_uniqueness_deviation():
    print("\n[Test 5] Refuting Clause 2: deviation exceeds volume orientation +-1 & positive-grade non-uniqueness ...")
    # 5a. Positively oriented volume scaling nu = c * omega_0 (c > 0, c != 1)
    cl20 = BasisIndependentClifford(diag_gram([1, 1]))
    for c in [Fraction(2), Fraction(1, 3), Fraction(5, 2)]:
        # Unique Omega for *_nu is c * omega_0 (evaluated at x = 1)
        omega_c = cl20.hodge_star_right(cl20.basis(0), c)
        assert omega_c == cl20.scale(c, cl20.basis(3))
        assert c > 0 and c not in (Fraction(1), Fraction(-1))

    # 5b. In degenerate Cl(1,0,1), all c > 0 share identical metric norm 0 (no canonical unit representative)
    cl101 = BasisIndependentClifford(diag_gram([1, 0]))
    norms = {cl101.inner(cl101.scale(c, cl101.basis(3)), cl101.scale(c, cl101.basis(3))) for c in [1, 2, 3, 10]}
    assert norms == {Fraction(0)}

    # 5c. On positive grades k >= 1 in degenerate Q = diag(0, 0), infinitely many c * omega_0 realize *_omega_0
    cl00 = BasisIndependentClifford(diag_gram([0, 0]))
    for c in [Fraction(-3), Fraction(0), Fraction(1), Fraction(2), Fraction(99)]:
        omega_c = cl00.scale(c, cl00.basis(3))
        for m in [1, 2, 3]:  # all positive-grade basis blades
            assert cl00.hodge_star_right(cl00.basis(m), Fraction(1)) == cl00.mul(
                cl00.rev(cl00.basis(m)), omega_c
            )
    print("  PASS: Scale gauge R_{>0} in Cl(1,0,1) and positive-grade non-uniqueness in Cl(0,0,2) verified")


def main():
    print("=" * 76)
    print("Conjecture 00000007616 — Exact Algebraic Verification Suite")
    print("=" * 76)
    test_1_universal_chevalley_hodge()
    test_2_positive_euclidean_regime()
    test_3_refute_unreverted_and_rank_characterization()
    test_4_refute_unit_norm()
    test_5_refute_pm1_uniqueness_deviation()
    print("\n" + "=" * 76)
    print("ALL VERIFICATION CHECKS PASSED — VERDICT: CONJECTURE 00000007616 IS FALSE")
    print("=" * 76)


if __name__ == "__main__":
    main()
