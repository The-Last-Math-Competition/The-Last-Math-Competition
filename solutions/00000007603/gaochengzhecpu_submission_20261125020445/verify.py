#!/usr/bin/env python3
"""Independent computational verification for Conjecture 00000007603.

Uses only the Python 3 standard library (`fractions`, `math`, `random`, `sys`)
to verify:
1. Isomorphism between the recursive tuple Clifford algebra (matching Core Lean 4)
   and the standard bitmask basis-blade Clifford algebra Cl(p, q).
2. Positive non-vacuity identities: positive-definite norm coincidences,
   grade-1 Euclidean vector-pair & versor multiplicativity, Hurwitz composition
   laws on Cl(0,0), Cl(0,1), Cl(0,2), and 2D conjugation determinant laws.
3. Exact rational counterexamples refuting Clauses I and III across all standard
   norm conventions (`||.||_2^2`, `N_rev`, `N_conj`) in Cl(n,0), Cl(0,n),
   even subalgebra Cl(4,0)^+, and indefinite grade-1 vector pairs in Cl(1,1).
4. Exact refutations of Clause II (unit-norm / Pin groups vs. isometry group O(p,q)),
   including the `{+1, -1}` double-cover kernel, Cl(0,1) cardinality/infinity mismatch,
   and the rational non-Pin algebraic unit `3/5 + (4/5) e_1 e_2 e_3` in Cl(3,0).
5. Exact Bott-periodicity conversion constants `C(p, q) = 2^{(p+q+delta(p-q mod 8))/2}`
   for all 21 signatures with `0 <= p + q <= 5`, verified both via exact primitive
   idempotent attainment (`Fraction`) and numerical singular-vector maximization.
"""

from __future__ import annotations

from fractions import Fraction
import math
import random
import sys
from typing import List, Sequence, Tuple


class BitmaskClifford:
    """Clifford algebra Cl(sig) with basis blades indexed by bitmasks `0 .. 2^n - 1`.
    Here `sig[i]` is `e_i^2` for `0 <= i < n`.
    """

    def __init__(self, sig: Sequence[int]):
        self.sig = list(sig)
        self.n = len(self.sig)
        self.dim = 1 << self.n
        self.mul_sign = [[0] * self.dim for _ in range(self.dim)]
        self.mul_idx = [[0] * self.dim for _ in range(self.dim)]
        for a in range(self.dim):
            for b in range(self.dim):
                s = 1
                for j in range(self.n):
                    if (a >> j) & 1:
                        swaps = (b & ((1 << j) - 1)).bit_count()
                        if swaps & 1:
                            s = -s
                        if (b >> j) & 1:
                            s *= self.sig[j]
                self.mul_sign[a][b] = s
                self.mul_idx[a][b] = a ^ b

    def basis(self, mask: int, coeff=1) -> list:
        v = [0] * self.dim
        v[mask] = coeff
        return v

    def add(self, x: Sequence, y: Sequence) -> list:
        return [xa + ya for xa, ya in zip(x, y)]

    def sub(self, x: Sequence, y: Sequence) -> list:
        return [xa - ya for xa, ya in zip(x, y)]

    def smul(self, r, x: Sequence) -> list:
        return [r * xa for xa in x]

    def mul(self, x: Sequence, y: Sequence) -> list:
        res = [0] * self.dim
        for a, xa in enumerate(x):
            if xa == 0:
                continue
            for b, yb in enumerate(y):
                if yb == 0:
                    continue
                res[self.mul_idx[a][b]] += self.mul_sign[a][b] * xa * yb
        return res

    def involute(self, x: Sequence) -> list:
        return [(-xa if (a.bit_count() & 1) else xa) for a, xa in enumerate(x)]

    def reverse(self, x: Sequence) -> list:
        res = []
        for a, xa in enumerate(x):
            k = a.bit_count()
            res.append(-xa if ((k * (k - 1) // 2) & 1) else xa)
        return res

    def conjugate(self, x: Sequence) -> list:
        res = []
        for a, xa in enumerate(x):
            k = a.bit_count()
            res.append(-xa if ((k * (k + 1) // 2) & 1) else xa)
        return res

    def l2_norm_sq(self, x: Sequence):
        return sum(xa * xa for xa in x)

    def rev_norm(self, x: Sequence):
        return self.mul(self.reverse(x), x)[0]

    def conj_norm(self, x: Sequence):
        return self.mul(self.conjugate(x), x)[0]

    def quad_form(self, vec_coords: Sequence) -> int | Fraction:
        return sum(c * v * v for c, v in zip(self.sig, vec_coords))

    def of_vec(self, vec_coords: Sequence) -> list:
        res = [0] * self.dim
        for i, val in enumerate(vec_coords):
            res[1 << i] = val
        return res


# --- Recursive Tuple Model (exact mirror of Lean's `Cl R sig`) ---

def lean_add(sig: list[int], x, y):
    if not sig:
        return x + y
    return (lean_add(sig[1:], x[0], y[0]), lean_add(sig[1:], x[1], y[1]))


def lean_neg(sig: list[int], x):
    if not sig:
        return -x
    return (lean_neg(sig[1:], x[0]), lean_neg(sig[1:], x[1]))


def lean_smul(sig: list[int], r, x):
    if not sig:
        return r * x
    return (lean_smul(sig[1:], r, x[0]), lean_smul(sig[1:], r, x[1]))


def lean_involute(sig: list[int], x):
    if not sig:
        return x
    return (lean_involute(sig[1:], x[0]), lean_neg(sig[1:], lean_involute(sig[1:], x[1])))


def lean_rev(sig: list[int], x):
    if not sig:
        return x
    return (lean_rev(sig[1:], x[0]), lean_involute(sig[1:], lean_rev(sig[1:], x[1])))


def lean_conj(sig: list[int], x):
    if not sig:
        return x
    return (lean_conj(sig[1:], x[0]), lean_neg(sig[1:], lean_involute(sig[1:], lean_conj(sig[1:], x[1]))))


def lean_mul(sig: list[int], x, y):
    if not sig:
        return x * y
    c, cs = sig[0], sig[1:]
    x0, x1 = x
    y0, y1 = y
    return (
        lean_add(cs, lean_mul(cs, x0, y0), lean_smul(cs, c, lean_mul(cs, x1, lean_involute(cs, y1)))),
        lean_add(cs, lean_mul(cs, x0, y1), lean_mul(cs, x1, lean_involute(cs, y0))),
    )


def lean_l2(sig: list[int], x):
    if not sig:
        return x * x
    return lean_l2(sig[1:], x[0]) + lean_l2(sig[1:], x[1])


def bitmask_to_lean(sig: list[int], bm_vec: list):
    """Map bitmask basis representation of Cl(reversed(sig)) to Lean's outer-first `Cl R sig`.
    In `Cl R (c :: cs)`, the newly adjoined outer generator `c` corresponds to the highest bit `n - 1`
    in `Cl(cs_reversed + [c])`, where `e_{i_1} ... e_{i_k}` is ordered from inner to outer!
    """
    if not sig:
        return bm_vec[0]
    half = len(bm_vec) // 2
    return (bitmask_to_lean(sig[1:], bm_vec[:half]), bitmask_to_lean(sig[1:], bm_vec[half:]))


def test_1_lean_bitmask_isomorphism(rng: random.Random) -> None:
    print("[1/5] Verifying isomorphism between Lean recursive model and bitmask Cl(p, q)...")
    checked = 0
    for n in range(0, 5):
        for p in range(n + 1):
            q = n - p
            # Inner-to-outer signature for bitmask vs outer-to-inner list for Lean:
            bm_sig = [1] * p + [-1] * q
            lean_sig = list(reversed(bm_sig))
            cl = BitmaskClifford(bm_sig)
            for _ in range(25):
                x = [rng.randint(-4, 4) for _ in range(cl.dim)]
                y = [rng.randint(-4, 4) for _ in range(cl.dim)]
                lx = bitmask_to_lean(lean_sig, x)
                ly = bitmask_to_lean(lean_sig, y)
                assert bitmask_to_lean(lean_sig, cl.mul(x, y)) == lean_mul(lean_sig, lx, ly)
                assert bitmask_to_lean(lean_sig, cl.involute(x)) == lean_involute(lean_sig, lx)
                assert bitmask_to_lean(lean_sig, cl.reverse(x)) == lean_rev(lean_sig, lx)
                assert bitmask_to_lean(lean_sig, cl.conjugate(x)) == lean_conj(lean_sig, lx)
                assert cl.l2_norm_sq(x) == lean_l2(lean_sig, lx)
                checked += 1
    print(f"      PASS ({checked} randomized algebra/involution/norm checks across 0 <= p+q <= 4).")


def test_2_positive_domain(rng: random.Random) -> None:
    print("[2/5] Verifying positive non-vacuity theorems (vectors, versors, Hurwitz n <= 2)...")
    # (a) Norm coincidences and Euclidean vector-pair & versor multiplicativity
    for n in range(0, 6):
        cl_euc = BitmaskClifford([1] * n)
        cl_spin = BitmaskClifford([-1] * n)
        for _ in range(30):
            x = [rng.randint(-5, 5) for _ in range(cl_euc.dim)]
            assert cl_euc.rev_norm(x) == cl_euc.l2_norm_sq(x)
            assert cl_spin.conj_norm(x) == cl_spin.l2_norm_sq(x)
        if n >= 1:
            for _ in range(30):
                u_c = [rng.randint(-5, 5) for _ in range(n)]
                v_c = [rng.randint(-5, 5) for _ in range(n)]
                u = cl_euc.of_vec(u_c)
                v = cl_euc.of_vec(v_c)
                uv = cl_euc.mul(u, v)
                dot = sum(a * b for a, b in zip(u_c, v_c))
                wedge_sq = sum(
                    (u_c[i] * v_c[j] - u_c[j] * v_c[i]) ** 2
                    for i in range(n)
                    for j in range(i + 1, n)
                )
                assert uv[0] == dot
                assert cl_euc.l2_norm_sq(uv) == dot * dot + wedge_sq
                assert cl_euc.l2_norm_sq(uv) == cl_euc.quad_form(u_c) * cl_euc.quad_form(v_c)
                # Versor of length 3 times arbitrary multivector Y
                w3_c = [rng.randint(-3, 3) for _ in range(n)]
                vers = cl_euc.mul(uv, cl_euc.of_vec(w3_c))
                y = [rng.randint(-3, 3) for _ in range(cl_euc.dim)]
                vy = cl_euc.mul(vers, y)
                assert cl_euc.l2_norm_sq(vy) == cl_euc.l2_norm_sq(vers) * cl_euc.l2_norm_sq(y)

    # (b) Hurwitz Cl(0,0), Cl(0,1), Cl(0,2) and general 2D conjugation determinant law
    for n in (0, 1, 2):
        cl_h = BitmaskClifford([-1] * n)
        for _ in range(50):
            x = [rng.randint(-6, 6) for _ in range(cl_h.dim)]
            y = [rng.randint(-6, 6) for _ in range(cl_h.dim)]
            xy = cl_h.mul(x, y)
            assert cl_h.l2_norm_sq(xy) == cl_h.l2_norm_sq(x) * cl_h.l2_norm_sq(y)

    for sig2 in ([1, 1], [1, -1], [-1, -1]):
        cl2 = BitmaskClifford(sig2)
        for _ in range(40):
            x = [rng.randint(-6, 6) for _ in range(4)]
            y = [rng.randint(-6, 6) for _ in range(4)]
            assert cl2.conj_norm(cl2.mul(x, y)) == cl2.conj_norm(x) * cl2.conj_norm(y)
    print("      PASS (Euclidean vector/versor laws for 0 <= n <= 5 and Hurwitz laws for n <= 2).")


def test_3_multivector_and_indefinite_refutations() -> None:
    print("[3/5] Verifying exact counterexamples for Clauses I and III across all norms...")
    # (a) Cl(n, 0) for 1 <= n <= 5: X_+ = 1 + e_1, X_- = 1 - e_1
    for n in range(1, 6):
        cl = BitmaskClifford([1] * n)
        xp = cl.add(cl.basis(0), cl.basis(1))
        xm = cl.sub(cl.basis(0), cl.basis(1))
        xp2 = cl.mul(xp, xp)
        xpxm = cl.mul(xp, xm)
        assert cl.l2_norm_sq(xp) == 2 and cl.rev_norm(xp) == 2
        assert cl.l2_norm_sq(xm) == 2 and cl.rev_norm(xm) == 2
        assert cl.l2_norm_sq(xp2) == 8 and cl.rev_norm(xp2) == 8
        assert cl.l2_norm_sq(xpxm) == 0 and all(v == 0 for v in xpxm)

    # (b) Cl(0, n) for 3 <= n <= 5: X_+- = 1 +- e_1 e_2 e_3; W = 1 + e_1 for N_rev
    for n in range(3, 6):
        cl = BitmaskClifford([-1] * n)
        xp = cl.add(cl.basis(0), cl.basis(0b111))
        xm = cl.sub(cl.basis(0), cl.basis(0b111))
        xp2 = cl.mul(xp, xp)
        xpxm = cl.mul(xp, xm)
        assert cl.l2_norm_sq(xp) == 2 and cl.conj_norm(xp) == 2
        assert cl.l2_norm_sq(xp2) == 8 and cl.conj_norm(xp2) == 8
        assert cl.l2_norm_sq(xpxm) == 0 and all(v == 0 for v in xpxm)
        w = cl.add(cl.basis(0), cl.basis(1))
        assert cl.rev_norm(w) == 0 and cl.rev_norm(cl.mul(w, w)) == -4

    # (c) Cl(3, 0): Z = 1 + e_1 e_2 e_3 refutes N_conj
    cl30 = BitmaskClifford([1, 1, 1])
    z = cl30.add(cl30.basis(0), cl30.basis(0b111))
    assert cl30.conj_norm(z) == 0 and cl30.conj_norm(cl30.mul(z, z)) == -4

    # (d) Cl(n, 0) for n = 4, 5: even element X_+- = 1 +- e_1 e_2 e_3 e_4 refutes ALL THREE norms!
    for n in (4, 5):
        cl = BitmaskClifford([1] * n)
        xp = cl.add(cl.basis(0), cl.basis(0b1111))
        xm = cl.sub(cl.basis(0), cl.basis(0b1111))
        assert cl.involute(xp) == xp and cl.involute(xm) == xm
        xp2 = cl.mul(xp, xp)
        xpxm = cl.mul(xp, xm)
        for fn in (cl.l2_norm_sq, cl.rev_norm, cl.conj_norm):
            assert fn(xp) == 2 and fn(xm) == 2
            assert fn(xp2) == 8 and fn(xpxm) == 0

    # (e) Indefinite Cl(1, 1) on grade-1 vector pairs: u = e_1 + e_2, v = e_1 - e_2
    cl11 = BitmaskClifford([1, -1])
    u = cl11.of_vec([1, 1])
    v = cl11.of_vec([1, -1])
    uv = cl11.mul(u, v)
    u2 = cl11.mul(u, u)
    assert cl11.quad_form([1, 1]) == 0 and cl11.quad_form([1, -1]) == 0
    assert uv == [2, 0, 0, -2] and any(uv)
    assert cl11.l2_norm_sq(u) == 2 and cl11.l2_norm_sq(v) == 2
    assert cl11.l2_norm_sq(uv) == 8 and cl11.l2_norm_sq(u2) == 0
    assert cl11.rev_norm(uv) == 0  # nonzero element with zero reversal norm
    print("      PASS (All Euclidean, Spin-Euclidean, even-subalgebra, and indefinite refutations verified).")


def test_4_spectrum_and_isometry_group() -> None:
    print("[4/5] Verifying refutations of Clause II (unit-norm / Pin groups vs. O(p, q))...")
    # (a) Cl(0, 1) ~= C: Pin(0, 1) = {+-1, +-e_1} has size 4 > |O(1)| = 2, and rational S^1 is infinite
    cl01 = BitmaskClifford([-1])
    pin01 = [[1, 0], [-1, 0], [0, 1], [0, -1]]
    assert len({tuple(u) for u in pin01}) == 4
    for u in pin01:
        assert cl01.mul(cl01.conjugate(u), u) == [1, 0] and cl01.l2_norm_sq(u) == 1
    seen_circle_pts = set()
    for k in range(1, 30):
        pt = (Fraction(k * k - 1, k * k + 1), Fraction(2 * k, k * k + 1))
        u = list(pt)
        assert cl01.mul(cl01.conjugate(u), u) == [Fraction(1), Fraction(0)]
        seen_circle_pts.add(pt)
    assert len(seen_circle_pts) == 29

    # (b) Cl(3, 0): rational non-Pin unit U = 3/5 + (4/5) e_1 e_2 e_3
    cl30 = BitmaskClifford([1, 1, 1])
    u = [Fraction(0)] * 8
    u[0] = Fraction(3, 5)
    u[0b111] = Fraction(4, 5)
    u_rev = cl30.reverse(u)
    u_inv = cl30.involute(u)
    assert cl30.mul(u_rev, u) == [Fraction(1)] + [Fraction(0)] * 7
    assert cl30.l2_norm_sq(u) == Fraction(1)
    # Untwisted conjugation fixes all basis vectors e_1, e_2, e_3:
    for i in range(3):
        ei = cl30.basis(1 << i, Fraction(1))
        assert cl30.mul(cl30.mul(u, ei), u_rev) == ei
    # Twisted conjugation sends e_1 to -7/25 e_1 - 24/25 e_2 e_3 (leaves grade-1 subspace V!):
    e1 = cl30.basis(1, Fraction(1))
    twisted_e1 = cl30.mul(cl30.mul(u_inv, e1), u_rev)
    assert twisted_e1[1] == Fraction(-7, 25) and twisted_e1[0b110] == Fraction(-24, 25)
    non_grade1_support = [a for a, val in enumerate(twisted_e1) if val != 0 and a.bit_count() != 1]
    assert non_grade1_support == [0b110]
    print("      PASS (Double-cover kernel, Cl(0,1) infinite S^1, and Cl(3,0) non-Pin unit verified).")


def bott_conversion_constant(p: int, q: int) -> int:
    """Exact optimal L2 conversion constant `C(p, q) = 2^{(p + q + delta((p - q) mod 8)) / 2}`."""
    delta = {0: 0, 1: 1, 2: 0, 3: -1, 4: -2, 5: -1, 6: -2, 7: -1}
    s = (p - q) % 8
    return 1 << ((p + q + delta[s]) // 2)


def test_5_bott_periodicity_constants(rng: random.Random) -> None:
    print("[5/5] Verifying exact Bott-periodicity conversion constants C(p, q) for 0 <= p+q <= 5...")
    print("      Signature   C(p,q)   Idempotent Ratio   Sampled Max Ratio")
    for n in range(0, 6):
        for p in range(n, -1, -1):
            q = n - p
            c_exact = bott_conversion_constant(p, q)
            r_exp = int(round(math.log2(c_exact)))
            cl = BitmaskClifford([1] * p + [-1] * q)
            pos_blades = [a for a in range(1, cl.dim) if cl.mul_sign[a][a] == 1]

            def find_commuting_involutions(chosen: list[int], start: int) -> list[int] | None:
                if len(chosen) == r_exp:
                    return chosen
                span = {0}
                for g in chosen:
                    span |= {x ^ g for x in list(span)}
                for idx in range(start, len(pos_blades)):
                    cand = pos_blades[idx]
                    if cand in span:
                        continue
                    if all(cl.mul_sign[cand][g] == cl.mul_sign[g][cand] for g in chosen):
                        found = find_commuting_involutions(chosen + [cand], idx + 1)
                        if found is not None:
                            return found
                return None

            gens = find_commuting_involutions([], 0)
            assert gens is not None, f"Missing {r_exp} commuting involutions in Cl({p},{q})"
            idem = cl.basis(0, Fraction(1))
            for g in gens:
                idem = cl.mul(idem, cl.smul(Fraction(1, 2), cl.add(cl.basis(0, Fraction(1)), cl.basis(g, Fraction(1)))))
            idem_sq = cl.mul(idem, idem)
            assert idem_sq == idem  # exact idempotent P^2 = P!
            exact_ratio = cl.l2_norm_sq(idem_sq) / (cl.l2_norm_sq(idem) ** 2)
            assert exact_ratio == Fraction(c_exact)

            # Numerical alternating singular-vector maximization check
            max_num = 0.0
            for _ in range(12):
                x = [rng.gauss(0.0, 1.0) for _ in range(cl.dim)]
                nx = math.sqrt(cl.l2_norm_sq(x))
                x = [z / nx for z in x]
                y = [rng.gauss(0.0, 1.0) for _ in range(cl.dim)]
                ny = math.sqrt(cl.l2_norm_sq(y))
                y = [z / ny for z in y]
                for _ in range(35):
                    xy = cl.mul(x, y)
                    ny_v = [sum(xy[c ^ b] * cl.mul_sign[c][b] * x[c] for c in range(cl.dim)) for b in range(cl.dim)]
                    nrm = math.sqrt(sum(z * z for z in ny_v))
                    if nrm > 0:
                        y = [z / nrm for z in ny_v]
                    xy = cl.mul(x, y)
                    nx_v = [sum(xy[c ^ b] * cl.mul_sign[c][b] * y[b] for b in range(cl.dim)) for c in range(cl.dim)]
                    nrm = math.sqrt(sum(z * z for z in nx_v))
                    if nrm > 0:
                        x = [z / nrm for z in nx_v]
                max_num = max(max_num, cl.l2_norm_sq(cl.mul(x, y)))
            assert max_num <= c_exact + 1e-9
            assert abs(max_num - c_exact) < 1e-5
            print(f"      Cl({p},{q})      {c_exact:>4d}             {int(exact_ratio):>4d}          {max_num:>10.6f}")
    print("      PASS (All 21 Bott-periodicity conversion constants verified exactly and numerically).")


def main() -> int:
    rng = random.Random(7603)
    print("=== Verification Suite for Conjecture 00000007603 ===")
    test_1_lean_bitmask_isomorphism(rng)
    test_2_positive_domain(rng)
    test_3_multivector_and_indefinite_refutations()
    test_4_spectrum_and_isometry_group()
    test_5_bott_periodicity_constants(rng)
    print("=== ALL VERIFICATION CHECKS PASSED (EXIT CODE 0) ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())
