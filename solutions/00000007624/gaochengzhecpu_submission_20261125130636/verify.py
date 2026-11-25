"""Standalone computational verification suite for Conjecture 00000007624.

Verifies both the restricted positive theorems (grade-1 nilpotent-isotropic equivalence,
Sylvester nondegenerate signature and degenerate inertia criteria, and the polar
orthogonality criterion for null-vector sums) and all three counterexample families:
  1. Nonzero multivector nilpotents in strictly positive-definite Clifford algebras
     under BOTH sign conventions (+Q in Cl_{2,0} and -Q in Cl_{0,4}), plus the sharp
     classification of reduced vs. non-reduced signatures Cl_{p,q}.
  2. Failure of the null-vector sum construction in Cl_{1,1} (sum of two null vectors
     is an invertible unit, not nilpotent), contrasted with totally isotropic subspaces
     in Cl_{2,2}.
  3. Failure of the signature condition across degenerate real forms (inertia (p, 0, r)),
     complex/Gaussian-integer sums of squares, finite prime fields F_p (all odd primes
     p < 100), and rational Hasse-Minkowski obstructions in signatures (1,1) and (2,1).
"""

from __future__ import annotations

import itertools
import sys
from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class GaussInt:
    """Exact arithmetic in Gaussian integers Z[i]."""

    re: int
    im: int = 0

    def __add__(self, other: GaussInt | int) -> GaussInt:
        if isinstance(other, int):
            other = GaussInt(other, 0)
        return GaussInt(self.re + other.re, self.im + other.im)

    def __radd__(self, other: int) -> GaussInt:
        return self + other

    def __sub__(self, other: GaussInt | int) -> GaussInt:
        if isinstance(other, int):
            other = GaussInt(other, 0)
        return GaussInt(self.re - other.re, self.im - other.im)

    def __neg__(self) -> GaussInt:
        return GaussInt(-self.re, -self.im)

    def __mul__(self, other: GaussInt | int) -> GaussInt:
        if isinstance(other, int):
            other = GaussInt(other, 0)
        return GaussInt(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def __rmul__(self, other: int) -> GaussInt:
        return self * other

    def is_zero(self) -> bool:
        return self.re == 0 and self.im == 0


class CliffordAlgebra:
    """Exact 2^n-dimensional Clifford algebra Cl(g) for diagonal weights g = [g_0, ..., g_{n-1}]."""

    def __init__(self, weights: list, zero=0, one=1, mod: int | None = None):
        self.weights = list(weights)
        self.n = len(self.weights)
        self.dim = 1 << self.n
        self.zero = zero
        self.one = one
        self.mod = mod
        self._table = [
            [self._basis_mul(a, b) for b in range(self.dim)] for a in range(self.dim)
        ]

    def _norm(self, val):
        if self.mod is not None:
            return val % self.mod
        return val

    def _is_zero_scalar(self, val) -> bool:
        if isinstance(val, GaussInt):
            return val.is_zero()
        return self._norm(val) == 0

    def _basis_mul(self, a: int, b: int):
        sign = 1
        for i in range(self.n):
            if (a >> i) & 1:
                below = b & ((1 << i) - 1)
                if below.bit_count() % 2 == 1:
                    sign = -sign
        factor = self.one * sign
        common = a & b
        for i in range(self.n):
            if (common >> i) & 1:
                factor = self._norm(factor * self.weights[i])
        return factor, a ^ b

    def zero_elem(self) -> list:
        return [self.zero for _ in range(self.dim)]

    def one_elem(self) -> list:
        out = self.zero_elem()
        out[0] = self._norm(self.one)
        return out

    def scalar_elem(self, r) -> list:
        out = self.zero_elem()
        out[0] = self._norm(r)
        return out

    def basis_blade(self, mask: int) -> list:
        out = self.zero_elem()
        out[mask] = self._norm(self.one)
        return out

    def embed_vec(self, coords: list) -> list:
        assert len(coords) == self.n
        out = self.zero_elem()
        for i, c in enumerate(coords):
            out[1 << i] = self._norm(c)
        return out

    def quad_form(self, coords: list):
        total = self.zero
        for w, x in zip(self.weights, coords):
            total = self._norm(total + w * x * x)
        return total

    def polar_form(self, u: list, v: list):
        total = self.zero
        for w, x, y in zip(self.weights, u, v):
            total = self._norm(total + w * x * y)
        return total

    def add(self, x: list, y: list) -> list:
        return [self._norm(a + b) for a, b in zip(x, y)]

    def mul(self, x: list, y: list) -> list:
        out = self.zero_elem()
        for a, xa in enumerate(x):
            if self._is_zero_scalar(xa):
                continue
            row = self._table[a]
            for b, yb in enumerate(y):
                if self._is_zero_scalar(yb):
                    continue
                factor, c = row[b]
                if not self._is_zero_scalar(factor):
                    out[c] = self._norm(out[c] + factor * xa * yb)
        return out

    def power(self, x: list, k: int) -> list:
        res = self.one_elem()
        for _ in range(k):
            res = self.mul(res, x)
        return res

    def is_zero(self, x: list) -> bool:
        return all(self._is_zero_scalar(c) for c in x)

    def eq(self, x: list, y: list) -> bool:
        return all(self._is_zero_scalar(a - b) for a, b in zip(x, y))


def verify_positive_theorems() -> None:
    print("[1/5] Verifying positive theorems (Clifford axioms, grade-1 equivalence, signature)...")
    for weights in ([1, 1], [-1, -1, -1], [1, -1], [1, -1, 0]):
        cl = CliffordAlgebra(weights)
        # Associativity on all basis triples when dim <= 8 (or sampled/all for dim <= 8)
        if cl.dim <= 8:
            blades = [cl.basis_blade(m) for m in range(cl.dim)]
            for a in blades:
                for b in blades:
                    ab = cl.mul(a, b)
                    for c in blades:
                        assert cl.eq(cl.mul(ab, c), cl.mul(a, cl.mul(b, c))), (
                            f"Associativity failed for weights={weights}"
                        )
        # Fundamental Clifford relation and grade-1 nilpotent <-> isotropic check
        for coords_t in itertools.product([-2, -1, 0, 1, 2], repeat=cl.n):
            coords = list(coords_t)
            ev = cl.embed_vec(coords)
            qf = cl.quad_form(coords)
            assert cl.eq(cl.mul(ev, ev), cl.scalar_elem(qf))
            if any(c != 0 for c in coords):
                is_iso = qf == 0
                assert not cl.is_zero(cl.power(ev, 1))
                for k in range(2, 6):
                    is_nil_k = cl.is_zero(cl.power(ev, k))
                    assert is_nil_k == is_iso, (
                        f"Grade-1 nilpotency mismatch at k={k}, v={coords}, weights={weights}"
                    )

    # Sylvester canonical signature & inertia theorem check on small dimensions
    for p in range(4):
        for q in range(4):
            if p + q > 4:
                continue
            cl = CliffordAlgebra([1] * p + [-1] * q)
            found_iso = False
            for coords_t in itertools.product([-1, 0, 1], repeat=cl.n):
                if any(coords_t) and cl.quad_form(list(coords_t)) == 0:
                    found_iso = True
                    break
            assert found_iso == (p >= 1 and q >= 1), f"Signature check failed at ({p},{q})"
    print("      PASS: Associativity, v^2 = Q(v)*1, grade-1 nilpotency, and signature verified.")


def verify_positive_definite_nilpotents_and_classification() -> None:
    print("[2/5] Verifying positive-definite nilpotents (+Q and -Q) and (p,q) classification...")
    # 1A: Cl_{2,0} (+Q convention: e1^2 = +1, e2^2 = +1)
    cl20 = CliffordAlgebra([1, 1])
    for x1, x2 in itertools.product(range(-5, 6), repeat=2):
        if (x1, x2) != (0, 0):
            assert cl20.quad_form([x1, x2]) > 0
    # Explicit nilpotent x = e1 + e1*e2 (mask 0b01 + mask 0b11)
    x_20 = cl20.add(cl20.basis_blade(0b01), cl20.basis_blade(0b11))
    assert not cl20.is_zero(x_20)
    assert cl20.is_zero(cl20.mul(x_20, x_20))
    # Also check (1 + e2)*e1 = e1 - e1*e2 (matching Lean's nilpotentCl20)
    x_20_lean = cl20.mul(
        cl20.add(cl20.one_elem(), cl20.basis_blade(0b10)), cl20.basis_blade(0b01)
    )
    assert not cl20.is_zero(x_20_lean)
    assert cl20.is_zero(cl20.mul(x_20_lean, x_20_lean))

    # 1B: Cl_{0,4} (-Q convention on positive-definite R^4: e_i^2 = -1 for i=1..4)
    cl04 = CliffordAlgebra([-1, -1, -1, -1])
    for vec in itertools.product([-2, -1, 0, 1, 2], repeat=4):
        if any(vec):
            assert cl04.quad_form(list(vec)) < 0  # -Q(v) < 0, zero isotropic vectors
    # Check (e1 e2 e3)^2 = +1
    omega3 = cl04.basis_blade(0b0111)
    assert cl04.eq(cl04.mul(omega3, omega3), cl04.one_elem())
    # Explicit nilpotent y = e4 + e1 e2 e3 e4 = (1 + e1 e2 e3) e4
    y_04 = cl04.add(cl04.basis_blade(0b1000), cl04.basis_blade(0b1111))
    assert not cl04.is_zero(y_04)
    assert cl04.is_zero(cl04.mul(y_04, y_04))

    # 1C: Complete (p, q) classification check
    reduced_set = {(0, 0), (1, 0), (0, 1), (0, 2), (0, 3)}
    for p, q in reduced_set:
        cl = CliffordAlgebra([1] * p + [-1] * q)
        vals = [-2, -1, 0, 1, 2] if cl.dim <= 4 else [-1, 0, 1]
        for coeff_t in itertools.product(vals, repeat=cl.dim):
            if any(coeff_t):
                elem = list(coeff_t)
                assert not cl.is_zero(cl.mul(elem, elem)), (
                    f"Unexpected square-zero element in Cl_{{{p},{q}}}"
                )

    for p in range(6):
        for q in range(6):
            if p + q > 5 or (p, q) in reduced_set:
                continue
            cl = CliffordAlgebra([1] * p + [-1] * q)
            if p >= 1 and q >= 1:
                coords = [0] * (p + q)
                coords[0] = 1
                coords[p] = 1
                witness = cl.embed_vec(coords)
            elif p >= 2 and q == 0:
                witness = cl.add(cl.basis_blade(0b01), cl.basis_blade(0b11))
            elif p == 0 and q >= 4:
                witness = cl.add(cl.basis_blade(0b1000), cl.basis_blade(0b1111))
            else:
                raise AssertionError(f"Unhandled signature ({p}, {q})")
            assert not cl.is_zero(witness)
            assert cl.is_zero(cl.mul(witness, witness)), (
                f"Witness failed in Cl_{{{p},{q}}}"
            )
    print("      PASS: Cl_{2,0} (+Q), Cl_{0,4} (-Q), and sharp 5-exception classification verified.")


def verify_null_vector_sum_failure() -> None:
    print("[3/5] Verifying null-vector sum refutation and polar orthogonality criterion...")
    cl11 = CliffordAlgebra([Fraction(1), Fraction(-1)], zero=Fraction(0), one=Fraction(1))
    u = cl11.embed_vec([Fraction(1), Fraction(1)])    # e1 + e2
    w = cl11.embed_vec([Fraction(1), Fraction(-1)])   # e1 - e2
    assert cl11.is_zero(cl11.mul(u, u))
    assert cl11.is_zero(cl11.mul(w, w))
    assert cl11.is_zero(cl11.add(cl11.mul(u, u), cl11.mul(w, w)))
    s = cl11.add(u, w)  # 2 * e1
    s_sq = cl11.mul(s, s)
    assert cl11.eq(s_sq, cl11.scalar_elem(Fraction(4)))
    # Explicit inverse (1/4) * s = (1/2) * e1 proves s is a unit, never nilpotent
    s_inv = cl11.embed_vec([Fraction(1, 2), Fraction(0)])
    assert cl11.eq(cl11.mul(s, s_inv), cl11.one_elem())
    for k in range(1, 8):
        assert not cl11.is_zero(cl11.power(s, k))

    # Contrast in Cl_{2,2}: orthogonal vs non-orthogonal null-vector pairs
    cl22 = CliffordAlgebra([1, 1, -1, -1])
    null_vecs = [
        list(v)
        for v in itertools.product([-1, 0, 1], repeat=4)
        if any(v) and cl22.quad_form(list(v)) == 0
    ]
    assert len(null_vecs) > 0
    for u_c in null_vecs:
        for w_c in null_vecs:
            sum_elem = cl22.add(cl22.embed_vec(u_c), cl22.embed_vec(w_c))
            sq_zero = cl22.is_zero(cl22.mul(sum_elem, sum_elem))
            orth = cl22.polar_form(u_c, w_c) == 0
            assert sq_zero == orth
    print(f"      PASS: Cl_{{1,1}} unit sum and {len(null_vecs)}^2 Cl_{{2,2}} null pairs verified.")


def verify_degenerate_and_field_refutations() -> None:
    print("[4/5] Verifying degenerate inertia, Z[i]/C, and finite-field sums of squares...")
    # 3A: Degenerate positive-semidefinite inertia (1, 0, 1): Q(x1, x2) = x1^2 + 0*x2^2
    cl_deg = CliffordAlgebra([1, 0])
    e2 = cl_deg.embed_vec([0, 1])
    assert not cl_deg.is_zero(e2)
    assert cl_deg.quad_form([0, 1]) == 0
    assert cl_deg.is_zero(cl_deg.mul(e2, e2))

    # 3B: Gaussian integers Z[i] (modeling C): Q(z1, z2) = z1^2 + z2^2 at (1, i)
    cl_gi = CliffordAlgebra([GaussInt(1, 0), GaussInt(1, 0)], zero=GaussInt(0, 0), one=GaussInt(1, 0))
    v_gi = [GaussInt(1, 0), GaussInt(0, 1)]
    assert cl_gi.quad_form(v_gi).is_zero()
    ev_gi = cl_gi.embed_vec(v_gi)
    assert not cl_gi.is_zero(ev_gi)
    assert cl_gi.is_zero(cl_gi.mul(ev_gi, ev_gi))

    # 3C: Finite prime fields F_p for all odd primes p < 100 (Chevalley-Warning 3-squares)
    odd_primes = [
        p for p in range(3, 100, 2) if all(p % d != 0 for d in range(3, int(p**0.5) + 1, 2))
    ]
    for p in odd_primes:
        # Pure sum of 3 squares x^2 + y^2 + z^2 = 0 (mod p) ALWAYS has a nonzero solution
        witness_3 = None
        for x in range(p):
            for y in range(p):
                if (x * x + y * y + 1) % p == 0:
                    witness_3 = [x, y, 1]
                    break
            if witness_3 is not None:
                break
        assert witness_3 is not None, f"Chevalley-Warning 3-squares failed at p={p}"
        cl_fp = CliffordAlgebra([1, 1, 1], mod=p)
        ev_fp = cl_fp.embed_vec(witness_3)
        assert not cl_fp.is_zero(ev_fp)
        assert cl_fp.is_zero(cl_fp.mul(ev_fp, ev_fp))

        # Pure sum of 2 squares x^2 + y^2 = 0 (mod p) has nonzero solution iff p == 1 (mod 4)
        has_2sq = any(
            (x, y) != (0, 0) and (x * x + y * y) % p == 0
            for x in range(p)
            for y in range(p)
        )
        assert has_2sq == (p % 4 == 1), f"2-squares criterion failed at p={p}"
    print(f"      PASS: Degenerate form, Z[i], and {len(odd_primes)} odd prime fields F_p verified.")


def verify_hasse_minkowski_obstructions() -> None:
    print("[5/5] Verifying Hasse-Minkowski obstructions over Q in signatures (1,1) and (2,1)...")
    # Binary indefinite Q(x, y) = x^2 - 2 y^2 (real signature (1, 1))
    for a in range(-60, 61):
        for b in range(-60, 61):
            if (a, b) != (0, 0):
                assert a * a - 2 * b * b != 0

    # Ternary indefinite Q(x, y, z) = x^2 + y^2 - 3 z^2 (real signature (2, 1))
    # Verify 3-adic obstruction: mod 9, a^2 + b^2 - 3 c^2 == 0 forces 3 | a, 3 | b, 3 | c
    for a in range(9):
        for b in range(9):
            for c in range(9):
                if (a * a + b * b - 3 * c * c) % 9 == 0:
                    assert a % 3 == 0 and b % 3 == 0 and c % 3 == 0
    for a in range(-25, 26):
        for b in range(-25, 26):
            for c in range(-25, 26):
                if (a, b, c) != (0, 0, 0):
                    assert a * a + b * b - 3 * c * c != 0
    print("      PASS: Rational anisotropy of x^2 - 2y^2 and x^2 + y^2 - 3z^2 verified.")


def main() -> int:
    print("=" * 74)
    print("Conjecture 00000007624 — Computational Verification Suite")
    print("=" * 74)
    verify_positive_theorems()
    verify_positive_definite_nilpotents_and_classification()
    verify_null_vector_sum_failure()
    verify_degenerate_and_field_refutations()
    verify_hasse_minkowski_obstructions()
    print("=" * 74)
    print("ALL VERIFICATION CHECKS PASSED (EXIT CODE 0) — VERDICT: FALSE IN GENERAL")
    print("=" * 74)
    return 0


if __name__ == "__main__":
    sys.exit(main())
