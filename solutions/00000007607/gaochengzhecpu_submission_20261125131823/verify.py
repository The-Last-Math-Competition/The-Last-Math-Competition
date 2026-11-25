#!/usr/bin/env python3
"""
Exact & Numerical Verification Suite for Conjecture 00000007607
("Rotor Logarithm-Sum Angle Additivity")

Implements arbitrary-dimension Euclidean Clifford algebras Cl_{n,0}(Q) and Cl_{n,0}(R)
from first principles (bitmask blade arithmetic with Koszul signs, zero external
dependencies) and independently verifies:
  1. Positive abelian theorem in n = 2 (Spin(2) / coplanar rotors): Lie bracket [B1, B2] = 0,
     exact rotor angle additivity, and spectral angle additivity of B1 + B2.
  2. Complete refutation in n = 3 (Spin(3) subset Cl_{3,0}):
     - 90-degree orthogonal rotors over Q[sqrt(2)] and R: three-way separation
       Theta(R1 R2) = 2*pi/3 != 2*||B1 + B2|| = pi/sqrt(2) != theta1 + theta2 = pi,
       exp(B1)*exp(B2) != exp(B1 + B2), cyclic 3-cycle e1 -> e2 -> e3 -> e1,
       and [e12, e23] = 2*e13 != 0.
     - 180-degree orthogonal rotors over Z: (-e12)(-e23) = e13 != +-1 (Theta = pi != 2*pi).
     - Exact rational Pythagorean spectral (3^2 + 4^2 = 25 != 49) & Cayley unit-rotor checks.
     - Master sum-of-squares & Lagrange identities across rational grids and 200 random pairs.
  3. Four-dimensional disjoint-plane phenomenon in Cl_{4,0}(Q) and so(4):
     [e12, e34] = 0 and exp(B1)*exp(B2) = exp(B1 + B2) hold, yet B1 ^ B2 != 0 makes
     B1 + B2 non-simple (double rotation with vector spectrum {+-i*theta1, +-i*theta2}).
  4. Universal dimension sweep across n = 3..8 in SO(n) / so(n).
"""

from __future__ import annotations

import math
import random
import sys
from fractions import Fraction
from typing import Dict, Tuple


# =============================================================================
# 1. Exact Arbitrary-Dimension Euclidean Clifford Algebra Cl_{n,0}
# =============================================================================

def blade_mul_sign(a: int, b: int) -> Tuple[int, int]:
    """Multiply basis blades indexed by bitmasks a, b in Cl_{n,0} (e_i^2 = +1).
    Returns (sign, a ^ b) where sign in {+1, -1}.
    """
    swaps = 0
    x = a >> 1
    y = b
    while x:
        swaps += (x & 0)  # no-op placeholder for clarity
        # Each bit i in a moves past all strictly lower bits j < i present in b:
        x = 0
    # Direct bit-counting of inversions {(i, j) : i in a, j in b, i > j}:
    inv = 0
    temp_a = a
    bit_pos = 0
    while temp_a:
        if temp_a & 1:
            lower_mask = (1 << bit_pos) - 1
            inv += (b & lower_mask).bit_count()
        temp_a >>= 1
        bit_pos += 1
    return (-1 if (inv & 1) else 1), (a ^ b)


def blade_rev_sign(mask: int) -> int:
    """Reversion sign (-1)^(k(k-1)/2) for a blade of grade k."""
    k = mask.bit_count()
    return -1 if ((k * (k - 1)) // 2) & 1 else 1


class CliffordElem:
    """Sparse multivector in Cl_{n,0} over exact Fraction or float."""

    def __init__(self, n: int, coeffs: Dict[int, Fraction | float] | None = None, zero=Fraction(0)):
        self.n = n
        self.zero = zero
        self.coeffs: Dict[int, Fraction | float] = {}
        if coeffs:
            for k, v in coeffs.items():
                if v != zero:
                    self.coeffs[k] = v

    @classmethod
    def scalar(cls, n: int, val: Fraction | float, zero=Fraction(0)) -> "CliffordElem":
        return cls(n, {0: val}, zero=zero)

    @classmethod
    def basis(cls, n: int, indices_1based: Tuple[int, ...], coeff=Fraction(1), zero=Fraction(0)) -> "CliffordElem":
        res = cls.scalar(n, coeff, zero=zero)
        for idx in indices_1based:
            assert 1 <= idx <= n
            res = res * cls(n, {1 << (idx - 1): (1.0 if isinstance(zero, float) else Fraction(1))}, zero=zero)
        return res

    def __add__(self, other: "CliffordElem") -> "CliffordElem":
        out = dict(self.coeffs)
        for k, v in other.coeffs.items():
            out[k] = out.get(k, self.zero) + v
        return CliffordElem(self.n, out, zero=self.zero)

    def __sub__(self, other: "CliffordElem") -> "CliffordElem":
        out = dict(self.coeffs)
        for k, v in other.coeffs.items():
            out[k] = out.get(k, self.zero) - v
        return CliffordElem(self.n, out, zero=self.zero)

    def __neg__(self) -> "CliffordElem":
        return CliffordElem(self.n, {k: -v for k, v in self.coeffs.items()}, zero=self.zero)

    def smul(self, c: Fraction | float) -> "CliffordElem":
        return CliffordElem(self.n, {k: c * v for k, v in self.coeffs.items()}, zero=self.zero)

    def __mul__(self, other: "CliffordElem") -> "CliffordElem":
        out: Dict[int, Fraction | float] = {}
        for a, va in self.coeffs.items():
            for b, vb in other.coeffs.items():
                sgn, mask = blade_mul_sign(a, b)
                term = va * vb if sgn == 1 else -(va * vb)
                out[mask] = out.get(mask, self.zero) + term
        return CliffordElem(self.n, out, zero=self.zero)

    def rev(self) -> "CliffordElem":
        return CliffordElem(
            self.n,
            {k: (v if blade_rev_sign(k) == 1 else -v) for k, v in self.coeffs.items()},
            zero=self.zero,
        )

    def grade(self, r: int) -> "CliffordElem":
        return CliffordElem(
            self.n,
            {k: v for k, v in self.coeffs.items() if k.bit_count() == r},
            zero=self.zero,
        )

    def scalar_part(self) -> Fraction | float:
        return self.coeffs.get(0, self.zero)

    def bracket(self, other: "CliffordElem") -> "CliffordElem":
        return self * other - other * self

    def act(self, v: "CliffordElem") -> "CliffordElem":
        return (self * v) * self.rev()

    def norm_sq_euc(self) -> Fraction | float:
        return sum((v * v for v in self.coeffs.values()), self.zero)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CliffordElem):
            return False
        return self.n == other.n and self.coeffs == other.coeffs


def exp_float_multivector(b: CliffordElem, terms: int = 35) -> CliffordElem:
    """Truncated power series exp(b) in Cl_{n,0}(R) to machine precision."""
    acc = CliffordElem.scalar(b.n, 1.0, zero=0.0)
    power = CliffordElem.scalar(b.n, 1.0, zero=0.0)
    fact = 1.0
    for k in range(1, terms + 1):
        power = power * b
        fact *= k
        acc = acc + power.smul(1.0 / fact)
    return acc


def max_coeff_diff(a: CliffordElem, b: CliffordElem) -> float:
    keys = set(a.coeffs.keys()) | set(b.coeffs.keys())
    if not keys:
        return 0.0
    return max(abs(float(a.coeffs.get(k, 0.0)) - float(b.coeffs.get(k, 0.0))) for k in keys)


# =============================================================================
# 2. Verification Suites
# =============================================================================

def verify_clifford_foundations() -> None:
    print("[1/6] Verifying Clifford algebra axioms & bivector grade decomposition (n = 2..5)...")
    for n in (2, 3, 4, 5):
        vecs = [CliffordElem.basis(n, (i,)) for i in range(1, n + 1)]
        one = CliffordElem.scalar(n, Fraction(1))
        zero = CliffordElem(n)
        for i in range(n):
            assert vecs[i] * vecs[i] == one, f"e_{i+1}^2 != 1 in Cl_{n}"
            for j in range(i + 1, n):
                assert vecs[i] * vecs[j] == -(vecs[j] * vecs[i]), "anticommutativity failed"

        # Check associativity & reversion on mixed multivectors
        x = vecs[0] + CliffordElem.basis(n, (1, 2), Fraction(3, 2))
        y = one - vecs[1] + CliffordElem.basis(n, (1, min(n, 3)), Fraction(-2, 5))
        z = vecs[-1] + CliffordElem.basis(n, (max(1, n - 1), n), Fraction(7, 3))
        assert (x * y) * z == x * (y * z), f"associativity failed in Cl_{n}"
        assert (x * y).rev() == y.rev() * x.rev(), f"reversion failed in Cl_{n}"

        # Check canonical bivector product decomposition:
        # B1 * B2 = <B1 B2>_0 + (1/2)[B1, B2] + <B1 B2>_4
        b1 = CliffordElem.basis(n, (1, 2), Fraction(5, 3))
        if n >= 3:
            b1 = b1 + CliffordElem.basis(n, (2, 3), Fraction(-7, 4))
        b2 = CliffordElem.basis(n, (1, 2), Fraction(-2, 5))
        if n >= 4:
            b2 = b2 + CliffordElem.basis(n, (3, 4), Fraction(11, 6))
        prod = b1 * b2
        rhs = prod.grade(0) + b1.bracket(b2).smul(Fraction(1, 2)) + prod.grade(4)
        assert prod == rhs, f"bivector grade decomposition failed in Cl_{n}"
    print("      PASS: Associativity, reversion, and B1*B2 = <B1*B2>_0 + 1/2[B1,B2] + B1^B2 verified.")


def verify_planar_spin2_positive() -> None:
    print("[2/6] Verifying POSITIVE theorem in dimension n = 2 (Spin(2) subset Cl_{2,0})...")
    e12_q = CliffordElem.basis(2, (1, 2))
    one_q = CliffordElem.scalar(2, Fraction(1))

    # Exact rational Pythagorean rotors R1 = 4/5 - 3/5 e12, R2 = 12/13 - 5/13 e12
    r1 = one_q.smul(Fraction(4, 5)) - e12_q.smul(Fraction(3, 5))
    r2 = one_q.smul(Fraction(12, 13)) - e12_q.smul(Fraction(5, 13))
    expected_prod = one_q.smul(Fraction(33, 65)) - e12_q.smul(Fraction(56, 65))
    assert r1 * r1.rev() == one_q
    assert r2 * r2.rev() == one_q
    assert r1 * r2 == expected_prod
    assert r1.bracket(r2) == CliffordElem(2)

    # Exact Lie bracket & spectral angle additivity for arbitrary rational generators
    for a1_num, a2_num in ((3, 4), (7, -2), (5, 11)):
        a1, a2 = Fraction(a1_num, 2), Fraction(a2_num, 2)
        b1 = e12_q.smul(-a1)
        b2 = e12_q.smul(-a2)
        assert b1.bracket(b2) == CliffordElem(2), "[B1, B2] != 0 in Cl_2"
        assert (b1 + b2) * (b1 + b2) == one_q.smul(-((a1 + a2) ** 2))

    # Numerical exponential law exp(B1)*exp(B2) = exp(B1 + B2) in Cl_{2,0}(R)
    e12_f = CliffordElem.basis(2, (1, 2), 1.0, zero=0.0)
    for theta1, theta2 in ((0.7, 1.2), (-0.4, 2.1), (math.pi / 2, math.pi / 3)):
        b1_f = e12_f.smul(-theta1 / 2.0)
        b2_f = e12_f.smul(-theta2 / 2.0)
        lhs = exp_float_multivector(b1_f) * exp_float_multivector(b2_f)
        rhs = exp_float_multivector(b1_f + b2_f)
        assert max_coeff_diff(lhs, rhs) < 1e-14
    print("      PASS: n = 2 Lie bracket [B1,B2] = 0, exp(B1)exp(B2) = exp(B1+B2), and angle additivity hold.")


def verify_spin3_counterexamples_and_master_laws() -> None:
    print("[3/6] Verifying Spin(3) counterexamples & master sum-of-squares characterizations...")
    one_q = CliffordElem.scalar(3, Fraction(1))
    e12_q = CliffordElem.basis(3, (1, 2))
    e23_q = CliffordElem.basis(3, (2, 3))
    e13_q = CliffordElem.basis(3, (1, 3))

    # (a) Lie bracket non-vanishing: [e12, e23] = 2 e13 != 0
    comm = e12_q.bracket(e23_q)
    assert comm == e13_q.smul(Fraction(2))
    assert comm != CliffordElem(3)

    # (b) 180-degree orthogonal rotors: R1 = -e12, R2 = -e23 => R1*R2 = e13 != +-1
    r180_1 = -e12_q
    r180_2 = -e23_q
    assert r180_1 * r180_2 == e13_q
    assert r180_1 * r180_2 != one_q and r180_1 * r180_2 != -one_q

    # (c) 90-degree orthogonal rotors in Cl_{3,0}(R)
    e1_f = CliffordElem.basis(3, (1,), 1.0, zero=0.0)
    e2_f = CliffordElem.basis(3, (2,), 1.0, zero=0.0)
    e3_f = CliffordElem.basis(3, (3,), 1.0, zero=0.0)
    e12_f = CliffordElem.basis(3, (1, 2), 1.0, zero=0.0)
    e23_f = CliffordElem.basis(3, (2, 3), 1.0, zero=0.0)
    one_f = CliffordElem.scalar(3, 1.0, zero=0.0)

    b1_90 = e12_f.smul(-math.pi / 4.0)
    b2_90 = e23_f.smul(-math.pi / 4.0)
    r90_1 = exp_float_multivector(b1_90)
    r90_2 = exp_float_multivector(b2_90)
    comp_90 = r90_1 * r90_2
    exp_sum_90 = exp_float_multivector(b1_90 + b2_90)

    # Check cyclic permutation e1 -> e2 -> e3 -> e1 and (R1 R2)^3 = -1
    assert max_coeff_diff(comp_90.act(e1_f), e2_f) < 1e-14
    assert max_coeff_diff(comp_90.act(e2_f), e3_f) < 1e-14
    assert max_coeff_diff(comp_90.act(e3_f), e1_f) < 1e-14
    assert max_coeff_diff((comp_90 * comp_90) * comp_90, -one_f) < 1e-14
    assert abs(max_coeff_diff(comp_90 * comp_90, -one_f) - 0.5) < 1e-14

    theta_true = 2.0 * math.acos(float(comp_90.scalar_part()))
    theta_spec_sum = 2.0 * math.sqrt(float((b1_90 + b2_90).norm_sq_euc()))
    theta_naive = (math.pi / 2.0) + (math.pi / 2.0)
    assert abs(theta_true - 2.0 * math.pi / 3.0) < 1e-14
    assert abs(theta_spec_sum - math.pi / math.sqrt(2.0)) < 1e-14
    assert abs(theta_true - theta_spec_sum) > 0.12
    assert abs(theta_spec_sum - theta_naive) > 0.90
    assert abs(theta_true - theta_naive) > 1.04
    assert max_coeff_diff(comp_90, exp_sum_90) > 0.45

    # (d) Exact rational Pythagorean spectral & Cayley checks
    b_pyth1 = e12_q.smul(Fraction(-3, 2))
    b_pyth2 = e23_q.smul(Fraction(-4, 2))
    assert (b_pyth1 + b_pyth2).norm_sq_euc() == Fraction(25, 4)
    assert (b_pyth1 + b_pyth2).norm_sq_euc() != Fraction(49, 4)

    rc1 = one_q.smul(Fraction(4, 5)) - e12_q.smul(Fraction(3, 5))
    rc2 = one_q.smul(Fraction(12, 13)) - e23_q.smul(Fraction(5, 13))
    assert (rc1 * rc2).scalar_part() == Fraction(48, 65)
    assert (rc1 * rc2).scalar_part() != Fraction(33, 65)

    # (e) Rational grid + 200 random unit-bivector tests of Master Identities
    pyth_bivecs = [
        e12_q,
        e23_q,
        e13_q,
        e12_q.smul(Fraction(3, 5)) + e23_q.smul(Fraction(4, 5)),
        e23_q.smul(Fraction(12, 13)) - e13_q.smul(Fraction(5, 13)),
        e12_q.smul(Fraction(2, 3)) + e23_q.smul(Fraction(2, 3)) + e13_q.smul(Fraction(1, 3)),
    ]
    cayley_ts = [Fraction(1, 2), Fraction(1, 3), Fraction(1, 5), Fraction(2, 3)]
    for u1 in pyth_bivecs:
        assert u1.norm_sq_euc() == Fraction(1)
        for u2 in pyth_bivecs:
            diff_norm_sq = (u1 - u2).norm_sq_euc()
            # Lagrange identity check
            inner = -(u1 * u2).scalar_part()
            assert u1.bracket(u2).norm_sq_euc() == Fraction(4) * (Fraction(1) - inner * inner)
            for t1 in cayley_ts:
                c1 = (1 - t1 * t1) / (1 + t1 * t1)
                s1 = (2 * t1) / (1 + t1 * t1)
                for t2 in cayley_ts:
                    c2 = (1 - t2 * t2) / (1 + t2 * t2)
                    s2 = (2 * t2) / (1 + t2 * t2)
                    rot1 = one_q.smul(c1) - u1.smul(s1)
                    rot2 = one_q.smul(c2) - u2.smul(s2)
                    lhs_master = Fraction(2) * ((rot1 * rot2).scalar_part() - (c1 * c2 - s1 * s2))
                    rhs_master = s1 * s2 * diff_norm_sq
                    assert lhs_master == rhs_master
                    if u1 != u2:
                        assert (rot1 * rot2).scalar_part() > (c1 * c2 - s1 * s2)
                        assert ((t1 + t2) ** 2 - (u1.smul(-t1) + u2.smul(-t2)).norm_sq_euc()) == t1 * t2 * diff_norm_sq

    rng = random.Random(7607)
    for _ in range(200):
        raw1 = [rng.gauss(0.0, 1.0) for _ in range(3)]
        n1 = math.sqrt(sum(v * v for v in raw1))
        raw2 = [rng.gauss(0.0, 1.0) for _ in range(3)]
        n2 = math.sqrt(sum(v * v for v in raw2))
        u1_f = e23_f.smul(raw1[0] / n1) + CliffordElem.basis(3, (1, 3), -raw1[1] / n1, zero=0.0) + e12_f.smul(raw1[2] / n1)
        u2_f = e23_f.smul(raw2[0] / n2) + CliffordElem.basis(3, (1, 3), -raw2[1] / n2, zero=0.0) + e12_f.smul(raw2[2] / n2)
        th1 = rng.uniform(0.15, math.pi - 0.15)
        th2 = rng.uniform(0.15, math.pi - 0.15)
        b1_r = u1_f.smul(-th1 / 2.0)
        b2_r = u2_f.smul(-th2 / 2.0)
        prod_r = exp_float_multivector(b1_r) * exp_float_multivector(b2_r)
        th_comp = 2.0 * math.acos(max(-1.0, min(1.0, float(prod_r.scalar_part()))))
        assert th_comp < th1 + th2 - 1e-9
    print(
        f"      PASS: 90-deg angles (Theta={math.degrees(theta_true):.4f} deg, "
        f"2||B1+B2||={math.degrees(theta_spec_sum):.4f} deg, "
        f"theta1+theta2={math.degrees(theta_naive):.4f} deg) all distinct; "
        "exact rational & 200 random Spin(3) checks passed."
    )


def verify_spin4_disjoint_commuting_obstruction() -> None:
    print("[4/6] Verifying Spin(4) / Cl_{4,0} commuting disjoint-plane non-simplicity obstruction...")
    one_q = CliffordElem.scalar(4, Fraction(1))
    e12_q = CliffordElem.basis(4, (1, 2))
    e34_q = CliffordElem.basis(4, (3, 4))
    e1234_q = CliffordElem.basis(4, (1, 2, 3, 4))

    # [e12, e34] = 0
    assert e12_q.bracket(e34_q) == CliffordElem(4)

    # B1 = -(3/2)e12, B2 = -2 e34 (angles theta1 = 3, theta2 = 4)
    a1, a2 = Fraction(3, 2), Fraction(4, 2)
    b1 = e12_q.smul(-a1)
    b2 = e34_q.smul(-a2)
    bsum = b1 + b2
    assert b1.bracket(b2) == CliffordElem(4)

    # (B1 + B2)^2 = -25/4 + 6 e1234 != -(7/2)^2
    bsum_sq = bsum * bsum
    assert bsum_sq == one_q.smul(Fraction(-25, 4)) + e1234_q.smul(Fraction(6))
    assert bsum_sq.grade(4) != CliffordElem(4)
    assert bsum_sq != one_q.smul(-((a1 + a2) ** 2))

    # Chiral minimal polynomial ((B1+B2)^2 + (7/2)^2)((B1+B2)^2 + (1/2)^2) = 0
    fac_plus = bsum_sq + one_q.smul((a1 + a2) ** 2)
    fac_minus = bsum_sq + one_q.smul((a1 - a2) ** 2)
    assert fac_plus != CliffordElem(4)
    assert fac_minus != CliffordElem(4)
    assert fac_plus * fac_minus == CliffordElem(4)

    # Numerical check: exp(B1)exp(B2) == exp(B1 + B2) DOES hold, yet action is double rotation
    e12_f = CliffordElem.basis(4, (1, 2), 1.0, zero=0.0)
    e34_f = CliffordElem.basis(4, (3, 4), 1.0, zero=0.0)
    b1_f = e12_f.smul(-0.6)
    b2_f = e34_f.smul(-0.9)
    assert max_coeff_diff(
        exp_float_multivector(b1_f) * exp_float_multivector(b2_f),
        exp_float_multivector(b1_f + b2_f),
    ) < 1e-14
    print("      PASS: [e12, e34] = 0 gives exp(B1)exp(B2) = exp(B1+B2), yet B1^B2 != 0 breaks single-angle additivity.")


def verify_universal_dimension_sweep() -> None:
    print("[5/6] Verifying universal orthogonal & Lie refutations across dimensions n = 3..8...")
    for n in range(3, 9):
        # Construct n x n matrices Q12, Q23 in SO(n) and A12, A23 in so(n)
        q12 = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
        q12[0][0], q12[0][1], q12[1][0], q12[1][1] = 0, -1, 1, 0

        q23 = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
        q23[1][1], q23[1][2], q23[2][1], q23[2][2] = 0, -1, 1, 0

        comp = [
            [sum(q12[i][k] * q23[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)
        ]
        tr_comp = sum(comp[i][i] for i in range(n))
        tr_additive_pi = (n - 2) + 2 * (-1)  # trace of single-plane rotation by pi/2 + pi/2 = pi
        assert tr_comp == n - 3
        assert tr_comp != tr_additive_pi

        # Check commutator [A12, A23] != 0
        a12 = [[0] * n for _ in range(n)]
        a12[0][1], a12[1][0] = -1, 1
        a23 = [[0] * n for _ in range(n)]
        a23[1][2], a23[2][1] = -1, 1
        comm = [
            [
                sum(a12[i][k] * a23[k][j] - a23[i][k] * a12[k][j] for k in range(n))
                for j in range(n)
            ]
            for i in range(n)
        ]
        assert any(comm[i][j] != 0 for i in range(n) for j in range(n))
    print("      PASS: Every dimension n = 3..8 gives tr(Q12 Q23) = n - 3 != n - 4 and [A12, A23] != 0.")


def verify_bch_closed_form_spin3() -> None:
    print("[6/6] Verifying exact Baker-Campbell-Hausdorff rotor logarithm formula in Spin(3)...")
    e12_f = CliffordElem.basis(3, (1, 2), 1.0, zero=0.0)
    e23_f = CliffordElem.basis(3, (2, 3), 1.0, zero=0.0)
    b1 = e12_f.smul(-math.pi / 4.0)
    b2 = e23_f.smul(-math.pi / 4.0)
    r12 = exp_float_multivector(b1) * exp_float_multivector(b2)

    # Exact principal logarithm log(R1 R2) = -(Theta / (2 sin(Theta/2))) * (-<R1 R2>_2)
    # Wait: R = cos(Theta/2) - sin(Theta/2) u => <R>_2 = -sin(Theta/2) u => log(R) = (Theta / (2 sin(Theta/2))) <R>_2
    cos_half = float(r12.scalar_part())
    sin_half = math.sqrt(1.0 - cos_half * cos_half)
    theta = 2.0 * math.acos(cos_half)
    b_true_log = r12.grade(2).smul(theta / (2.0 * sin_half))

    assert max_coeff_diff(exp_float_multivector(b_true_log), r12) < 1e-14
    # First-order BCH approximation B1 + B2 + 1/2 [B1, B2] already captures the e13 axis direction!
    bch_first = b1 + b2 + b1.bracket(b2).smul(0.5)
    assert abs(float(b_true_log.coeffs[0b101])) > 0.6  # nonzero e13 component!
    assert float((b1 + b2).coeffs.get(0b101, 0.0)) == 0.0
    assert float(bch_first.coeffs[0b101]) != 0.0
    print("      PASS: Exact log(R1 R2) has nonzero [B1, B2] (e13) component absent from B1 + B2.")


def main() -> int:
    print("==========================================================================")
    print(" Conjecture 00000007607 Verification Suite (Clifford / Spin / Lie Theory)")
    print("==========================================================================")
    verify_clifford_foundations()
    verify_planar_spin2_positive()
    verify_spin3_counterexamples_and_master_laws()
    verify_spin4_disjoint_commuting_obstruction()
    verify_universal_dimension_sweep()
    verify_bch_closed_form_spin3()
    print("==========================================================================")
    print(" ALL CHECKS PASSED: Conjecture 00000007607 DISPROVED for n >= 3 (TRUE n=2)")
    print("==========================================================================")
    return 0


if __name__ == "__main__":
    sys.exit(main())
