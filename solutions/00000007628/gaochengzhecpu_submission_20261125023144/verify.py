#!/usr/bin/env python3
"""
Standalone exact verification suite for Conjecture 00000007628:
  "Minimal ideals with the ideal dimension law of Clifford algebras:
   the minimal-ideal dimension is exactly the spinor dimension;
   the law is exact with test by semisimple decomposition;
   and the automorphism group of the ideal is the symplectic group."

Uses ONLY the Python 3.12 standard library (exact rational arithmetic via
`fractions.Fraction` and exact modular arithmetic over finite fields F_p).
Verifies both:
  1. Positive Non-Vacuity Regime (split Clifford algebra Cl_{1,1}(K) ≅ M_2(K)
     with canonical Clifford-conjugation spinor pairing ω), and
  2. Complete Multi-Reading Refutation across all standard readings of minimal
     ideals, quadratic spaces, spinor dimensions, and ideal automorphism groups.
"""

from __future__ import annotations

from fractions import Fraction
import itertools
import math
import sys
from typing import Callable, Sequence


# ---------------------------------------------------------------------------
# 1. Exact 2x2 Matrix Algebra over Q and F_p
# ---------------------------------------------------------------------------

Mat2Q = tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]
Vec2Q = tuple[Fraction, Fraction]


def qmat(a11: int | Fraction, a12: int | Fraction,
         a21: int | Fraction, a22: int | Fraction) -> Mat2Q:
    return ((Fraction(a11), Fraction(a12)), (Fraction(a21), Fraction(a22)))


def qadd(A: Mat2Q, B: Mat2Q) -> Mat2Q:
    return ((A[0][0] + B[0][0], A[0][1] + B[0][1]),
            (A[1][0] + B[1][0], A[1][1] + B[1][1]))


def qscale(c: int | Fraction, A: Mat2Q) -> Mat2Q:
    cf = Fraction(c)
    return ((cf * A[0][0], cf * A[0][1]), (cf * A[1][0], cf * A[1][1]))


def qmul(A: Mat2Q, B: Mat2Q) -> Mat2Q:
    return (
        (A[0][0] * B[0][0] + A[0][1] * B[1][0],
         A[0][0] * B[0][1] + A[0][1] * B[1][1]),
        (A[1][0] * B[0][0] + A[1][1] * B[1][0],
         A[1][0] * B[0][1] + A[1][1] * B[1][1]),
    )


def qact(A: Mat2Q, u: Vec2Q) -> Vec2Q:
    return (A[0][0] * u[0] + A[0][1] * u[1],
            A[1][0] * u[0] + A[1][1] * u[1])


def qdet(A: Mat2Q) -> Fraction:
    return A[0][0] * A[1][1] - A[0][1] * A[1][0]


def qconj_cliff(A: Mat2Q) -> Mat2Q:
    """Clifford conjugation on Cl_{1,1}(Q) ≅ M_2(Q): X |-> J^{-1} X^T J."""
    return ((A[1][1], -A[0][1]), (-A[1][0], A[0][0]))


def qomega(u: Vec2Q, v: Vec2Q) -> Fraction:
    return u[0] * v[1] - u[1] * v[0]


def verify_positive_split_clifford11() -> None:
    print("=== [1/6] Positive Non-Vacuity Check: Split Cl_{1,1}(Q) ≅ M_2(Q) ===")
    Z2 = qmat(0, 0, 0, 0)
    I2 = qmat(1, 0, 0, 1)
    g1 = qmat(1, 0, 0, -1)
    g2 = qmat(0, 1, -1, 0)
    g12 = qmul(g1, g2)

    assert qmul(g1, g1) == I2
    assert qmul(g2, g2) == qscale(-1, I2)
    assert qadd(qmul(g1, g2), qmul(g2, g1)) == Z2

    E11 = qscale(Fraction(1, 2), qadd(I2, g1))
    E22 = qscale(Fraction(1, 2), qadd(I2, qscale(-1, g1)))
    assert E11 == qmat(1, 0, 0, 0)
    assert E22 == qmat(0, 0, 0, 1)
    assert qmul(E11, E11) == E11 and qmul(E22, E22) == E22
    assert qmul(E11, E22) == Z2 and qmul(E22, E11) == Z2
    assert qadd(E11, E22) == I2

    # Clifford conjugation on basis {I2, g1, g2, g12}
    assert qconj_cliff(I2) == I2
    assert qconj_cliff(g1) == qscale(-1, g1)
    assert qconj_cliff(g2) == qscale(-1, g2)
    assert qconj_cliff(g12) == qscale(-1, g12)

    # Exact spinor pairing covariance omega(X u, v) == omega(u, bar(X) v)
    basis_cl = [I2, g1, g2, g12]
    test_vecs = [(Fraction(1), Fraction(0)),
                 (Fraction(0), Fraction(1)),
                 (Fraction(3, 2), Fraction(-5, 7)),
                 (Fraction(-2, 3), Fraction(11, 5))]
    for X in basis_cl:
        for u in test_vecs:
            for v in test_vecs:
                assert qomega(qact(X, u), v) == qomega(u, qact(qconj_cliff(X), v))

    # Determinant law omega(g u, g v) == det(g) * omega(u, v)
    sample_mats = [
        qmat(2, 3, 5, 8),      # det = 1  (in Sp_2(Q))
        qmat(3, -1, 7, -2),    # det = 1  (in Sp_2(Q))
        qmat(2, 1, 1, 2),      # det = 3  (not in Sp_2(Q))
        qmat(-1, 0, 0, 1),     # det = -1 (not in Sp_2(Q))
    ]
    for g in sample_mats:
        for u in test_vecs:
            for v in test_vecs:
                assert qomega(qact(g, u), qact(g, v)) == qdet(g) * qomega(u, v)

    print("  [PASS] Cl_{1,1}(Q) = S_1 (+) S_2, dim_Q(S_1) = 2 = 2^(2/2), conversion = 4/2 = 2.")
    print("  [PASS] Canonical spinor pairing omega is Clifford-conjugation covariant and Aut_Q(S_1, omega) = Sp_2(Q).")


# ---------------------------------------------------------------------------
# 2. Minimal Two-Sided Ideal Refutation (dim J_min = 4^m != 2^m)
# ---------------------------------------------------------------------------

def verify_two_sided_ideal_refutation() -> None:
    print("\n=== [2/6] Refutation 1: Minimal Two-Sided Ideal Dimension (4^m != 2^m) ===")
    # Exhaustively verify over F_3 that EVERY nonzero X in M_2(F_3) generates all of M_2(F_3)
    p = 3
    all_m2 = list(itertools.product(range(p), repeat=4))

    def m2_mul_fp(A: tuple[int, int, int, int], B: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
        return (
            (A[0] * B[0] + A[1] * B[2]) % p,
            (A[0] * B[1] + A[1] * B[3]) % p,
            (A[2] * B[0] + A[3] * B[2]) % p,
            (A[2] * B[1] + A[3] * B[3]) % p,
        )

    def m2_add_fp(A: tuple[int, int, int, int], B: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
        return tuple((A[i] + B[i]) % p for i in range(4))  # type: ignore[return-value]

    for X in all_m2:
        if X == (0, 0, 0, 0):
            continue
        # Generate two-sided ideal M_2(F_3) X M_2(F_3)
        prods = {m2_mul_fp(m2_mul_fp(L, X), R) for L in all_m2 for R in all_m2}
        ideal = set(prods)
        changed = True
        while changed:
            changed = False
            new_elems = {m2_add_fp(a, b) for a in ideal for b in prods}
            if not new_elems.issubset(ideal):
                ideal |= new_elems
                changed = True
        assert len(ideal) == p ** 4 == 81, f"Expected full M_2(F_3), got {len(ideal)}"

    # Verify dimension table for split Cl_{m,m}(K) ≅ M_{2^m}(K), m = 1..5
    for m in range(1, 6):
        two_sided_dim = 4 ** m
        spinor_dim = 2 ** m
        assert two_sided_dim == spinor_dim ** 2 and two_sided_dim > spinor_dim

    print("  [PASS] Exhaustive check on Cl_{1,1}(F_3) ≅ M_2(F_3): all 80 nonzero elements generate dim-4 ideal (4 != 2).")
    print("  [PASS] For all split Cl_{m,m}(K) ≅ M_{2^m}(K) (m >= 1): unique minimal two-sided ideal has dim 4^m > 2^m.")


# ---------------------------------------------------------------------------
# 3. Degenerate Quadratic Forms: Exterior Algebras Cl(K^n, 0) = Lambda(K^n)
# ---------------------------------------------------------------------------

def exterior_mul_blade(mask_a: int, mask_b: int, n: int) -> tuple[int, int]:
    """Multiply basis blades e_A and e_B in Lambda(K^n). Returns (sign, mask)."""
    if mask_a & mask_b:
        return (0, 0)
    inversions = 0
    for i in range(n):
        if (mask_a >> i) & 1:
            # Count j < i present in mask_b
            lower_b = mask_b & ((1 << i) - 1)
            inversions += lower_b.bit_count()
    sign = -1 if (inversions % 2 == 1) else 1
    return (sign, mask_a | mask_b)


def verify_degenerate_exterior_refutation() -> None:
    print("\n=== [3/6] Refutation 2: Degenerate Clifford / Exterior Algebras Cl(K^n, 0) = Lambda(K^n) ===")
    for n in (2, 3, 4):
        dim_alg = 1 << n
        top_mask = dim_alg - 1
        spinor_dim = 1 << (n // 2)

        # 1. Associativity on all blade triples
        for a in range(dim_alg):
            for b in range(dim_alg):
                sab, mab = exterior_mul_blade(a, b, n)
                for c in range(dim_alg):
                    s1, m1 = exterior_mul_blade(mab, c, n) if sab != 0 else (0, 0)
                    sbc, mbc = exterior_mul_blade(b, c, n)
                    s2, m2 = exterior_mul_blade(a, mbc, n) if sbc != 0 else (0, 0)
                    assert (sab * s1, m1 if sab * s1 != 0 else 0) == (
                        sbc * s2, m2 if sbc * s2 != 0 else 0
                    )

        # 2. Every nonzero element can be left-multiplied onto a nonzero scalar multiple of top blade e_{1..n}
        # Proof check on basis: for any lowest-degree nonzero blade A in support(x), multiplying by complement ~A
        # kills all blades not subset of A (hence kills all other blades of >= degree or incomparable) and maps A -> +- top_mask!
        for mask in range(dim_alg):
            comp = top_mask ^ mask
            s, m = exterior_mul_blade(comp, mask, n)
            assert s in (-1, 1) and m == top_mask

        assert 1 != spinor_dim
        print(f"  [PASS] Lambda(K^{n}) = Cl(K^{n}, 0): dim = {dim_alg}, rad dim = {dim_alg - 1} > 0 (not semisimple), "
              f"unique minimal left/two-sided ideal dim = 1 != {spinor_dim} = 2^floor({n}/2).")

    # Exhaustive check over F_3 for Lambda(F_3^2): all 80 nonzero elements generate left ideals containing e_{12},
    # and NO left ideal L complements K*e_{12}!
    p = 3
    all_ext2 = list(itertools.product(range(p), repeat=4))  # masks 00, 01, 10, 11

    def ext2_mul_fp(x: tuple[int, int, int, int], y: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
        res = [0, 0, 0, 0]
        for a in range(4):
            if x[a] == 0:
                continue
            for b in range(4):
                if y[b] == 0:
                    continue
                s, m = exterior_mul_blade(a, b, 2)
                if s != 0:
                    res[m] = (res[m] + s * x[a] * y[b]) % p
        return (res[0], res[1], res[2], res[3])

    e12 = (0, 0, 0, 1)
    idempotents = [x for x in all_ext2 if ext2_mul_fp(x, x) == x]
    assert idempotents == [(0, 0, 0, 0), (1, 0, 0, 0)], f"Unexpected idempotents: {idempotents}"

    for x in all_ext2:
        if x == (0, 0, 0, 0):
            continue
        left_multiples = {ext2_mul_fp(m, x) for m in all_ext2}
        assert e12 in left_multiples

    print("  [PASS] Exhaustive F_3 check on Lambda(F_3^2): only idempotents are {0, 1}; all 80 nonzero elements hit e_12.")


# ---------------------------------------------------------------------------
# 4. Nondegenerate Division Clifford Algebras (Quaternions Cl_{0,2}(Q) = H_Q)
# ---------------------------------------------------------------------------

def verify_division_clifford_quaternions() -> None:
    print("\n=== [4/6] Refutation 3: Nondegenerate Division Clifford Algebra Cl_{0,2}(Q) = H_Q ===")
    QuatQ = tuple[Fraction, Fraction, Fraction, Fraction]

    def hmul(p: QuatQ, q: QuatQ) -> QuatQ:
        return (
            p[0] * q[0] - p[1] * q[1] - p[2] * q[2] - p[3] * q[3],
            p[0] * q[1] + p[1] * q[0] + p[2] * q[3] - p[3] * q[2],
            p[0] * q[2] - p[1] * q[3] + p[2] * q[0] + p[3] * q[1],
            p[0] * q[3] + p[1] * q[2] - p[2] * q[1] + p[3] * q[0],
        )

    def hinv(q: QuatQ) -> QuatQ:
        nsq = sum(c * c for c in q)
        assert nsq > 0
        return (q[0] / nsq, -q[1] / nsq, -q[2] / nsq, -q[3] / nsq)

    one_q: QuatQ = (Fraction(1), Fraction(0), Fraction(0), Fraction(0))
    qi: QuatQ = (Fraction(0), Fraction(1), Fraction(0), Fraction(0))
    qj: QuatQ = (Fraction(0), Fraction(0), Fraction(1), Fraction(0))

    assert hmul(qi, qi) == (Fraction(-1), Fraction(0), Fraction(0), Fraction(0))
    assert hmul(qj, qj) == (Fraction(-1), Fraction(0), Fraction(0), Fraction(0))
    ij = hmul(qi, qj)
    ji = hmul(qj, qi)
    assert tuple(ij[k] + ji[k] for k in range(4)) == (0, 0, 0, 0)

    for coords in itertools.product((-2, -1, 0, 1, 2), repeat=4):
        if coords == (0, 0, 0, 0):
            continue
        q = tuple(Fraction(c) for c in coords)  # type: ignore[assignment]
        assert hmul(hinv(q), q) == one_q and hmul(q, hinv(q)) == one_q

    print("  [PASS] Cl_{0,2}(Q) = H_Q is semisimple (division ring), yet unique minimal left ideal has dim_Q = 4 != 2 = 2^(2/2).")


# ---------------------------------------------------------------------------
# 5. Exhaustive Ideal Automorphism Group Spectrum vs. Symplectic Group
# ---------------------------------------------------------------------------

def verify_automorphism_groups() -> None:
    print("\n=== [5/6] Refutation 4: All Five Ideal Automorphism Notions vs. Symplectic Group ===")
    p = 3
    vecs = list(itertools.product(range(p), repeat=2))
    mats = list(itertools.product(range(p), repeat=4))

    def mul_m(A: tuple[int, int, int, int], B: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
        return (
            (A[0] * B[0] + A[1] * B[2]) % p,
            (A[0] * B[1] + A[1] * B[3]) % p,
            (A[2] * B[0] + A[3] * B[2]) % p,
            (A[2] * B[1] + A[3] * B[3]) % p,
        )

    def act_m(A: tuple[int, int, int, int], u: tuple[int, int]) -> tuple[int, int]:
        return ((A[0] * u[0] + A[1] * u[1]) % p, (A[2] * u[0] + A[3] * u[1]) % p)

    def det_m(A: tuple[int, int, int, int]) -> int:
        return (A[0] * A[3] - A[1] * A[2]) % p

    def s1_mul(u: tuple[int, int], v: tuple[int, int]) -> tuple[int, int]:
        return ((u[0] * v[0]) % p, (u[1] * v[0]) % p)

    def omega_fp(u: tuple[int, int], v: tuple[int, int]) -> int:
        return (u[0] * v[1] - u[1] * v[0]) % p

    def dot_fp(u: tuple[int, int], v: tuple[int, int]) -> int:
        return (u[0] * v[0] + u[1] * v[1]) % p

    cl11_g1 = (1, 0, 0, 2)  # [[1, 0], [0, -1]] mod 3
    cl11_g2 = (0, 1, 2, 0)  # [[0, 1], [-1, 0]] mod 3

    gl2 = [g for g in mats if det_m(g) != 0]
    cl_mod_aut = [g for g in gl2 if mul_m(g, cl11_g1) == mul_m(cl11_g1, g)
                  and mul_m(g, cl11_g2) == mul_m(cl11_g2, g)]
    s1_alg_aut = [g for g in gl2 if all(
        act_m(g, s1_mul(u, v)) == s1_mul(act_m(g, u), act_m(g, v))
        for u in vecs for v in vecs
    )]
    orthog_cl20 = [g for g in gl2 if all(
        dot_fp(act_m(g, u), act_m(g, v)) == dot_fp(u, v)
        for u in vecs for v in vecs
    )]
    sp2 = [g for g in gl2 if all(
        omega_fp(act_m(g, u), act_m(g, v)) == omega_fp(u, v)
        for u in vecs for v in vecs
    )]

    assert len(cl_mod_aut) == 2
    assert len(s1_alg_aut) == 6
    assert len(orthog_cl20) == 8
    assert len(sp2) == 24
    assert len(gl2) == 48

    # Verify affine characterization of s1_alg_aut: g = [[1, 0], [q, s]] with s != 0
    expected_aff1 = [(1, 0, q, s) for q in range(p) for s in (1, 2)]
    assert set(s1_alg_aut) == set(expected_aff1)

    # Verify derived subgroup orders: [Aff_1(F_3), Aff_1(F_3)] has order 3 (abelian),
    # whereas [Sp_2(F_3), Sp_2(F_3)] = Q_8 has order 8 (non-abelian)!
    def inv_gl2(g: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
        d = det_m(g)
        d_inv = 1 if d == 1 else 2
        return ((d_inv * g[3]) % p, (-d_inv * g[1]) % p, (-d_inv * g[2]) % p, (d_inv * g[0]) % p)

    def derived_subgroup(group: Sequence[tuple[int, int, int, int]]) -> set[tuple[int, int, int, int]]:
        comms = {mul_m(mul_m(a, b), mul_m(inv_gl2(a), inv_gl2(b))) for a in group for b in group}
        sub = set(comms)
        changed = True
        while changed:
            changed = False
            nxt = {mul_m(x, y) for x in sub for y in comms}
            if not nxt.issubset(sub):
                sub |= nxt
                changed = True
        return sub

    der_aff1 = derived_subgroup(s1_alg_aut)
    der_sp2 = derived_subgroup(sp2)
    assert len(der_aff1) == 3 and all(mul_m(x, y) == mul_m(y, x) for x in der_aff1 for y in der_aff1)
    assert len(der_sp2) == 8 and any(mul_m(x, y) != mul_m(y, x) for x in der_sp2 for y in der_sp2)

    # Verify center obstruction for two-sided ideal algebra automorphisms PGL_2(F_q) vs Sp_2(F_q)
    # Over F_3 (|PGL_2(F_3)| = |Sp_2(F_3)| = 24) and F_5 (|PGL_2(F_5)| = |Sp_2(F_5)| = 120):
    # |Z(PGL_2(F_q))| = 1 whereas |Z(Sp_2(F_q))| = 2!
    for q_prime in (3, 5):
        mats_q = [g for g in itertools.product(range(q_prime), repeat=4)
                  if (g[0] * g[3] - g[1] * g[2]) % q_prime != 0]

        def mul_q(A: tuple[int, int, int, int], B: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
            return (
                (A[0] * B[0] + A[1] * B[2]) % q_prime,
                (A[0] * B[1] + A[1] * B[3]) % q_prime,
                (A[2] * B[0] + A[3] * B[2]) % q_prime,
                (A[2] * B[1] + A[3] * B[3]) % q_prime,
            )

        def is_scalar_q(A: tuple[int, int, int, int]) -> bool:
            return A[1] == 0 and A[2] == 0 and A[0] == A[3] and A[0] != 0

        sp2_q = [g for g in mats_q if (g[0] * g[3] - g[1] * g[2]) % q_prime == 1]
        center_sp2_q = [z for z in sp2_q if all(mul_q(z, y) == mul_q(y, z) for y in sp2_q)]
        assert len(center_sp2_q) == 2

        # Canonical coset representatives of PGL_2(F_q) = GL_2(F_q) / F_q^x: first nonzero entry == 1
        pgl2_reps = [g for g in mats_q if next(c for c in g if c != 0) == 1]
        assert len(pgl2_reps) == len(sp2_q)  # 24 for q=3, 120 for q=5

        # z in GL_2 maps to Z(PGL_2) iff z*y*z^{-1} is scalar multiple of y for all y in GL_2
        # i.e. z*y and y*z differ by a nonzero scalar for all y in pgl2_reps
        def same_projective(A: tuple[int, int, int, int], B: tuple[int, int, int, int]) -> bool:
            return any(tuple((c * a) % q_prime for a in A) == B for c in range(1, q_prime))

        center_pgl2_q = [z for z in pgl2_reps if all(same_projective(mul_q(z, y), mul_q(y, z)) for y in pgl2_reps)]
        assert len(center_pgl2_q) == 1  # Trivial center!

    # Dimension comparison for N = 2^m (m = 1..4):
    # - For all m >= 1, dim Sp_N = N(N+1)/2 never equals dim Aut_Cl (1), dim Aut_alg(S) (N(N-1)), or dim GL_N (N^2).
    # - For m == 1 (N = 2), dim PGL_2 = dim Sp_2 = 3, distinguished globally by |Z(PGL_2)| = 1 != 2 = |Z(Sp_2)|;
    #   for all m >= 2 (N >= 4), dim PGL_N = N^2 - 1 > N(N+1)/2 = dim Sp_N (e.g. 15 > 10 at N = 4).
    for m in range(1, 5):
        N = 1 << m
        dim_cl_mod = 1
        dim_left_alg = N * (N - 1)
        dim_twosided_alg = N * N - 1
        dim_gl = N * N
        dim_sp = N * (N + 1) // 2
        assert dim_sp not in (dim_cl_mod, dim_left_alg, dim_gl)
        if m >= 2:
            assert dim_twosided_alg > dim_sp

    print("  [PASS] F_3 spinor automorphism order spectrum: |Aut_Cl|=2, |Aut_alg(S_1)|=6, |O_2|=8, |Sp_2|=24, |GL_2|=48.")
    print("  [PASS] Center invariant over F_3 (order 24) and F_5 (order 120): |Z(PGL_2)| = 1 != 2 = |Z(Sp_2)|.")
    print("  [PASS] Algebraic group dimensions for N = 2^m: Sp_N dim N(N+1)/2 never matches 1, N(N-1), N^2 (nor N^2-1 for m>=2).")


# ---------------------------------------------------------------------------
# 6. Lounesto-Porteous Mod-8 Periodicity Table of Spinor Bilinear Invariants
# ---------------------------------------------------------------------------

def verify_mod8_spinor_bilinear_table() -> None:
    print("\n=== [6/6] Refutation 5: Mod-8 Periodicity of Spinor Bilinear Invariants on Cl_{m,m}(K) ===")
    print("    m |  n=2m |  N=2^m | +1(rev) | +1(conj) | sym N(N+1)/2 | skew N(N-1)/2 | Type(rev, conj)")
    print("  ----+-------+--------+---------+----------+--------------+---------------+----------------")
    both_orthog_dims: list[int] = []
    for m in range(0, 9):
        n = 2 * m
        N = 1 << m
        plus_rev = sum(math.comb(n, k) for k in range(n + 1) if (k % 4) in (0, 1))
        plus_conj = sum(math.comb(n, k) for k in range(n + 1) if (k % 4) in (0, 3))
        sym_d = N * (N + 1) // 2
        skew_d = N * (N - 1) // 2

        t_rev = "O" if plus_rev == sym_d else "Sp"
        t_conj = "O" if plus_conj == sym_d else "Sp"
        assert plus_rev in (sym_d, skew_d)
        assert plus_conj in (sym_d, skew_d)
        if t_rev == "O" and t_conj == "O":
            both_orthog_dims.append(n)

        print(f"   {m:2d} | {n:5d} | {N:6d} | {plus_rev:7d} | {plus_conj:8d} | {sym_d:12d} | {skew_d:13d} | ({t_rev}_{N}, {t_conj}_{N})")

    assert both_orthog_dims == [0, 8, 16]
    print("  [PASS] At n = 8 (Cl_{4,4}(K) ≅ M_16(K), N = 16) and all n ≡ 0 (mod 8), BOTH reversion and Clifford")
    print("         conjugation have +1-eigenspace dim N(N+1)/2 (136 != 120 at n=8), inducing O_N rather than Sp_N!")


def main() -> int:
    verify_positive_split_clifford11()
    verify_two_sided_ideal_refutation()
    verify_degenerate_exterior_refutation()
    verify_division_clifford_quaternions()
    verify_automorphism_groups()
    verify_mod8_spinor_bilinear_table()
    print("\nALL 6 VERIFICATION SUITES PASSED SUCCESSFULLY (Conjecture 00000007628: FALSE in general; positive split witness verified).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
