#!/usr/bin/env python3
"""
Standalone Exact Rational Verification Suite for Conjecture 00000007618
=======================================================================

Problem Statement (SOURCE.md):
  Definition: The intersection-correction law of projective formulas.
  Conjecture:
    (C1) The sign-correction term spectrum is complete;
    (C2) the combination of the correction is the dimension sum of subspaces; and
    (C3) the combination of the dimension sum is the mod-two reduction.
  (dimension-summed intersection sign correction)

Verdict: FALSE (Refuted across all standard projective intersection conventions,
with an exact positive characterization for the forward three-star Poincare/Hodge
meet formula in even ambient vector dimensions n = 2m, notably P^3 at n = 4).

Uses ONLY the Python 3 standard library (`fractions.Fraction`, `itertools`).
"""

import itertools
import sys
from fractions import Fraction


# ---------------------------------------------------------------------------
# 1. Exact Combinatorial & Multivector Algebra over Q
# ---------------------------------------------------------------------------

def perm_sign(seq):
    """Exact parity sign (+1 or -1) of a sequence of distinct comparable items."""
    inv = 0
    m = len(seq)
    for i in range(m):
        for j in range(i + 1, m):
            if seq[i] > seq[j]:
                inv += 1
    return -1 if (inv % 2 == 1) else 1


def wedge_basis(I, J):
    """Exterior wedge product e_I ^ e_J of sorted index tuples I, J."""
    sI = set(I)
    for x in J:
        if x in sI:
            return 0, ()
    comb = list(I) + list(J)
    return perm_sign(comb), tuple(sorted(comb))


def clifford_mul_basis(q, I, J):
    """Orthogonal Clifford geometric product e_I *_q e_J over Q."""
    coeff = Fraction(1)
    cur = list(I)
    for x in J:
        swaps = sum(1 for y in cur if y > x)
        if swaps % 2 == 1:
            coeff = -coeff
        if x in cur:
            cur.remove(x)
            coeff *= q[x]
        else:
            cur.append(x)
            cur.sort()
    return coeff, tuple(cur)


def rev_sign(k):
    """Clifford reversion sign (-1)^{k(k-1)/2} on grade k."""
    return -1 if ((k * (k - 1) // 2) % 2 == 1) else 1


def mv_clean(mv):
    return {k: v for k, v in mv.items() if v != 0}


def mv_scale(c, mv):
    if c == 0:
        return {}
    return {k: Fraction(c) * v for k, v in mv.items() if v != 0}


def mv_wedge(A, B):
    out = {}
    for I, cA in A.items():
        for J, cB in B.items():
            sgn, K = wedge_basis(I, J)
            if sgn != 0:
                out[K] = out.get(K, Fraction(0)) + cA * cB * sgn
    return mv_clean(out)


def mv_clifford_mul(q, A, B):
    out = {}
    for I, cA in A.items():
        for J, cB in B.items():
            c_ij, K = clifford_mul_basis(q, I, J)
            if c_ij != 0:
                out[K] = out.get(K, Fraction(0)) + cA * cB * c_ij
    return mv_clean(out)


def mv_rev(A):
    return {I: c * rev_sign(len(I)) for I, c in A.items() if c != 0}


def hodge_star_right_basis(n, q, I):
    """
    Classical exterior right Hodge star e_I ^ (*_q e_I) = <e_I, e_I>_q * omega_n.
    """
    metric_factor = Fraction(1)
    for idx in I:
        metric_factor *= q[idx]
    sI = set(I)
    Jc = tuple(x for x in range(n) if x not in sI)
    sgn, full = wedge_basis(I, Jc)
    assert full == tuple(range(n))
    return metric_factor * sgn, Jc


def hodge_star_left_basis(n, q, I):
    """
    Classical exterior left Hodge star (*_{q,L} e_I) ^ e_I = <e_I, e_I>_q * omega_n.
    """
    metric_factor = Fraction(1)
    for idx in I:
        metric_factor *= q[idx]
    sI = set(I)
    Jc = tuple(x for x in range(n) if x not in sI)
    sgn, full = wedge_basis(Jc, I)
    assert full == tuple(range(n))
    return metric_factor * sgn, Jc


def mv_pstar_right(n, A):
    q1 = (Fraction(1),) * n
    out = {}
    for I, c in A.items():
        s, J = hodge_star_right_basis(n, q1, I)
        out[J] = out.get(J, Fraction(0)) + c * s
    return mv_clean(out)


def mv_pstar_right_inv(n, Y):
    q1 = (Fraction(1),) * n
    out = {}
    for K, c in Y.items():
        m = len(K)
        k = n - m
        s, I = hodge_star_right_basis(n, q1, K)
        sgn_inv = (-1) ** (k * (n - k))
        out[I] = out.get(I, Fraction(0)) + c * s * sgn_inv
    return mv_clean(out)


def mv_vee(n, A, B):
    """Canonical Grassmann-Cayley regressive product A v B = *^{-1}((*A) ^ (*B))."""
    return mv_pstar_right_inv(n, mv_wedge(mv_pstar_right(n, A), mv_pstar_right(n, B)))


def mv_vee_forward3star(n, A, B):
    """Uncorrected forward three-star operator *((*A) ^ (*B))."""
    return mv_pstar_right(n, mv_wedge(mv_pstar_right(n, A), mv_pstar_right(n, B)))


def bbr_shuffle_splits_basis(n, I, J):
    """
    Peano / Doubilet-Rota-Stein / Barnabei-Brini-Rota shuffle formulas for A v B
    on basis blades e_I (grade r), e_J (grade s) with r + s >= n (k = r + s - n):
      - BBR1 (first n - s vectors bracketed with B, last k vectors retained);
      - BBR2 (first k vectors retained, last n - s vectors bracketed with B).
    """
    r, s = len(I), len(J)
    if r + s < n:
        return {}, {}
    k = r + s - n
    out1, out2 = {}, {}

    for drop in itertools.combinations(range(r), n - s):
        sdrop = set(drop)
        keep = [idx for idx in range(r) if idx not in sdrop]
        sgn_sh = perm_sign(list(drop) + keep)
        I_drop = tuple(I[idx] for idx in drop)
        I_keep = tuple(I[idx] for idx in keep)
        sgn_br, full = wedge_basis(I_drop, J)
        if sgn_br != 0:
            assert full == tuple(range(n))
            out1[I_keep] = out1.get(I_keep, Fraction(0)) + Fraction(sgn_sh * sgn_br)

    for keep in itertools.combinations(range(r), k):
        skeep = set(keep)
        drop = [idx for idx in range(r) if idx not in skeep]
        sgn_sh = perm_sign(list(keep) + drop)
        I_keep = tuple(I[idx] for idx in keep)
        I_drop = tuple(I[idx] for idx in drop)
        sgn_br, full = wedge_basis(I_drop, J)
        if sgn_br != 0:
            assert full == tuple(range(n))
            out2[I_keep] = out2.get(I_keep, Fraction(0)) + Fraction(sgn_sh * sgn_br)

    return mv_clean(out1), mv_clean(out2)


def cartan_left_basis(I, J):
    """Cartan left interior contraction e_I _|C e_J characterized by <g, I _|C J> = <I ^ g, J>."""
    sI = set(I)
    if not sI.issubset(set(J)):
        return 0, ()
    K = tuple(x for x in J if x not in sI)
    sgn, full = wedge_basis(I, K)
    assert full == J
    return sgn, K


# ---------------------------------------------------------------------------
# 2. Verification Suites
# ---------------------------------------------------------------------------

def verify_foundations():
    print("[1/5] Verifying Chevalley-Hodge realization, double-star laws & Grassmann-Cayley meet equivalences...")
    test_metrics = [
        ("Euclidean R^3", (Fraction(1), Fraction(1), Fraction(1))),
        ("Euclidean R^4", (Fraction(1), Fraction(1), Fraction(1), Fraction(1))),
        ("Lorentzian R^{1,1}", (Fraction(1), Fraction(-1))),
        ("Minkowski R^{3,1}", (Fraction(1), Fraction(1), Fraction(1), Fraction(-1))),
        ("Split R^{2,2}", (Fraction(1), Fraction(1), Fraction(-1), Fraction(-1))),
        ("Rational diag(2,-3,5)", (Fraction(2), Fraction(-3), Fraction(5))),
        ("Degenerate PGA R^{3,0,1}", (Fraction(1), Fraction(1), Fraction(1), Fraction(0))),
    ]

    for label, q in test_metrics:
        n = len(q)
        omega = {tuple(range(n)): Fraction(1)}
        prod_q = Fraction(1)
        for qi in q:
            prod_q *= qi

        for k in range(n + 1):
            for I in itertools.combinations(range(n), k):
                mvI = {I: Fraction(1)}
                s_hodge, Jc = hodge_star_right_basis(n, q, I)
                hodge_mv = mv_clean({Jc: s_hodge})
                cliff_mv = mv_clifford_mul(q, mv_rev(mvI), omega)
                assert hodge_mv == cliff_mv, f"Chevalley-Hodge mismatch in {label} on {I}"

                # Double star check
                s2, I2 = hodge_star_right_basis(n, q, Jc)
                lhs_double = mv_clean({I2: s_hodge * s2})
                rhs_double = mv_scale(((-1) ** (k * (n - k))) * prod_q, mvI)
                assert lhs_double == rhs_double, f"Double-star mismatch in {label} on {I}"

    # Verify equivalence of Right-Star Meet == Left-Star Meet == BBR1 Shuffle Meet across 1 <= n <= 5
    total_blade_pairs = 0
    for n in range(1, 6):
        q1 = (Fraction(1),) * n
        for r in range(n + 1):
            for s in range(n + 1):
                for I in itertools.combinations(range(n), r):
                    for J in itertools.combinations(range(n), s):
                        total_blade_pairs += 1
                        mv_r = mv_vee(n, {I: Fraction(1)}, {J: Fraction(1)})

                        # Left star meet
                        sL_A, cI = hodge_star_left_basis(n, q1, I)
                        sL_B, cJ = hodge_star_left_basis(n, q1, J)
                        sw, W = wedge_basis(cI, cJ)
                        if sw == 0:
                            mv_l = {}
                        else:
                            k = r + s - n
                            sL_W, K = hodge_star_left_basis(n, q1, W)
                            mv_l = mv_clean({K: sL_A * sL_B * sw * sL_W * ((-1) ** (k * (n - k)))})

                        bbr1, bbr2 = bbr_shuffle_splits_basis(n, I, J)
                        assert mv_r == mv_l == bbr1, f"Canonical meet mismatch at n={n}, I={I}, J={J}"
                        if r + s >= n:
                            k = r + s - n
                            assert bbr2 == mv_scale((-1) ** (k * (n - s)), mv_r)

    # Generic non-coordinate-aligned subspace associativity & commutation in P^3 (n = 4)
    v1 = {(0,): Fraction(1), (1,): Fraction(2), (3,): Fraction(-1)}
    v2 = {(1,): Fraction(1), (2,): Fraction(-3)}
    v3 = {(0,): Fraction(2), (2,): Fraction(1), (3,): Fraction(4)}
    v4 = {(0,): Fraction(-1), (1,): Fraction(1), (2,): Fraction(2), (3,): Fraction(-3)}
    P1 = mv_wedge(mv_wedge(v1, v2), v3)   # generic plane (grade 3)
    P2 = mv_wedge(mv_wedge(v1, v2), v4)   # generic plane (grade 3)
    P3 = mv_wedge(mv_wedge(v1, v3), v4)   # generic plane (grade 3)
    lhs_assoc = mv_vee(4, mv_vee(4, P1, P2), P3)
    rhs_assoc = mv_vee(4, P1, mv_vee(4, P2, P3))
    assert lhs_assoc == rhs_assoc and len(lhs_assoc) > 0, "Generic meet associativity failed in P^3"
    assert mv_vee(4, P2, P1) == mv_scale(-1, mv_vee(4, P1, P2)), "Generic plane swap failed in P^3"

    print(f"      PASS ({len(test_metrics)} algebras, {total_blade_pairs} blade pairs, generic non-aligned flats).")


def verify_dimension_sum_parity_invariance():
    print("[2/5] Verifying universal parity equivalence of vector, projective, and codimension sums...")
    checked = 0
    for n in range(1, 12):
        for r in range(1, n + 1):
            for s in range(1, n + 1):
                p_sum = (r - 1) + (s - 1)
                c_sum = (n - r) + (n - s)
                v_sum = r + s
                assert (p_sum % 2) == (v_sum % 2) == (c_sum % 2)
                checked += 1
        for r in range(0, n + 1):
            for s in range(0, n + 1):
                if r + s >= n:
                    k = r + s - n
                    assert (k * (n - k)) % 2 == ((r + s) * (n - 1)) % 2
    print(f"      PASS ({checked} dimension triples; k(n-k) === (r+s)(n-1) mod 2 verified).")


def verify_all_seven_sign_laws():
    print("[3/5] Verifying exact blade-level formulas for all 7 projective intersection conventions...")
    checked = 0
    for n in range(1, 6):
        q1 = (Fraction(1),) * n
        omega = {tuple(range(n)): Fraction(1)}
        om_inv = mv_rev(omega)

        for r in range(0, n + 1):
            for s in range(0, n + 1):
                if r + s < n:
                    continue
                k = r + s - n
                for I in itertools.combinations(range(n), r):
                    compI = [x for x in range(n) if x not in set(I)]
                    for shared in itertools.combinations(I, k):
                        J = tuple(sorted(compI + list(shared)))
                        checked += 1
                        mvA = {I: Fraction(1)}
                        mvB = {J: Fraction(1)}
                        meet = mv_vee(n, mvA, mvB)
                        assert len(meet) == 1 and next(iter(meet.values())) in (-1, 1)

                        # L1: Forward 3-star *((*A) ^ (*B))
                        fwd = mv_vee_forward3star(n, mvA, mvB)
                        s_L1 = (-1) ** (k * (n - k))
                        assert fwd == mv_scale(s_L1, meet)

                        # L2: Regressive commutation B v A
                        swp = mv_vee(n, mvB, mvA)
                        s_L2 = (-1) ** ((n - r) * (n - s))
                        assert swp == mv_scale(s_L2, meet)

                        # L3: BBR2 second shuffle split
                        _, bbr2 = bbr_shuffle_splits_basis(n, I, J)
                        s_L3 = (-1) ** (k * (n - s))
                        assert bbr2 == mv_scale(s_L3, meet)

                        # L4: Cartan left interior (*A) _|C B
                        s_stA, cI = hodge_star_right_basis(n, q1, I)
                        s_car, K_car = cartan_left_basis(cI, J)
                        mv_carL = mv_clean({K_car: s_stA * s_car})
                        s_L4 = (-1) ** (k * (n - r))
                        assert mv_carL == mv_scale(s_L4, meet)

                        # L5: Cartan right interior A |_C (*B)
                        # <C, A |_C (*B)> = <C ^ (*B), A> -> sign (-1)^{(s+k)(n-s)}
                        s_stB, cJ = hodge_star_right_basis(n, q1, J)
                        K_carR = tuple(x for x in I if x not in set(cJ))
                        s_wR, fullR = wedge_basis(K_carR, cJ)
                        assert fullR == I
                        mv_carR = mv_clean({K_carR: s_stB * s_wR})
                        s_L5 = (-1) ** ((s + k) * (n - s))
                        assert mv_carR == mv_scale(s_L5, meet)

                        # L6: Dorst left contraction (*A) _| B
                        mv_dorL = mv_scale(rev_sign(n - r), mv_carL)
                        s_L6 = (-1) ** (k * (n - r) + (n - r) * (n - r - 1) // 2)
                        assert mv_dorL == mv_scale(s_L6, meet)

                        # L7: Unreverted Clifford ((A * om^{-1}) ^ (B * om^{-1})) * om
                        dA = mv_clifford_mul(q1, mvA, om_inv)
                        dB = mv_clifford_mul(q1, mvB, om_inv)
                        mv_cl = mv_clifford_mul(q1, mv_wedge(dA, dB), omega)
                        s_L7 = (-1) ** (
                            r * (r - 1) // 2
                            + s * (s - 1) // 2
                            + (2 * n - r - s) * (2 * n - r - s - 1) // 2
                            + k * (n - k)
                        )
                        assert mv_cl == mv_scale(s_L7, meet)

    print(f"      PASS ({checked} transverse spanning blade pairs across 1 <= n <= 5).")


def verify_positive_regime_and_refutations():
    print("[4/5] Verifying positive even-n regime and refutations of Conjecture 00000007618...")

    laws = {
        "L1_Forward3Star": lambda n, r, s: (-1) ** ((r + s - n) * (2 * n - r - s)),
        "L2_Commutation": lambda n, r, s: (-1) ** ((n - r) * (n - s)),
        "L3_BBR2_Split": lambda n, r, s: (-1) ** ((r + s - n) * (n - s)),
        "L4_CartanLeft": lambda n, r, s: (-1) ** ((r + s - n) * (n - r)),
        "L5_CartanRight": lambda n, r, s: (-1) ** ((r + 2 * s - n) * (n - s)),
        "L6_DorstLeft": lambda n, r, s: (-1) ** ((r + s - n) * (n - r) + (n - r) * (n - r - 1) // 2),
        "L7_UnrevClifford": lambda n, r, s: (-1) ** (
            r * (r - 1) // 2
            + s * (s - 1) // 2
            + (2 * n - r - s) * (2 * n - r - s - 1) // 2
            + (r + s - n) * (2 * n - r - s)
        ),
    }

    # 1. L1 dichotomy across 1 <= n <= 10
    for n in range(1, 11):
        pairs = [(r, s) for r in range(n + 1) for s in range(n + 1) if r + s >= n]
        spec = sorted(set(laws["L1_Forward3Star"](n, r, s) for r, s in pairs))
        matches_mod2 = all(laws["L1_Forward3Star"](n, r, s) == (-1) ** (r + s) for r, s in pairs)
        if n % 2 == 0:
            assert spec == [-1, 1] and matches_mod2, f"Expected L1 to hold at even n={n}"
            if n >= 4:
                proper = [(r, s) for r in range(1, n) for s in range(1, n) if r + s >= n]
                spec_prop = sorted(set(laws["L1_Forward3Star"](n, r, s) for r, s in proper))
                assert spec_prop == [-1, 1]
        else:
            assert spec == [1] and not matches_mod2, f"Expected L1 to collapse to {{+1}} at odd n={n}"

    # 2. L2-L7 fail (-1)^{r+s} for EVERY n >= 1, and fail Clause 2 ALONE on proper flats in P^3 (n = 4)
    for name in ["L2_Commutation", "L3_BBR2_Split", "L4_CartanLeft", "L5_CartanRight", "L6_DorstLeft", "L7_UnrevClifford"]:
        fn = laws[name]
        for n in range(1, 11):
            pairs = [(r, s) for r in range(n + 1) for s in range(n + 1) if r + s >= n]
            assert not all(fn(n, r, s) == (-1) ** (r + s) for r, s in pairs), f"{name} unexpectedly held at n={n}"

        # Pure Clause 2 check on proper nonempty flats in P^3 (n = 4):
        # Must find (r1, s1) and (r2, s2) in {1,2,3}^2 with r1 + s1 == r2 + s2 >= 4 and fn(4, r1, s1) != fn(4, r2, s2)!
        proper_p3 = [(r, s) for r in range(1, 4) for s in range(1, 4) if r + s >= 4]
        by_sum = {}
        for r, s in proper_p3:
            by_sum.setdefault(r + s, set()).add(fn(4, r, s))
        assert any(len(vals) > 1 for vals in by_sum.values()), f"{name} unexpectedly factored through r+s in P^3"

    print("      PASS (L1 even/odd dichotomy verified for 1 <= n <= 10; L2-L7 refuted for all n >= 1 & Clause 2 in P^3).")


def verify_arbitrary_metric_three_star_and_minkowski():
    print("[5/5] Verifying arbitrary-metric three-star identity & 4D Minkowski R^{3,1} sign flip...")
    q_gen = (Fraction(2), Fraction(-3), Fraction(5), Fraction(-7))
    det_sq = Fraction(1)
    for qi in q_gen:
        det_sq *= qi * qi

    for r in range(5):
        for s in range(5):
            if r + s < 4:
                continue
            k = r + s - 4
            for I in itertools.combinations(range(4), r):
                for J in itertools.combinations(range(4), s):
                    sA, cI = hodge_star_right_basis(4, q_gen, I)
                    sB, cJ = hodge_star_right_basis(4, q_gen, J)
                    sw, W = wedge_basis(cI, cJ)
                    meet = mv_vee(4, {I: Fraction(1)}, {J: Fraction(1)})
                    if sw == 0:
                        assert meet == {}
                    else:
                        sFwd, K = hodge_star_right_basis(4, q_gen, W)
                        lhs = {K: sA * sB * sw * sFwd}
                        rhs = mv_scale(((-1) ** (k * (4 - k))) * det_sq, meet)
                        assert lhs == rhs

    # Minkowski R^{3,1} double-star vs inverse-star sign flip at n = 4, r = 2, s = 2
    q_mink = (Fraction(1), Fraction(1), Fraction(1), Fraction(-1))
    I, J = (0, 1), (2, 3)
    sA, cI = hodge_star_right_basis(4, q_mink, I)
    sB, cJ = hodge_star_right_basis(4, q_mink, J)
    sw, W = wedge_basis(cI, cJ)
    sFwd, K = hodge_star_right_basis(4, q_mink, W)
    # Inverse of *_mink on W = (0,1,2,3): since *_mink(1) = +omega_4, *_mink^{-1}(omega_4) = +1,
    # whereas *_mink(omega_4) = -1!
    inv_meet_mink = sA * sB * sw * Fraction(1)   # = -1 * (e_{01} v e_{23})
    fwd_meet_mink = sA * sB * sw * sFwd          # = +1 * (e_{01} v e_{23})
    assert inv_meet_mink == -1 and fwd_meet_mink == 1
    assert fwd_meet_mink // inv_meet_mink == -1  # opposite to (-1)^{2+2} = +1!
    print("      PASS (Arbitrary-metric three-star identity & Minkowski R^{3,1} double-star sign flip verified).")


def main():
    print("=======================================================================")
    print("  Exact Rational Verification Suite — Conjecture 00000007618")
    print("=======================================================================")
    verify_foundations()
    verify_dimension_sum_parity_invariance()
    verify_all_seven_sign_laws()
    verify_positive_regime_and_refutations()
    verify_arbitrary_metric_three_star_and_minkowski()
    print("=======================================================================")
    print("  ALL VERIFICATION CHECKS PASSED — VERDICT: FALSE (REFUTED)")
    print("=======================================================================")


if __name__ == "__main__":
    main()
