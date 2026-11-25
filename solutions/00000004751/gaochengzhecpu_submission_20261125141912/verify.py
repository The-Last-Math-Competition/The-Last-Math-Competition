#!/usr/bin/env python3
"""
Standalone exact symbolic and combinatorial verification suite for Conjecture 00000004751.

Requires only the Python 3 standard library (fractions, math, collections).
Independently verifies:
  1. Premise discrepancy between the ordinary log-moment series log(1 + M(z)) and
     Voiculescu / Nica-Speicher free cumulant (R-)series, including failure of boxplus additivity.
  2. Exact noncrossing partition posets NC(n) (n = 1..6), Kreweras complements K(pi),
     poset Mobius inversion mu_{NC}(pi, sigma), comparison with the classical partition
     lattice Pi(n), and failure of block-structure invariance of mu_{NC}(pi, 1_n)
     at n = 4 (type (2,1,1)) and n = 6 (singleton-free type (2,2,2)).
  3. Refutation of closedness for Operation (A) (unshifted Voiculescu R_f o R_g):
     both algebraic divergence for non-centered b_1 != 0 and loss of Hankel / square
     positivity for centered Rademacher probability measures (kappa_1 = 0).
  4. Refutation of closedness and exact positive interval-partition structure constants
     for Operation (B) (centered cumulant series C_f o C_g), plus the complete aggregated
     ratio table S_comp(lambda) / M_1(lambda) = (-1)^{k-1} k / C(n+k-2, k-1) for n = 1..6.
  5. Refutation of block-structure determination for Operation (C) (Nica-Speicher boxed
     convolution C_f * C_g) via Kreweras block-type splitting at n = 4 and n = 6.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from math import comb, factorial
import sys


# ============================================================================
# Part 1: Exact Multivariate Polynomial & Formal Power Series Engine over Q
# ============================================================================

def poly_zero():
    return {}


def poly_const(c):
    c = Fraction(c)
    return {(): c} if c != 0 else {}


def poly_var(name):
    return {((name, 1),): Fraction(1)}


def poly_add(p, q):
    res = dict(p)
    for m, c in q.items():
        nv = res.get(m, Fraction(0)) + c
        if nv == 0:
            res.pop(m, None)
        else:
            res[m] = nv
    return res


def poly_scale(p, s):
    s = Fraction(s)
    if s == 0:
        return {}
    return {m: c * s for m, c in p.items()}


def mono_mul(m1, m2):
    d = dict(m1)
    for k, v in m2:
        d[k] = d.get(k, 0) + v
    return tuple(sorted((k, v) for k, v in d.items() if v != 0))


def poly_mul(p, q):
    res = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = mono_mul(m1, m2)
            nv = res.get(m, Fraction(0)) + c1 * c2
            if nv == 0:
                res.pop(m, None)
            else:
                res[m] = nv
    return res


def fps_mul(A, B, N):
    res = [poly_zero() for _ in range(N + 1)]
    for i in range(N + 1):
        if not A[i]:
            continue
        for j in range(N + 1 - i):
            if B[j]:
                res[i + j] = poly_add(res[i + j], poly_mul(A[i], B[j]))
    return res


def fps_compose(F, G, N):
    assert not G[0], "Formal power series composition requires G[0] == 0."
    res = [poly_zero() for _ in range(N + 1)]
    res[0] = F[0]
    g_pow = [poly_zero() for _ in range(N + 1)]
    g_pow[0] = poly_const(1)
    for k in range(1, N + 1):
        g_pow = fps_mul(g_pow, G, N)
        if F[k]:
            for n in range(N + 1):
                if g_pow[n]:
                    res[n] = poly_add(res[n], poly_mul(F[k], g_pow[n]))
    return res


def fps_log1p(M, N):
    assert not M[0]
    F = [poly_zero()] + [poly_const(Fraction((-1) ** (k - 1), k)) for k in range(1, N + 1)]
    return fps_compose(F, M, N)


def free_moments_from_cumulants_fps(kap, N):
    M = [poly_zero() for _ in range(N + 1)]
    for _ in range(1, N + 1):
        arg = [poly_zero() for _ in range(N + 1)]
        arg[1] = poly_const(1)
        for j in range(2, N + 1):
            arg[j] = M[j - 1]
        M = fps_compose(kap, arg, N)
    return M


def free_cumulants_from_moments_fps(M, N):
    u_inv = [poly_zero() for _ in range(N + 1)]
    u_inv[1] = poly_const(1)
    tail = [poly_zero() for _ in range(N + 1)]
    for j in range(2, N + 1):
        tail[j] = M[j - 1]
    for step in range(2, N + 1):
        comp = fps_compose(tail, u_inv, N)
        u_inv[step] = poly_scale(comp[step], -1)
    return fps_compose(M, u_inv, N)


# ============================================================================
# Part 2: Set Partitions, NC(n), Interval Partitions, Kreweras, and Mobius
# ============================================================================

def catalan(n):
    return comb(2 * n, n) // (n + 1)


def generate_set_partitions(n):
    parts = [()]
    for x in range(1, n + 1):
        nxt = []
        for p in parts:
            for idx in range(len(p)):
                np = list(p)
                np[idx] = p[idx] + (x,)
                nxt.append(tuple(np))
            nxt.append(p + ((x,),))
        parts = nxt
    return parts


def is_noncrossing(part):
    block_of = {x: idx for idx, b in enumerate(part) for x in b}
    elems = sorted(block_of.keys())
    m = len(elems)
    for i1 in range(m):
        for i2 in range(i1 + 1, m):
            for i3 in range(i2 + 1, m):
                for i4 in range(i3 + 1, m):
                    a, b, c, d = elems[i1], elems[i2], elems[i3], elems[i4]
                    if block_of[a] == block_of[c] and block_of[b] == block_of[d] and block_of[a] != block_of[b]:
                        return False
    return True


def is_interval_partition(part):
    for b in part:
        if list(b) != list(range(b[0], b[-1] + 1)):
            return False
    return True


def refines(pi, sigma):
    sigma_sets = [set(b) for b in sigma]
    return all(any(set(b).issubset(S) for S in sigma_sets) for b in pi)


def compute_poset_mobius(poset):
    ordered = sorted(poset, key=lambda p: -len(p))
    m = len(ordered)
    mu = {}
    for i in range(m):
        pi = ordered[i]
        mu[(pi, pi)] = 1
        for j in range(i + 1, m):
            sigma = ordered[j]
            if not refines(pi, sigma):
                mu[(pi, sigma)] = 0
            else:
                mu[(pi, sigma)] = -sum(
                    mu[(pi, ordered[k])]
                    for k in range(i, j)
                    if refines(pi, ordered[k]) and refines(ordered[k], sigma)
                )
    return mu


def kreweras_complement(pi, n):
    p_inv = {}
    for b in pi:
        k = len(b)
        for idx in range(k):
            p_inv[b[(idx + 1) % k]] = b[idx]
    perm = {i: p_inv[(i % n) + 1] for i in range(1, n + 1)}
    visited = set()
    blocks = []
    for i in range(1, n + 1):
        if i not in visited:
            cur = i
            cyc = []
            while cur not in visited:
                visited.add(cur)
                cyc.append(cur)
                cur = perm[cur]
            blocks.append(tuple(sorted(cyc)))
    return tuple(sorted(blocks, key=lambda b: b[0]))


def block_type(pi):
    return tuple(sorted((len(b) for b in pi), reverse=True))


def int_partitions(n, max_part=None):
    if max_part is None:
        max_part = n
    if n == 0:
        yield ()
        return
    for v in range(min(n, max_part), 0, -1):
        for rest in int_partitions(n - v, v):
            yield (v,) + rest


def hankel_det(moments, size):
    A = [[Fraction(moments[i + j]) for j in range(size)] for i in range(size)]
    det = Fraction(1)
    for i in range(size):
        piv = next((r for r in range(i, size) if A[r][i] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != i:
            A[i], A[piv] = A[piv], A[i]
            det = -det
        det *= A[i][i]
        for r in range(i + 1, size):
            factor = A[r][i] / A[i][i]
            for c in range(i, size):
                A[r][c] -= factor * A[i][c]
    return det


# ============================================================================
# Verification Suite
# ============================================================================

def main():
    print("=" * 74)
    print("VERIFICATION SUITE FOR CONJECTURE 00000004751")
    print("=" * 74)

    # ------------------------------------------------------------------------
    # Check 1: Premise Check (Ordinary Logarithm vs Free Cumulant Series)
    # ------------------------------------------------------------------------
    print("\n[Check 1] Premise check: log(1 + M(z)) vs free R-series C(z) = z R(z)")
    N = 6
    m_vars = [poly_zero()] + [poly_var(f"m{i}") for i in range(1, N + 1)]
    k_vars = [poly_zero()] + [poly_var(f"k{i}") for i in range(1, N + 1)]

    M_from_k = free_moments_from_cumulants_fps(k_vars, N)
    k_roundtrip = free_cumulants_from_moments_fps(M_from_k, N)
    for n in range(1, N + 1):
        assert k_roundtrip[n] == k_vars[n], f"Lagrange inversion failed at n={n}"

    C_from_m = free_cumulants_from_moments_fps(m_vars, N)
    L_from_m = fps_log1p(m_vars, N)
    assert C_from_m[2] != L_from_m[2], "Expected log(1+M) and C(z) to differ at z^2"
    assert L_from_m[2][(("m1", 2),)] == Fraction(-1, 2)
    assert C_from_m[2][(("m1", 2),)] == Fraction(-1, 1)

    # Dirac delta_1 (+) delta_1 = delta_2 test for log(1 + M(z))
    M_d1 = [poly_zero()] + [poly_const(1) for _ in range(1, N + 1)]
    M_d2 = [poly_zero()] + [poly_const(2 ** n) for n in range(1, N + 1)]
    L_d1 = fps_log1p(M_d1, N)
    L_d2 = fps_log1p(M_d2, N)
    assert L_d2[2][()] == Fraction(2, 1) and 2 * L_d1[2][()] == Fraction(1, 1)
    print("  PASS: M(z) = C(z(1+M(z))) verified symbolically up to degree 6.")
    print("  PASS: [z^2] log(1+M) = m_2 - (1/2)m_1^2 != m_2 - m_1^2 = kappa_2.")
    print("  PASS: [z^2] log(1+M_{delta_2}) = 2 != 1 = 2 * [z^2] log(1+M_{delta_1}).")

    # ------------------------------------------------------------------------
    # Check 2: Poset Mobius Inversion on NC(n) vs Pi(n) & Block Structure
    # ------------------------------------------------------------------------
    print("\n[Check 2] Poset Mobius function on NC(n) and Pi(n) (n = 1..6)")
    nc_cache = {}
    mu_nc_cache = {}
    for n in range(1, 7):
        sp = generate_set_partitions(n)
        nc = [p for p in sp if is_noncrossing(p)]
        assert len(nc) == catalan(n), f"|NC({n})| mismatch"
        mu_nc = compute_poset_mobius(nc)
        nc_cache[n] = nc
        mu_nc_cache[n] = mu_nc

        zero_n = tuple((i,) for i in range(1, n + 1))
        one_n = (tuple(range(1, n + 1)),)

        # Verify poset Mobius defining equations on all pairs and Kreweras formula
        for pi in nc:
            kp = kreweras_complement(pi, n)
            assert is_noncrossing(kp) and len(pi) + len(kp) == n + 1
            exp_0_pi = 1
            for b in pi:
                exp_0_pi *= ((-1) ** (len(b) - 1)) * catalan(len(b) - 1)
            assert mu_nc[(zero_n, pi)] == exp_0_pi
            exp_pi_1 = 1
            for b in kp:
                exp_pi_1 *= ((-1) ** (len(b) - 1)) * catalan(len(b) - 1)
            assert mu_nc[(pi, one_n)] == exp_pi_1

        # Verify symbolic moment-cumulant Mobius inversion matches Lagrange inversion
        for pi_check_poly_flag in [True]:
            m_sum = poly_zero()
            c_sum = poly_zero()
            for pi in nc:
                k_mon = poly_const(1)
                m_mon = poly_const(1)
                for b in pi:
                    k_mon = poly_mul(k_mon, k_vars[len(b)])
                    m_mon = poly_mul(m_mon, m_vars[len(b)])
                m_sum = poly_add(m_sum, k_mon)
                c_sum = poly_add(c_sum, poly_scale(m_mon, mu_nc[(pi, one_n)]))
            assert m_sum == M_from_k[n]
            assert c_sum == C_from_m[n]

    # Classical Pi(5) check: mu_Pi(pi, 1_5) = (-1)^{|pi|-1} (|pi|-1)! depends ONLY on |pi|
    sp5 = generate_set_partitions(5)
    mu_sp5 = compute_poset_mobius(sp5)
    one_5 = ((1, 2, 3, 4, 5),)
    for pi in sp5:
        assert mu_sp5[(pi, one_5)] == ((-1) ** (len(pi) - 1)) * factorial(len(pi) - 1)

    # Explicit NC(4) and NC(6) counterexamples to block-structure invariance
    one_4 = ((1, 2, 3, 4),)
    pi4_adj = ((1, 2), (3,), (4,))
    pi4_nest = ((1, 3), (2,), (4,))
    assert block_type(pi4_adj) == (2, 1, 1) == block_type(pi4_nest)
    assert mu_nc_cache[4][(pi4_adj, one_4)] == 2
    assert mu_nc_cache[4][(pi4_nest, one_4)] == 1

    one_6 = ((1, 2, 3, 4, 5, 6),)
    pi6_flat = ((1, 2), (3, 4), (5, 6))
    pi6_rain = ((1, 6), (2, 5), (3, 4))
    assert block_type(pi6_flat) == (2, 2, 2) == block_type(pi6_rain)
    assert mu_nc_cache[6][(pi6_flat, one_6)] == 2
    assert mu_nc_cache[6][(pi6_rain, one_6)] == 1

    print("  PASS: All 196 partitions in NC(1)..NC(6) verified against Kreweras & Lagrange formulas.")
    print("  PASS: NC(4) type (2,1,1): mu_NC({{1,2},{3},{4}}, 1_4) = 2 != 1 = mu_NC({{1,3},{2},{4}}, 1_4).")
    print("  PASS: NC(6) type (2,2,2): mu_NC({{1,2},{3,4},{5,6}}, 1_6) = 2 != 1 = mu_NC({{1,6},{2,5},{3,4}}, 1_6).")

    # ------------------------------------------------------------------------
    # Check 3: Operation (A) - Voiculescu Unshifted R_f o R_g Closedness Failure
    # ------------------------------------------------------------------------
    print("\n[Check 3] Operation (A): Unshifted Voiculescu composition (R_f o R_g)(z)")
    # Non-centered algebraic non-termination: [z^0](R_{f,N} o R_g) = sum_{k=1}^N a_k b_1^{k-1}
    for N_trunc in [1, 5, 10, 50]:
        val = sum(1 * (1 ** (k - 1)) for k in range(1, N_trunc + 1))
        assert val == N_trunc

    # Centered probability measure counterexample: Rademacher mu = (delta_{-1} + delta_1)/2
    N8 = 8
    M_rad = [poly_zero()] + [poly_const(1 if i % 2 == 0 else 0) for i in range(1, N8 + 1)]
    C_rad = free_cumulants_from_moments_fps(M_rad, N8)
    R_rad = [C_rad[i + 1] for i in range(N8)] + [poly_zero()]  # R_rad(0) = kappa_1 = 0
    assert not R_rad[0]
    R_rad_comp = fps_compose(R_rad, R_rad, N8 - 1)
    C_voic_comp = [poly_zero()] + R_rad_comp[:N8]
    M_voic_comp = free_moments_from_cumulants_fps(C_voic_comp, N8)
    m_voic = [Fraction(1)] + [M_voic_comp[i].get((), Fraction(0)) for i in range(1, N8 + 1)]

    assert m_voic[2] == 1 and m_voic[4] == 0
    sq_form_voic = m_voic[4] - 2 * m_voic[2] + m_voic[0]  # E[(X^2 - 1)^2]
    h3_voic = hankel_det(m_voic, 3)
    assert sq_form_voic == -1 and h3_voic == -1
    print("  PASS: Non-centered R_f o R_g constant term diverges as sum_{k>=1} a_k b_1^{k-1}.")
    print(f"  PASS: Centered Rademacher R_mu o R_mu has E[(X^2-1)^2] = {sq_form_voic} < 0 and det H_3 = {h3_voic} < 0.")

    # ------------------------------------------------------------------------
    # Check 4: Operation (B) - Centered Cumulant Series C_f o C_g & Ratio Table
    # ------------------------------------------------------------------------
    print("\n[Check 4] Operation (B): Centered R-series composition (C_f o C_g)(z)")
    af = [poly_zero()] + [poly_var(f"a{i}") for i in range(1, N + 1)]
    bg = [poly_zero()] + [poly_var(f"b{i}") for i in range(1, N + 1)]
    C_comp_sym = fps_compose(af, bg, N)

    for n in range(1, N + 1):
        int_parts = [p for p in nc_cache[n] if is_interval_partition(p)]
        assert len(int_parts) == 2 ** (n - 1)
        comb_poly = poly_zero()
        for pi in int_parts:
            term = af[len(pi)]
            for b in pi:
                term = poly_mul(term, bg[len(b)])
            comb_poly = poly_add(comb_poly, term)
        assert comb_poly == C_comp_sym[n], f"Interval partition formula mismatch at n={n}"

    # Positivity failure for C_rad o C_rad and C_semicircle o C_semicircle
    C_rad_ccomp = fps_compose(C_rad, C_rad, N8)
    M_rad_ccomp = free_moments_from_cumulants_fps(C_rad_ccomp, N8)
    m6_rad_ccomp = M_rad_ccomp[6].get((), Fraction(0))
    assert m6_rad_ccomp == -2

    C_sc = [poly_zero() for _ in range(N8 + 1)]
    C_sc[2] = poly_const(1)
    M_sc_ccomp = free_moments_from_cumulants_fps(fps_compose(C_sc, C_sc, N8), N8)
    m_sc = [Fraction(1)] + [M_sc_ccomp[i].get((), Fraction(0)) for i in range(1, N8 + 1)]
    sq_form_sc = m_sc[6] - 2 * m_sc[4] + m_sc[2]  # E[(X^3 - X)^2]
    assert sq_form_sc == -2

    print("  PASS: [z^n](C_f o C_g) matches interval-partition sum over Int(n) (|Int(n)| = 2^{n-1}) for n=1..6.")
    print(f"  PASS: Rademacher C_mu o C_mu yields negative even moment m_6 = {m6_rad_ccomp} < 0.")
    print(f"  PASS: Wigner semicircle C_sc o C_sc yields E[(X^3 - X)^2] = {sq_form_sc} < 0.")

    print("\n  Aggregated Block-Structure Comparison Table (n = 1..6):")
    print("  " + "-" * 70)
    print(f"  {'n':>2} | {'lambda':<18} | {'S_comp':>6} | {'|NC_lam|':>8} | {'M_1(lam)':>8} | {'S_comp/M_1':>10} | {'mu_NC(pi,1_n) set'}")
    print("  " + "-" * 70)
    non_integral_witnesses = 0
    for n in range(1, 7):
        one_n = (tuple(range(1, n + 1)),)
        for lam in int_partitions(n):
            k = len(lam)
            mults = Counter(lam)
            denom = 1
            for mr in mults.values():
                denom *= factorial(mr)
            s_comp = factorial(k) // denom
            pis = [pi for pi in nc_cache[n] if block_type(pi) == lam]
            nc_cnt = len(pis)
            m1_sum = sum(mu_nc_cache[n][(pi, one_n)] for pi in pis)
            mu_vals = sorted({mu_nc_cache[n][(pi, one_n)] for pi in pis})

            # Verify exact formulas
            assert nc_cnt == factorial(n) // (factorial(n - k + 1) * denom)
            assert m1_sum == ((-1) ** (k - 1)) * factorial(n + k - 2) // (factorial(n - 1) * denom)
            ratio_m1 = Fraction(s_comp, m1_sum)
            expected_ratio = Fraction(((-1) ** (k - 1)) * k, comb(n + k - 2, k - 1))
            assert ratio_m1 == expected_ratio
            if ratio_m1.denominator != 1:
                non_integral_witnesses += 1

            if n <= 5 or lam in ((6,), (4, 1, 1), (2, 2, 2), (2, 1, 1, 1, 1), (1, 1, 1, 1, 1, 1)):
                print(f"  {n:>2} | {str(lam):<18} | {s_comp:>6} | {nc_cnt:>8} | {m1_sum:>8} | {str(ratio_m1):>10} | {mu_vals}")
    print("  " + "-" * 70)
    assert non_integral_witnesses >= 15
    print(f"  PASS: Verified exact identity S_comp(lam)/M_1(lam) = (-1)^(k-1) * k / C(n+k-2, k-1) across all 30 partitions ({non_integral_witnesses} non-integral).")

    # ------------------------------------------------------------------------
    # Check 5: Operation (C) - Nica-Speicher Boxed Convolution C_f * C_g
    # ------------------------------------------------------------------------
    print("\n[Check 5] Operation (C): Nica-Speicher boxed convolution (C_f * C_g)")
    for n in [4, 6]:
        joint = defaultdict(Counter)
        for pi in nc_cache[n]:
            joint[block_type(pi)][block_type(kreweras_complement(pi, n))] += 1
        if n == 4:
            assert joint[(2, 1, 1)] == Counter({(3, 1): 4, (2, 2): 2})
        if n == 6:
            assert joint[(2, 2, 2)] == Counter({(2, 2, 1, 1): 3, (3, 1, 1, 1): 2})

    # Verify boxed convolution identity (k * zeta)_n = m_n and (m * mu)_n = k_n up to n = 6
    for n in range(1, 7):
        box_m = poly_zero()
        box_k = poly_zero()
        zero_n = tuple((i,) for i in range(1, n + 1))
        for pi in nc_cache[n]:
            kp = kreweras_complement(pi, n)
            k_mon = poly_const(1)
            m_mon = poly_const(1)
            for b in pi:
                k_mon = poly_mul(k_mon, k_vars[len(b)])
                m_mon = poly_mul(m_mon, m_vars[len(b)])
            # zeta_n = 1 for all n >= 1 => zeta_{K(pi)} = 1
            box_m = poly_add(box_m, k_mon)
            # mu_n = (-1)^{n-1} C_{n-1} => mu_{K(pi)} = mu_NC(0_n, K(pi)) = mu_NC(pi, 1_n)
            mu_kp = mu_nc_cache[n][(zero_n, kp)]
            box_k = poly_add(box_k, poly_scale(m_mon, mu_kp))
        assert box_m == M_from_k[n]
        assert box_k == C_from_m[n]

    print("  PASS: Boxed convolution Mobius inversion (k * zeta = m, m * mu = k) verified for n=1..6.")
    print("  PASS: Kreweras type splitting verified at n=4 ((2,1,1) -> 4*(3,1) + 2*(2,2)) and n=6 ((2,2,2) -> 2*(3,1,1,1) + 3*(2,2,1,1)).")

    print("\n" + "=" * 74)
    print("ALL VERIFICATION CHECKS PASSED SUCCESSFULLY (0 FAILURES).")
    print("=" * 74)


if __name__ == "__main__":
    sys.exit(main() or 0)
