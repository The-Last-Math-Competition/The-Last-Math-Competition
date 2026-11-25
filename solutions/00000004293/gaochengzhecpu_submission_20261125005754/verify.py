#!/usr/bin/env python3
"""
Independent Computational Verification Suite for Conjecture 00000004293
========================================================================
Verifies all theorems, formulas, and counterexamples in the resolution package:
  1. Exhaustive subgroup lattice construction and maximal chain counts for
     cyclic p-groups Z/p^k Z and elementary abelian p-groups (Z/p Z)^k.
  2. Young-lattice / Pontryagin-dual exact integer polynomials P_lambda(p)
     for general finite abelian p-groups G_lambda(p).
  3. Complete census of p-groups of orders p^2 and p^3 (including Heisenberg
     UT_3(F_p), metacyclic M(p^3), D_8, and Q_8).
  4. Universal Modulo-p Congruence c(G) == 1 (mod p) across all tested p-groups.
  5. Exact closed-form quasi-polynomial
         c(G_d(p)) = 3p^4 + 10p^3 + 9p^2 + 4p + 1 + (d/p) * p^2 * (2p + 1)
     for the non-abelian semidirect family G_d(p) = (Z/p^2 Z)^2 |x_{phi_d} (Z/p Z)
     of order p^5 (k = 5), and minimal period verification showing minimal
     periods 1, 3, 4, 5, 7, 11, 13 independent of log_p |G| = 5.
"""

from itertools import product
import math
import sys


# ---------------------------------------------------------------------------
# 1. Generic Finite Group & Subgroup Lattice Primitives
# ---------------------------------------------------------------------------

def make_table(elems, mult, ident):
    """Build integer-indexed multiplication and inverse tables, checking group axioms."""
    idx = {e: i for i, e in enumerate(elems)}
    n = len(elems)
    id_i = idx[ident]
    table = [[0] * n for _ in range(n)]
    for i, a in enumerate(elems):
        row = table[i]
        for j, b in enumerate(elems):
            row[j] = idx[mult(a, b)]
    inv = [-1] * n
    for i in range(n):
        assert table[id_i][i] == i and table[i][id_i] == i, "Identity axiom failed"
        for j in range(n):
            if table[i][j] == id_i and table[j][i] == id_i:
                inv[i] = j
                break
        assert inv[i] != -1, f"Inverse missing for element {i}"
    return table, inv, id_i


def generate_subgroup(gens, table, id_i):
    """Generate subgroup closed under multiplication from a seed set of indices."""
    sub = {id_i}
    frontier = set(gens) - sub
    while frontier:
        sub |= frontier
        nf = set()
        for a in frontier:
            row_a = table[a]
            for b in sub:
                ab = row_a[b]
                if ab not in sub:
                    nf.add(ab)
                ba = table[b][a]
                if ba not in sub:
                    nf.add(ba)
        frontier = nf
    return frozenset(sub)


def enumerate_all_subgroups_bruteforce(elems, mult, ident):
    """Exhaustively enumerate the full subgroup lattice Sub(G) without Frattini shortcuts."""
    table, _, id_i = make_table(elems, mult, ident)
    n = len(elems)
    cyclic = [generate_subgroup([g], table, id_i) for g in range(n)]
    subs = {frozenset([id_i]), frozenset(range(n))} | set(cyclic)
    changed = True
    while changed:
        changed = False
        for s in list(subs):
            for c in cyclic:
                if not c.issubset(s):
                    joined = generate_subgroup(s | c, table, id_i)
                    if joined not in subs:
                        subs.add(joined)
                        changed = True
    return sorted(subs, key=len)


def count_maximal_chains_poset(subs):
    """Count maximal chains from minimum to maximum in a finite bounded poset of sets."""
    m = len(subs)
    dp = [0] * m
    dp[0] = 1
    for j in range(1, m):
        sj = subs[j]
        below = [i for i in range(j) if subs[i].issubset(sj)]
        for i in below:
            si = subs[i]
            covered = not any(
                k != i and len(subs[k]) > len(si) and si.issubset(subs[k])
                for k in below
            )
            if covered:
                dp[j] += dp[i]
    return dp[-1]


def p_power(x, p, table, id_i):
    res = id_i
    for _ in range(p):
        res = table[res][x]
    return res


def maximal_subgroups_frattini(H, p, table, inv, id_i):
    """Enumerate all maximal subgroups of a finite p-group H via H / Phi(H) hyperplanes."""
    if len(H) == 1:
        return []
    H_list = sorted(H)
    gens_phi = {p_power(x, p, table, id_i) for x in H_list}
    for idx_x, x in enumerate(H_list):
        ix = inv[x]
        for y in H_list[idx_x + 1:]:
            comm = table[table[ix][inv[y]]][table[x][y]]
            if comm != id_i:
                gens_phi.add(comm)
    phi = generate_subgroup(gens_phi, table, id_i)

    basis = []
    cur = phi
    for x in H_list:
        if x not in cur:
            basis.append(x)
            cur = generate_subgroup(cur | {x}, table, id_i)
            if len(cur) == len(H):
                break
    d = len(basis)
    assert (p ** d) * len(phi) == len(H), "Burnside-Frattini index mismatch"
    if d == 1:
        return [phi]

    coatoms = []
    for pivot in range(d):
        for tail in product(range(p), repeat=(d - 1 - pivot)):
            h_gens = set(phi)
            for j in range(pivot):
                h_gens.add(basis[j])
            for offset, c_j in enumerate(tail):
                j = pivot + 1 + offset
                neg_c = (-c_j) % p
                bp_pow = id_i
                for _ in range(neg_c):
                    bp_pow = table[bp_pow][basis[pivot]]
                h_gens.add(table[basis[j]][bp_pow])
            M = generate_subgroup(h_gens, table, id_i)
            assert len(M) * p == len(H), "Maximal subgroup index != p"
            coatoms.append(M)
    assert len(coatoms) == (p ** d - 1) // (p - 1)
    return coatoms


def count_maximal_chains_frattini(elems, mult, ident, p):
    """Exact recursive DP of c(G) over Frattini coatoms."""
    table, inv, id_i = make_table(elems, mult, ident)
    memo = {}

    def dp(H):
        if len(H) == 1:
            return 1
        if H in memo:
            return memo[H]
        val = sum(dp(M) for M in maximal_subgroups_frattini(H, p, table, inv, id_i))
        assert val % p == 1, f"Universal mod-p congruence failed on subgroup of size {len(H)}"
        memo[H] = val
        return val

    G = frozenset(range(len(elems)))
    return dp(G)


# ---------------------------------------------------------------------------
# 2. Concrete p-Group Constructors & Closed-Form Formulas
# ---------------------------------------------------------------------------

def abelian_group(orders):
    elems = list(product(*(range(n) for n in orders)))
    ident = tuple(0 for _ in orders)
    def mult(a, b):
        return tuple((x + y) % n for x, y, n in zip(a, b, orders))
    return elems, mult, ident


def heisenberg_ut3(p):
    elems = list(product(range(p), repeat=3))
    ident = (0, 0, 0)
    def mult(a, b):
        return ((a[0] + b[0]) % p, (a[1] + b[1]) % p, (a[2] + b[2] + a[0] * b[1]) % p)
    return elems, mult, ident


def metacyclic_p3(p):
    elems = [(a, b) for a in range(p * p) for b in range(p)]
    ident = (0, 0)
    def mult(x, y):
        return ((x[0] + y[0] * (1 + x[1] * p)) % (p * p), (x[1] + y[1]) % p)
    return elems, mult, ident


def quaternion_q8():
    elems = [(a, b) for a in range(4) for b in range(2)]
    ident = (0, 0)
    def mult(x, y):
        a1, b1 = x
        a2, b2 = y
        a2_conj = a2 if b1 == 0 else (-a2) % 4
        carry = 2 if (b1 == 1 and b2 == 1) else 0
        return ((a1 + a2_conj + carry) % 4, (b1 + b2) % 2)
    return elems, mult, ident


def quadratic_semidirect_p5(p, d):
    p2 = p * p
    elems = [(u, v, b) for u in range(p2) for v in range(p2) for b in range(p)]
    ident = (0, 0, 0)
    def mult(x, y):
        u1, v1, b1 = x
        u2, v2, b2 = y
        u2_act = (u2 + b1 * p * d * v2) % p2
        v2_act = (v2 + b1 * p * u2) % p2
        return ((u1 + u2_act) % p2, (v1 + v2_act) % p2, (b1 + b2) % p)
    return elems, mult, ident


def flag_factorial(k, p):
    ans = 1
    for j in range(1, k + 1):
        ans *= sum(p ** i for i in range(j))
    return ans


def abelian_partition_poly_eval(lam, p):
    """Evaluate exact polynomial P_lambda(p) via Pontryagin-dual Young lattice recursion."""
    lam = tuple(sorted((x for x in lam if x > 0), reverse=True))
    if not lam:
        return 1
    distinct_parts = sorted(set(lam))
    total = 0
    for j in distinct_parts:
        m_j = lam.count(j)
        s_gt = sum(1 for x in lam if x > j)
        branch_count = (p ** s_gt) * sum(p ** i for i in range(m_j))
        # Decrement one part of size j
        new_lam = list(lam)
        new_lam.remove(j)
        if j - 1 > 0:
            new_lam.append(j - 1)
        total += branch_count * abelian_partition_poly_eval(tuple(new_lam), p)
    return total


def legendre_symbol(d, p):
    assert p >= 3
    r = d % p
    if r == 0:
        return 0
    val = pow(r, (p - 1) // 2, p)
    return 1 if val == 1 else -1


def gd_closed_form(p, d):
    leg = legendre_symbol(d, p)
    return 3 * p**4 + 10 * p**3 + 9 * p**2 + 4 * p + 1 + leg * (p**2) * (2 * p + 1)


# ---------------------------------------------------------------------------
# 3. Verification Suite Execution
# ---------------------------------------------------------------------------

def main():
    print("=" * 72)
    print("Conjecture 00000004293 — Independent Verification Suite")
    print("=" * 72)
    checks_run = 0

    # [Check 1] Cyclic p-groups Z/p^k Z (exhaustive brute-force poset + Frattini DP)
    print("\n[1] Cyclic p-groups Z/p^k Z (k = 1..4):")
    for k in [1, 2, 3, 4]:
        primes = [2, 3, 5, 7] if k <= 2 else ([2, 3, 5] if k == 3 else [2, 3])
        for p in primes:
            elems, mult, ident = abelian_group([p ** k])
            subs = enumerate_all_subgroups_bruteforce(elems, mult, ident)
            c_poset = count_maximal_chains_poset(subs)
            c_frat = count_maximal_chains_frattini(elems, mult, ident, p)
            assert len(subs) == k + 1, f"Expected {k+1} subgroups, got {len(subs)}"
            assert c_poset == 1 and c_frat == 1
            assert c_poset % p == 1
            checks_run += 1
        status = "WITNESS (period 1 = k)" if k == 1 else f"COUNTEREXAMPLE (period 1 < {k})"
        print(f"  k={k}: verified p in {primes} -> |Sub(G)|={k+1}, c(Z/p^{k}Z) = 1 [{status}]")

    # [Check 2] Elementary abelian p-groups (Z/p Z)^k
    print("\n[2] Elementary abelian p-groups (Z/p Z)^k (k = 2..4):")
    for k, primes, use_brute in [(2, [2, 3, 5, 7], True), (3, [2, 3, 5], True), (4, [2, 3], False)]:
        vals = {}
        for p in primes:
            elems, mult, ident = abelian_group([p] * k)
            c_frat = count_maximal_chains_frattini(elems, mult, ident, p)
            expected = flag_factorial(k, p)
            assert c_frat == expected, f"Mismatch for (Z/{p}Z)^{k}: {c_frat} != {expected}"
            if use_brute and len(elems) <= 125:
                subs = enumerate_all_subgroups_bruteforce(elems, mult, ident)
                c_poset = count_maximal_chains_poset(subs)
                assert c_poset == expected
            assert c_frat % p == 1
            vals[p] = c_frat
            checks_run += 1
        print(f"  k={k}: c((Z/pZ)^{k}) = [k]_p! verified for {vals} (polynomial quasi-period 1 < {k})")

    # [Check 3] General finite abelian p-groups G_lambda(p)
    print("\n[3] General finite abelian p-groups G_lambda(p):")
    partitions = [(2, 1), (3, 1), (2, 2), (2, 1, 1)]
    for lam in partitions:
        k = sum(lam)
        primes = [2, 3, 5] if k <= 3 else [2, 3]
        vals = {}
        for p in primes:
            elems, mult, ident = abelian_group([p ** part for part in lam])
            c_frat = count_maximal_chains_frattini(elems, mult, ident, p)
            c_poly = abelian_partition_poly_eval(lam, p)
            assert c_frat == c_poly, f"Partition {lam}, p={p}: {c_frat} != {c_poly}"
            assert c_frat % p == 1
            vals[p] = c_frat
            checks_run += 1
        print(f"  lambda={lam} (k={k}): exact polynomial match {vals} (quasi-period 1 < {k})")

    # [Check 4] Complete census of non-abelian p-groups of order p^3
    print("\n[4] Non-abelian p-groups of order p^3 (k = 3):")
    ut3_vals = {}
    m_vals = {}
    for p in [2, 3, 5, 7]:
        elems_u, mult_u, id_u = heisenberg_ut3(p)
        cu = count_maximal_chains_frattini(elems_u, mult_u, id_u, p)
        if p <= 5:
            assert cu == count_maximal_chains_poset(enumerate_all_subgroups_bruteforce(elems_u, mult_u, id_u))
        if p >= 3:
            assert cu == (p + 1) ** 2
        else:
            assert cu == 7  # D_8
        assert cu % p == 1
        ut3_vals[p] = cu
        checks_run += 1

        if p >= 3:
            elems_m, mult_m, id_m = metacyclic_p3(p)
            cm = count_maximal_chains_frattini(elems_m, mult_m, id_m, p)
            if p <= 5:
                assert cm == count_maximal_chains_poset(enumerate_all_subgroups_bruteforce(elems_m, mult_m, id_m))
            assert cm == 2 * p + 1
            assert cm % p == 1
            m_vals[p] = cm
            checks_run += 1

    elems_q8, mult_q8, id_q8 = quaternion_q8()
    cq8 = count_maximal_chains_poset(enumerate_all_subgroups_bruteforce(elems_q8, mult_q8, id_q8))
    assert cq8 == 3 and cq8 % 2 == 1
    checks_run += 1
    print(f"  UT_3(F_p): {ut3_vals} (D_8 at p=2; (p+1)^2 for p>=3, PORC period 1 < 3)")
    print(f"  M(p^3) (p>=3): {m_vals} (= 2p + 1, PORC period 1 < 3); Q_8 (p=2): c = {cq8}")

    # [Check 5] Non-abelian semidirect family G_d(p) of order p^5 (k = 5)
    print("\n[5] Non-abelian semidirect family G_d(p) of order p^5 (k = 5):")
    for p, d_list in [(3, [-3, -1, 0, 1, 2, 5]), (5, [-1, 2, 5])]:
        row = {}
        for d in d_list:
            elems, mult, ident = quadratic_semidirect_p5(p, d)
            c_exact = count_maximal_chains_frattini(elems, mult, ident, p)
            c_form = gd_closed_form(p, d)
            assert c_exact == c_form, f"G_{d}({p}): exact {c_exact} != formula {c_form}"
            assert c_exact % p == 1
            row[d] = c_exact
            checks_run += 1
        print(f"  p={p} (|G|={p**5}): verified d -> c(G_d({p})) = {row}")

    # [Check 6] Minimal PORC / quasi-polynomial period verification for G_d(p) (k = 5)
    print("\n[6] Minimal quasi-period check for G_d(p) across odd primes:")
    primes_sample = [p for p in range(3, 400) if all(p % q != 0 for q in range(2, int(math.isqrt(p)) + 1))]

    def has_porc_period(d, N, p0=20):
        # Since deg(c(G_d(p))) = 4 and p^2(2p+1) != 0, two distinct residue signs in the same
        # class mod N cannot be interpolated by a single polynomial on infinitely many primes.
        signs_by_class = {}
        for p in primes_sample:
            if p < p0:
                continue
            r = p % N
            s = legendre_symbol(d, p)
            signs_by_class.setdefault(r, set()).add(s)
        return all(len(v) <= 1 for v in signs_by_class.values())

    # d = -1: minimal period must be 4 (!= 5)
    min_per_minus1 = next(N for N in range(1, 20) if has_porc_period(-1, N))
    assert min_per_minus1 == 4 and not has_porc_period(-1, 5)
    checks_run += 1
    print(f"  d = -1: minimal period = {min_per_minus1} (period 5 valid? {has_porc_period(-1, 5)})")

    for ell in [3, 5, 7, 11, 13]:
        d_ell = ell if ell % 4 == 1 else -ell
        min_per = next(N for N in range(1, 30) if has_porc_period(d_ell, N, p0=ell + 1))
        assert min_per == ell, f"Expected minimal period {ell} for d={d_ell}, got {min_per}"
        checks_run += 1
        print(f"  ell = {ell:2d} (d = {d_ell:3d}): minimal PORC period = {min_per:2d} while log_p |G| = 5")

    print("\n" + "=" * 72)
    print(f"ALL {checks_run} VERIFICATION CHECKS PASSED SUCCESSFULLY (EXIT 0).")
    print("=" * 72)


if __name__ == "__main__":
    main()
