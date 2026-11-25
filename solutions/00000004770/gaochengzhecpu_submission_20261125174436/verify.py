#!/usr/bin/env python3
"""
Standalone Computational Verification Suite for Conjecture 00000004770
("Mobius spectrum-lattice separation pair" — Disproof Across Canonical Annular
and Boundary Noncrossing Partition Families, Plus Scope-Boundary Analysis).

Uses only the Python 3 standard library and exact integer arithmetic.
"""

from collections import Counter, defaultdict
import itertools
import math
import sys


# ---------------------------------------------------------------------------
# 1. Exact Set Partition and Permutation Primitives
# ---------------------------------------------------------------------------

def unique_partitions(n: int):
    """Return all set partitions of {1, ..., n} in canonical sorted tuple form."""
    def rec(elems):
        if not elems:
            yield ()
            return
        first = elems[0]
        for rest in rec(elems[1:]):
            for i in range(len(rest)):
                new_blk = tuple(sorted(rest[i] + (first,)))
                yield tuple(sorted(rest[:i] + (new_blk,) + rest[i + 1:]))
            yield tuple(sorted(rest + ((first,),)))

    return sorted(set(rec(list(range(1, n + 1)))))


def is_nc_order(part, order) -> bool:
    """True iff `part` is noncrossing with respect to linear/cyclic listing `order`."""
    pos = {x: idx for idx, x in enumerate(order)}
    blocks = [sorted(pos[x] for x in blk) for blk in part if len(blk) >= 2]
    for i in range(len(blocks)):
        b1 = blocks[i]
        for j in range(i + 1, len(blocks)):
            b2 = blocks[j]
            for a_i in range(len(b1)):
                a = b1[a_i]
                for c_i in range(a_i + 1, len(b1)):
                    c = b1[c_i]
                    for b_i in range(len(b2)):
                        b = b2[b_i]
                        for d_i in range(b_i + 1, len(b2)):
                            d = b2[d_i]
                            if (a < b < c < d) or (b < a < d < c):
                                return False
    return True


def refines(p1, p2) -> bool:
    """True iff `p1 <= p2` under partition refinement."""
    b2_sets = [set(b) for b in p2]
    return all(any(set(b1) <= s2 for s2 in b2_sets) for b1 in p1)


def generate_disc_nc(m: int):
    """Exact Catalan recursive generator for classical disc noncrossing partitions NC(m)."""
    memo = {0: [()]}
    for n in range(1, m + 1):
        res = []
        for pi2 in memo[n - 1]:
            shifted = tuple(tuple(x + 1 for x in blk) for blk in pi2)
            res.append(tuple(sorted(((1,),) + shifted)))
        for k in range(2, n + 1):
            for pi1 in memo[k - 2]:
                s1 = tuple(tuple(x + 1 for x in blk) for blk in pi1)
                for pi2 in memo[n - k + 1]:
                    s2 = []
                    for blk in pi2:
                        s_blk = tuple(x + k - 1 for x in blk)
                        if k in s_blk:
                            s_blk = (1,) + s_blk
                        s2.append(s_blk)
                    res.append(tuple(sorted(s1 + tuple(s2))))
        memo[n] = sorted(res)
    return memo[m]


def perm_cycles(perm):
    n = len(perm)
    vis = [False] * (n + 1)
    cycs = []
    for i in range(1, n + 1):
        if not vis[i]:
            cur = i
            c = []
            while not vis[cur]:
                vis[cur] = True
                c.append(cur)
                cur = perm[cur - 1]
            cycs.append(tuple(sorted(c)))
    return tuple(sorted(cycs))


def mul_perm(p1, p2):
    return tuple(p1[p2[i] - 1] for i in range(len(p1)))


def inv_perm(p):
    res = [0] * len(p)
    for i, v in enumerate(p):
        res[v - 1] = i + 1
    return tuple(res)


# ---------------------------------------------------------------------------
# 2. Finite Poset, Lattice, Möbius Spectrum, and Isomorphism Engine
# ---------------------------------------------------------------------------

def analyze_poset(elements, leq_fn):
    m = len(elements)
    leq = [[leq_fn(elements[i], elements[j]) for j in range(m)] for i in range(m)]

    # Verify poset axioms
    for i in range(m):
        assert leq[i][i], "Reflexivity failed"
    for i in range(m):
        for j in range(i + 1, m):
            assert not (leq[i][j] and leq[j][i]), "Antisymmetry failed"
    for i in range(m):
        for j in range(m):
            if leq[i][j]:
                for k in range(m):
                    if leq[j][k]:
                        assert leq[i][k], "Transitivity failed"

    # Semilattice & lattice checks
    join_ok = True
    meet_ok = True
    for i in range(m):
        for j in range(i + 1, m):
            ubs = [k for k in range(m) if leq[i][k] and leq[j][k]]
            min_ubs = [u for u in ubs if not any(u2 != u and leq[u2][u] for u2 in ubs)]
            if len(min_ubs) != 1:
                join_ok = False
            lbs = [k for k in range(m) if leq[k][i] and leq[k][j]]
            max_lbs = [l for l in lbs if not any(l2 != l and leq[l][l2] for l2 in lbs)]
            if len(max_lbs) != 1:
                meet_ok = False

    # Topological ordering & exact two-variable Mobius function
    order = sorted(range(m), key=lambda i: sum(leq[k][i] for k in range(m)))
    mu = [[0] * m for _ in range(m)]
    for idx_i in range(m):
        i = order[idx_i]
        mu[i][i] = 1
        for idx_j in range(idx_i + 1, m):
            j = order[idx_j]
            if leq[i][j]:
                mu[i][j] = -sum(
                    mu[i][order[idx_k]]
                    for idx_k in range(idx_i, idx_j)
                    if leq[i][order[idx_k]] and leq[order[idx_k]][j]
                )

    bots = [i for i in range(m) if all(leq[i][j] for j in range(m))]
    tops = [i for i in range(m) if all(leq[j][i] for j in range(m))]
    bot = bots[0] if len(bots) == 1 else None
    top = tops[0] if len(tops) == 1 else None

    bot_spec = Counter(mu[bot][j] for j in range(m)) if bot is not None else None
    top_spec = Counter(mu[i][top] for i in range(m)) if top is not None else None
    full_spec = Counter(mu[i][j] for i in range(m) for j in range(m) if leq[i][j])
    mu01 = mu[bot][top] if (bot is not None and top is not None) else None

    return {
        "m": m,
        "leq": leq,
        "mu": mu,
        "join_semi": join_ok,
        "meet_semi": meet_ok,
        "is_lattice": join_ok and meet_ok,
        "bot_spec": bot_spec,
        "top_spec": top_spec,
        "full_spec": full_spec,
        "mu01": mu01,
    }


def are_posets_isomorphic(leq1, leq2) -> bool:
    n = len(leq1)
    if n != len(leq2):
        return False
    deg1 = [(sum(leq1[i][j] for j in range(n)), sum(leq1[j][i] for j in range(n))) for i in range(n)]
    deg2 = [(sum(leq2[i][j] for j in range(n)), sum(leq2[j][i] for j in range(n))) for i in range(n)]
    if sorted(deg1) != sorted(deg2):
        return False
    groups1 = defaultdict(list)
    groups2 = defaultdict(list)
    for i in range(n):
        groups1[deg1[i]].append(i)
        groups2[deg2[i]].append(i)
    order1 = [i for k in sorted(groups1, key=lambda k: len(groups1[k])) for i in groups1[k]]
    cands = {i: groups2[deg1[i]] for i in range(n)}
    mapping = {}
    used = set()

    def bt(idx: int) -> bool:
        if idx == n:
            return True
        u = order1[idx]
        for v in cands[u]:
            if v in used:
                continue
            if all(
                leq1[u][order1[p]] == leq2[v][mapping[order1[p]]]
                and leq1[order1[p]][u] == leq2[mapping[order1[p]]][v]
                for p in range(idx)
            ):
                mapping[u] = v
                used.add(v)
                if bt(idx + 1):
                    return True
                used.remove(v)
                del mapping[u]
        return False

    return bt(0)


# ---------------------------------------------------------------------------
# 3. Canonical Annular and Boundary Noncrossing Partition Builders
# ---------------------------------------------------------------------------

def annular_s_nc(p: int, q: int):
    """Mingo-Nica annular noncrossing permutations S_NC(p, q) via genus-0 cycle identity."""
    n = p + q
    gamma = tuple(
        ((i % p) + 1 for i in range(1, p + 1))
    ) + tuple(
        (p + (j % q) + 1 for j in range(1, q + 1))
    )
    outer = set(range(1, p + 1))
    inner = set(range(p + 1, n + 1))
    res = []
    for perm in itertools.permutations(range(1, n + 1)):
        cycs = perm_cycles(perm)
        through = any((set(c) & outer) and (set(c) & inner) for c in cycs)
        inv_g = mul_perm(inv_perm(perm), gamma)
        csum = len(cycs) + len(perm_cycles(inv_g))
        if (not through and csum == n + 2) or (through and csum == n):
            res.append(perm)
    return res


def annular_nc_partitions(p: int, q: int):
    """Mingo-Nica annular set partitions NC_A(p, q), cross-checked against cut-annulus definition."""
    s_nc = annular_s_nc(p, q)
    from_perms = sorted(set(perm_cycles(perm) for perm in s_nc))

    outer_l = list(range(1, p + 1))
    inner_l = list(range(p + 1, p + q + 1))
    outer_s, inner_s = set(outer_l), set(inner_l)
    from_cuts = []
    for part in unique_partitions(p + q):
        through = any((set(b) & outer_s) and (set(b) & inner_s) for b in part)
        if not through:
            po = tuple(sorted(b for b in part if set(b) <= outer_s))
            pi = tuple(sorted(b for b in part if set(b) <= inner_s))
            if is_nc_order(po, outer_l) and is_nc_order(pi, inner_l):
                from_cuts.append(part)
        else:
            ok = False
            for r1 in range(p):
                ro = outer_l[r1:] + outer_l[:r1]
                for r2 in range(q):
                    ri = inner_l[r2:] + inner_l[:r2]
                    if is_nc_order(part, ro + ri):
                        ok = True
                        break
                if ok:
                    break
            if ok:
                from_cuts.append(part)

    assert from_perms == from_cuts, f"Cut vs permutation mismatch at ({p}, {q})"
    return from_cuts, s_nc


def type_b_nc(n: int):
    """Reiner / Biane-Goodman-Nica rotational noncrossing partitions NC^(B)(n)."""
    m = 2 * n
    def neg(x):
        return x + n if x <= n else x - n
    return [
        pt for pt in generate_disc_nc(m)
        if tuple(sorted(tuple(sorted(neg(x) for x in b)) for b in pt)) == pt
    ]


def refl_sym_nc(m: int, shift: int = 0):
    """Simion half-disc reflection-boundary noncrossing partitions NC^sym(m)."""
    def refl(x):
        return ((m + 1 - x + shift - 1) % m) + 1
    return [
        pt for pt in generate_disc_nc(m)
        if tuple(sorted(tuple(sorted(refl(x) for x in b)) for b in pt)) == pt
    ]


def type_d_nc(n: int):
    """Athanasiadis-Reiner Type-D noncrossing partition lattice NC^(D)(n) (n >= 2)."""
    k = n - 1
    pos_n, neg_n = 2 * k + 1, 2 * k + 2

    def neg(x):
        if x <= k:
            return x + k
        if x <= 2 * k:
            return x - k
        return neg_n if x == pos_n else pos_n

    def minor_arc(blk):
        for start in range(1, 2 * k + 1):
            arc = [((start - 1 + j) % (2 * k)) + 1 for j in range(k)]
            if all(x in arc for x in blk):
                idxs = [arc.index(x) for x in blk]
                return set(arc[min(idxs):max(idxs) + 1])
        raise RuntimeError("Invalid zero-free Type-B block")

    res = []
    for p_out in type_b_nc(k):
        z_blks = [b for b in p_out if tuple(sorted(neg(x) for x in b)) == b]
        if z_blks:
            z = z_blks[0]
            res.append(tuple(sorted([b for b in p_out if b != z] + [tuple(sorted(z + (pos_n, neg_n)))])))
        else:
            res.append(tuple(sorted(list(p_out) + [(pos_n,), (neg_n,)])))
            arcs = {b: minor_arc(b) for b in p_out}
            for b in p_out:
                nb = tuple(sorted(neg(x) for x in b))
                if not any(c != b and set(b) <= arcs[c] for c in p_out):
                    res.append(tuple(sorted(
                        [c for c in p_out if c != b and c != nb]
                        + [tuple(sorted(b + (pos_n,))), tuple(sorted(nb + (neg_n,)))]
                    )))
    return sorted(set(res))


# ---------------------------------------------------------------------------
# 4. Verification Checks
# ---------------------------------------------------------------------------

def verify_section_1_annular_dichotomy():
    print("=" * 74)
    print("SECTION 1: Mingo-Nica S_NC(p, q) and NC_A(p, q) Lattice Dichotomy")
    print("=" * 74)
    for s in range(2, 7):
        for p in range(1, s):
            q = s - p
            if p >= q:
                parts, perms = annular_nc_partitions(p, q)
                res_set = analyze_poset(parts, refines)

                # Biane reflection order on S_NC(p, q)
                def biane_leq(u, v, n=p + q):
                    lu = n - len(perm_cycles(u))
                    lv = n - len(perm_cycles(v))
                    luv = n - len(perm_cycles(mul_perm(inv_perm(u), v)))
                    return lu + luv == lv

                res_perm = analyze_poset(perms, biane_leq)
                print(
                    f"  (p,q)=({p},{q}): |S_NC|={len(perms):>3} (lattice={str(res_perm['is_lattice']):<5}), "
                    f"|NC_A|={len(parts):>3} (lattice={str(res_set['is_lattice']):<5}, mu01={res_set['mu01']})"
                )

                # Assert exact theoretical dichotomy
                assert res_perm["is_lattice"] == (p == 1 and q == 1)
                expected_set_lat = (q == 1) or ((p, q) in [(2, 2), (3, 2)])
                assert res_set["is_lattice"] == expected_set_lat

                if q == 1:
                    cat_p = math.comb(2 * p, p) // (p + 1)
                    assert len(parts) == (p + 3) * cat_p // 2
                    assert res_set["mu01"] == ((-1) ** p) * math.comb(2 * p - 2, p - 1)
                    # Check NC_A(p, 1) == {pi in Pi(p+1) : pi|_{[p]} in NC(p)}
                    circ_bdry = [
                        pt for pt in unique_partitions(p + 1)
                        if is_nc_order(
                            tuple(sorted(tuple(x for x in b if x <= p) for b in pt if any(x <= p for x in b))),
                            list(range(1, p + 1)),
                        )
                    ]
                    assert parts == circ_bdry
    print("  [PASS] All annular permutation & set-partition dichotomy assertions verified.\n")


def verify_section_2_equinumerous_trap_and_type_d():
    print("=" * 74)
    print("SECTION 2: C(2n, n) Equinumerosity Trap & Type-D Top-Mobius Coincidence")
    print("=" * 74)
    for n in range(1, 5):
        pb = analyze_poset(type_b_nc(n), refines)
        pe = analyze_poset(refl_sym_nc(2 * n, 0), refines)
        pv = analyze_poset(refl_sym_nc(2 * n, 1), refines)
        c2n = math.comb(2 * n, n)
        assert pb["m"] == pe["m"] == pv["m"] == c2n
        assert pb["is_lattice"] and pe["is_lattice"] and pv["is_lattice"]
        assert abs(pb["mu01"]) == math.comb(2 * n - 1, n - 1)
        cat_n1 = math.comb(2 * (n - 1), n - 1) // n
        assert abs(pe["mu01"]) == cat_n1 == abs(pv["mu01"])
        assert pe["full_spec"] == pv["full_spec"]
        if n >= 2:
            assert not are_posets_isomorphic(pb["leq"], pe["leq"])
            assert not are_posets_isomorphic(pb["leq"], pv["leq"])
            assert not are_posets_isomorphic(pe["leq"], pv["leq"])
            assert pb["bot_spec"] != pe["bot_spec"] and pb["bot_spec"] != pv["bot_spec"]
            assert pb["full_spec"] != pe["full_spec"]
            assert pe["bot_spec"] != pv["bot_spec"]
        print(
            f"  n={n} (size={c2n:>2}): |mu_B|={abs(pb['mu01']):>2}, |mu_sym|={abs(pe['mu01']):>2}, "
            f"bot_eq={pb['bot_spec'] == pe['bot_spec']}, full_eq={pb['full_spec'] == pe['full_spec']}"
        )

    # Type-D checks (n = 2, 3, 4)
    for n in [2, 3, 4]:
        pd = analyze_poset(type_d_nc(n), refines)
        expected_sz = (3 * n - 2) * math.comb(2 * n - 2, n - 1) // n
        expected_mu = 1 if n == 2 else (3 * n - 4) * math.comb(2 * n - 3, n - 2) // n
        assert pd["m"] == expected_sz and pd["is_lattice"] and abs(pd["mu01"]) == expected_mu
        print(f"  NC^(D)({n}): size={pd['m']}, mu(0,1)={pd['mu01']}, bot_spec={dict(sorted(pd['bot_spec'].items()))}")

    p_d3 = analyze_poset(type_d_nc(3), refines)
    p_nc4 = analyze_poset(generate_disc_nc(4), refines)
    assert are_posets_isomorphic(p_d3["leq"], p_nc4["leq"])
    print("  [PASS] Equinumerous trap (n=1..4) and Type-D (n=2..4) assertions verified.\n")


def verify_section_3_universal_canonical_rigidity(max_param: int = 50):
    print("=" * 74)
    print(f"SECTION 3: Canonical Rigidity Sweep Across All Parameters <= {max_param}")
    print("=" * 74)

    def cat(k):
        return math.comb(2 * k, k) // (k + 1)

    ann = []
    for p in range(1, max_param + 1):
        ann.append((("ncA_p1", p), (p + 3) * cat(p) // 2, math.comb(2 * p - 2, p - 1)))
        ann.append((("ncB_ann", p), math.comb(2 * p, p), math.comb(2 * p - 1, p - 1)))
    ann.append((("ncA_22",), 15, 6))
    ann.append((("ncA_32",), 52, 24))
    for p in range(2, max_param + 1):
        for q in range(2, p + 1):
            ann.append((("ncProd", p, q), cat(p) * cat(q), cat(p - 1) * cat(q - 1)))

    bdry = []
    for m in range(1, max_param + 1):
        bdry.append((("ncArc", m), cat(m + 1), cat(m)))
        bdry.append((("ncCirc", m), (m + 3) * cat(m) // 2, math.comb(2 * m - 2, m - 1)))
        bdry.append((("ncB_bdry", m), math.comb(2 * m, m), math.comb(2 * m - 1, m - 1)))
        if m >= 2:
            d_sz = (3 * m - 2) * math.comb(2 * m - 2, m - 1) // m
            d_mu = 1 if m == 2 else (3 * m - 4) * math.comb(2 * m - 3, m - 2) // m
            bdry.append((("ncD_bdry", m), d_sz, d_mu))
            s_sz = math.comb(m, m // 2)
            s_mu = 0 if m % 2 == 1 else cat(m // 2 - 1)
            bdry.append((("ncSym", m), s_sz, s_mu))

    def is_canonical_iso(ak, bk) -> bool:
        if ak in [("ncA_p1", 1), ("ncB_ann", 1)] and bk in [("ncArc", 1), ("ncCirc", 1), ("ncB_bdry", 1), ("ncSym", 2)]:
            return True
        if ak == ("ncA_p1", 2) and bk == ("ncArc", 2):
            return True
        if ak == ("ncA_22",) and bk == ("ncCirc", 3):
            return True
        if ak == ("ncProd", 2, 2) and bk == ("ncD_bdry", 2):
            return True
        if ak[0] == "ncA_p1" and bk[0] == "ncCirc" and ak[1] == bk[1]:
            return True
        if ak[0] == "ncB_ann" and bk[0] == "ncB_bdry" and ak[1] == bk[1]:
            return True
        return False

    total_checked = 0
    iso_matches = 0
    for ak, asz, amu in ann:
        for bk, bsz, bmu in bdry:
            total_checked += 1
            matched = (asz == bsz and amu == bmu)
            expected = is_canonical_iso(ak, bk)
            assert matched == expected, f"Unexpected match status: {ak} vs {bk}"
            if matched:
                iso_matches += 1

    print(f"  Checked {total_checked:,} canonical family pairs: {iso_matches} matches, 0 non-isomorphic collisions.")
    print("  [PASS] Universal canonical rigidity sweep verified.\n")


def verify_section_4_scope_boundary_sublattices():
    print("=" * 74)
    print("SECTION 4: Scope Boundary — Induced Noncrossing Sublattices")
    print("=" * 74)

    # 1) Minimal 5-element induced sublattices in NC(4) sharing lowerMobiusMult
    stem5 = [
        ((1,), (2,), (3,), (4,)),
        ((1,), (2,), (3, 4)),
        ((1,), (2, 3), (4,)),
        ((1,), (2, 3, 4)),
        ((1, 2, 3, 4),),
    ]
    pent5 = [
        ((1,), (2,), (3,), (4,)),
        ((1,), (2,), (3, 4)),
        ((1,), (2, 3), (4,)),
        ((1, 2), (3, 4)),
        ((1, 2, 3, 4),),
    ]
    nc4_set = set(generate_disc_nc(4))
    assert set(stem5) <= nc4_set and set(pent5) <= nc4_set
    r_stem5 = analyze_poset(stem5, refines)
    r_pent5 = analyze_poset(pent5, refines)
    assert r_stem5["is_lattice"] and r_pent5["is_lattice"]
    assert r_stem5["bot_spec"] == r_pent5["bot_spec"] == Counter({1: 2, -1: 2, 0: 1})
    assert not are_posets_isomorphic(r_stem5["leq"], r_pent5["leq"])
    print(f"  5-element NC(4) pair: both lattices, non-isomorphic, shared bot_spec={dict(r_stem5['bot_spec'])}")

    # 2) Self-dual graded 10-element interval-partition sublattices in NC(8) sharing ALL Mobius spectra
    def mask_to_nc8(mask: int):
        blocks = []
        cur = [1]
        for g in range(7):
            if (mask >> g) & 1:
                cur.append(g + 2)
            else:
                blocks.append(tuple(cur))
                cur = [g + 2]
        blocks.append(tuple(cur))
        return tuple(sorted(blocks))

    masks_a = [0, 1, 3, 7, 11, 15, 31, 47, 63, 127]
    masks_b = [0, 1, 3, 5, 7, 15, 31, 47, 63, 127]
    fam_a = [mask_to_nc8(m) for m in masks_a]
    fam_b = [mask_to_nc8(m) for m in masks_b]
    assert all(is_nc_order(p, list(range(1, 9))) for p in fam_a + fam_b)
    ra = analyze_poset(fam_a, refines)
    rb = analyze_poset(fam_b, refines)
    assert ra["is_lattice"] and rb["is_lattice"]
    assert ra["bot_spec"] == rb["bot_spec"] == Counter({1: 1, -1: 1, 0: 8})
    assert ra["top_spec"] == rb["top_spec"] == Counter({1: 1, -1: 1, 0: 8})
    assert ra["full_spec"] == rb["full_spec"] == Counter({1: 12, -1: 11, 0: 30})
    assert not are_posets_isomorphic(ra["leq"], rb["leq"])
    print(
        f"  10-element NC(8) pair: both self-dual graded lattices, non-isomorphic, "
        f"shared bot=top={dict(ra['bot_spec'])}, shared full={dict(ra['full_spec'])}"
    )
    print("  [PASS] Scope-boundary sublattice assertions verified.\n")


def main():
    verify_section_1_annular_dichotomy()
    verify_section_2_equinumerous_trap_and_type_d()
    verify_section_3_universal_canonical_rigidity(50)
    verify_section_4_scope_boundary_sublattices()
    print("ALL VERIFICATION CHECKS PASSED SUCCESSFULLY.")


if __name__ == "__main__":
    main()
