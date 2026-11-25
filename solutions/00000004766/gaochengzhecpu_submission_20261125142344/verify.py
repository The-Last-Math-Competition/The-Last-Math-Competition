#!/usr/bin/env python3
"""
Standalone symbolic and combinatorial verification for Conjecture 00000004766:
"Two-dimensional noncrossing is the joint structure of two noncrossing conditions.
 Conjecture: Its low-dimensional counts are explicit two-dimensional Narayana-type
 polynomials, given by symmetric combinations of the two-dimensional parameters and closed."

Uses Python 3.12 standard library only.
Verifies:
  1. Classical 1D Narayana baseline and small-order / boundary mirages (m=1 or n=1 on grids,
     n <= 3 on 2D posets and coupled noncrossing pairs, CNS word-invariance on bi-free BNC).
  2. Reading I — Cartesian Grid [m] x [n] Joint Noncrossing:
     - Bi-lexicographic NC(<_row) cap NC(<_col): non-palindromic polynomials on (2,2), (2,3),
       (2,4), (3,3), and universal 2-block formula c_2(m, n) = m*n + 1 for all 2 <= m, n <= 7
       versus c_2(1, n) = C(n, 2), proving algebraic non-polynomiality in Q[m, n].
     - Slice-wise, coordinate-projection, and planar convex-hull noncrossing variants on [m] x [n].
  3. Reading II — Bi-Ordered / 2D Poset Joint Noncrossing NC(id) cap NC(sigma):
     - Exact spectrum across S_3, S_4, S_5: order-dependence and non-palindromicity at n = 4, 5.
  4. Reading III — Voiculescu's Bi-Free BNC(chi) & Untwisted Two-Channel NC_2(chi):
     - CNS word-invariance on BNC(chi), failure of (u, v)-symmetry for m != n, failure of
       Narayana biduality at m = n = 2, and word-order dependence (LLRR vs LRLR) on NC_2(chi).
  5. Reading IV — Coupled Pairs (pi_1, pi_2) in NC(n) x NC(n):
     - Join-compatibility pi_1 vee pi_2 in NC(n), mutual block noncrossing, refinement 2-chains
       pi_1 <= pi_2, and bicolored circle interleaving pi sqcup sigma in NC(chi).
"""

import itertools
from collections import defaultdict
from fractions import Fraction
from math import comb


def set_partitions(n: int):
    """Yield all set partitions of {0, ..., n-1} as tuples of frozensets."""
    if n == 0:
        yield ()
        return
    for p in set_partitions(n - 1):
        for i in range(len(p)):
            yield p[:i] + (p[i] | {n - 1},) + p[i + 1 :]
        yield p + (frozenset({n - 1}),)


def is_nc_in_order(part, order) -> bool:
    """Return True iff partition `part` has no crossing a < b < c < d along `order`."""
    block_of = {}
    for b_idx, blk in enumerate(part):
        for x in blk:
            block_of[x] = b_idx
    seq = [block_of[x] for x in order]
    m = len(seq)
    for a in range(m):
        ba = seq[a]
        for b in range(a + 1, m):
            bb = seq[b]
            if ba == bb:
                continue
            for c in range(b + 1, m):
                if seq[c] != ba:
                    continue
                for d in range(c + 1, m):
                    if seq[d] == bb:
                        return False
    return True


def narayana_1d(n: int, k: int) -> int:
    if n <= 0 or k <= 0 or k > n:
        return 0
    return (comb(n, k) * comb(n, k - 1)) // n


def narayana_poly_1d(n: int) -> dict[int, int]:
    return {k: narayana_1d(n, k) for k in range(1, n + 1)}


def is_palindromic_1d(counts: dict[int, int], n: int) -> bool:
    return all(counts.get(k, 0) == counts.get(n + 1 - k, 0) for k in range(1, n + 1))


def is_symmetric_2d(counts: dict[tuple[int, int], int], max_deg: int) -> bool:
    return all(
        counts.get((i, j), 0) == counts.get((j, i), 0)
        for i in range(max_deg + 1)
        for j in range(max_deg + 1)
    )


def is_bidual_2d(counts: dict[tuple[int, int], int], n: int) -> bool:
    return all(
        counts.get((i, j), 0) == counts.get((n + 1 - i, n + 1 - j), 0)
        for i in range(1, n + 1)
        for j in range(1, n + 1)
    )


def fmt_poly_1d(counts: dict[int, int]) -> str:
    return " + ".join(f"{c}*t^{k}" for k, c in sorted(counts.items()) if c != 0)


def fmt_poly_2d(counts: dict[tuple[int, int], int]) -> str:
    return " + ".join(
        f"{c}*u^{i}*v^{j}" for (i, j), c in sorted(counts.items()) if c != 0
    )


def verify_reading_1_grid() -> None:
    print("======================================================================")
    print("READING I: Cartesian Grid [m] x [n] Joint Noncrossing")
    print("======================================================================")

    # 1A. Full block-enumerator polynomials of NC(<_row) cap NC(<_col)
    expected_grid = {
        (1, 4): {1: 1, 2: 6, 3: 6, 4: 1},
        (2, 2): {1: 1, 2: 5, 3: 6, 4: 1},
        (2, 3): {1: 1, 2: 7, 3: 26, 4: 38, 5: 15, 6: 1},
        (3, 2): {1: 1, 2: 7, 3: 26, 4: 38, 5: 15, 6: 1},
        (2, 4): {1: 1, 2: 9, 3: 43, 4: 138, 5: 230, 6: 146, 7: 28, 8: 1},
        (3, 3): {1: 1, 2: 10, 3: 43, 4: 147, 5: 368, 6: 480, 7: 243, 8: 36, 9: 1},
    }
    for (m, n), exp in expected_grid.items():
        N = m * n
        row_ord = tuple(range(N))
        col_ord = tuple(i * n + j for j in range(n) for i in range(m))
        counts: dict[int, int] = defaultdict(int)
        for p in set_partitions(N):
            if is_nc_in_order(p, row_ord) and is_nc_in_order(p, col_ord):
                counts[len(p)] += 1
        assert dict(counts) == exp, f"Grid ({m},{n}) mismatch: {dict(counts)} != {exp}"
        pal = is_palindromic_1d(counts, N)
        print(
            f"  [PASS] NC_2({m},{n}) (N={N}): total={sum(counts.values())}, "
            f"palindromic={pal}, P(t) = {fmt_poly_1d(counts)}"
        )
        if m >= 2 and n >= 2:
            assert not pal, f"Expected non-palindromic polynomial at ({m},{n})"

    # 1B. Universal 2-block classification c_2(m, n) = m*n + 1 for all 2 <= m, n <= 7
    # vs c_2(1, n) = C(n, 2) and c_2(m, 1) = C(m, 2)
    def count_c2(m: int, n: int) -> int:
        N = m * n
        if N < 2:
            return 0
        row_ord = list(range(N))
        col_ord = [i * n + j for j in range(n) for i in range(m)]

        def cyclic_intervals(ord_list):
            res = set()
            for l in range(N):
                for r in range(l, N):
                    if r - l + 1 == N:
                        continue
                    A = frozenset(ord_list[l : r + 1])
                    B = frozenset(ord_list) - A
                    res.add(frozenset({A, B}))
            return res

        return len(cyclic_intervals(row_ord) & cyclic_intervals(col_ord))

    for m in range(1, 8):
        for n in range(1, 8):
            val = count_c2(m, n)
            if m == 1:
                assert val == comb(n, 2)
            elif n == 1:
                assert val == comb(m, 2)
            else:
                assert val == m * n + 1, f"c_2({m},{n}) = {val} != {m*n+1}"
    print(
        "  [PASS] Universal 2-block formula verified for all 1 <= m, n <= 7: "
        "c_2(1, n) = C(n, 2), c_2(m, 1) = C(m, 2), and c_2(m, n) = m*n + 1 for m, n >= 2."
    )

    # Confirm Lagrange interpolation obstruction at m = 2:
    # Any polynomial Q(2, y) matching 2y + 1 at y = 2, 3, ..., deg+2 evaluates to 3 at y = 1 != 1 = c_2(2,1)
    assert Fraction(2 * 1 + 1) != Fraction(count_c2(2, 1))
    print(
        f"  [PASS] Algebraic non-polynomiality obstruction at m=2: "
        f"linear continuation gives 2(1)+1 = 3 != {count_c2(2, 1)} = c_2(2, 1)."
    )

    # 1C. Slice-wise & planar convex-hull grid variants
    def orient(a, b, c):
        return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])

    def on_seg(a, b, p):
        return (
            orient(a, b, p) == 0
            and min(a[0], b[0]) <= p[0] <= max(a[0], b[0])
            and min(a[1], b[1]) <= p[1] <= max(a[1], b[1])
        )

    def segs_intersect(a, b, c, d):
        o1, o2 = orient(a, b, c), orient(a, b, d)
        o3, o4 = orient(c, d, a), orient(c, d, b)
        if (o1 * o2 < 0) and (o3 * o4 < 0):
            return True
        return on_seg(a, b, c) or on_seg(a, b, d) or on_seg(c, d, a) or on_seg(c, d, b)

    def pt_in_tri(p, a, b, c):
        o1, o2, o3 = orient(a, b, p), orient(b, c, p), orient(c, a, p)
        return not ((o1 < 0 or o2 < 0 or o3 < 0) and (o1 > 0 or o2 > 0 or o3 > 0))

    def hulls_disjoint(S1, S2):
        L1, L2 = list(S1), list(S2)
        for i in range(len(L1)):
            for j in range(i, len(L1)):
                for k in range(len(L2)):
                    for l in range(k, len(L2)):
                        if i == j and k == l:
                            if L1[i] == L2[k]:
                                return False
                        elif i == j:
                            if on_seg(L2[k], L2[l], L1[i]):
                                return False
                        elif k == l:
                            if on_seg(L1[i], L1[j], L2[k]):
                                return False
                        elif segs_intersect(L1[i], L1[j], L2[k], L2[l]):
                            return False
        for p in L1:
            for a, b, c in itertools.combinations(L2, 3):
                if orient(a, b, c) != 0 and pt_in_tri(p, a, b, c):
                    return False
        for p in L2:
            for a, b, c in itertools.combinations(L1, 3):
                if orient(a, b, c) != 0 and pt_in_tri(p, a, b, c):
                    return False
        return True

    pts_33 = [(i, j) for i in range(3) for j in range(3)]
    conv_33: dict[int, int] = defaultdict(int)
    for p in set_partitions(9):
        blks = [[pts_33[x] for x in blk] for blk in p]
        if all(
            hulls_disjoint(blks[u], blks[v])
            for u in range(len(blks))
            for v in range(u + 1, len(blks))
        ):
            conv_33[len(p)] += 1
    assert sum(conv_33.values()) == 2915
    assert conv_33[3] == 226 and conv_33[7] == 222
    assert conv_33[4] == 708 and conv_33[6] == 692
    assert not is_palindromic_1d(conv_33, 9)
    print(
        f"  [PASS] Planar convex-hull NC on [3]x[3]: total=2915, "
        f"c_3=226 != 222=c_7, c_4=708 != 692=c_6 (non-palindromic)."
    )


def verify_reading_2_poset() -> None:
    print("\n======================================================================")
    print("READING II: Bi-Ordered / 2D Poset Joint Noncrossing NC(id) cap NC(sigma)")
    print("======================================================================")
    for n, expected_totals in [(3, [5]), (4, [13, 14]), (5, [32, 35, 37, 42])]:
        id_ord = tuple(range(n))
        nc_id = [p for p in set_partitions(n) if is_nc_in_order(p, id_ord)]
        spectrum = {}
        for sigma in itertools.permutations(range(n)):
            cnt: dict[int, int] = defaultdict(int)
            for p in nc_id:
                if is_nc_in_order(p, sigma):
                    cnt[len(p)] += 1
            key = tuple((k, cnt[k]) for k in range(1, n + 1))
            spectrum.setdefault(key, sigma)
        totals = sorted(sum(c for _, c in key) for key in spectrum)
        assert totals == expected_totals, f"S_{n} totals {totals} != {expected_totals}"
        print(f"  [PASS] n={n}: {len(spectrum)} distinct polynomials across S_{n}, totals={totals}")
        for key in sorted(spectrum, key=lambda kv: sum(c for _, c in kv)):
            d = dict(key)
            print(
                f"         total={sum(d.values()):2d}, palindromic={str(is_palindromic_1d(d, n)):5s}: "
                f"{fmt_poly_1d(d)}  (witness sigma={spectrum[key]})"
            )


def verify_reading_3_bifree() -> None:
    print("\n======================================================================")
    print("READING III: Voiculescu's Bi-Free BNC(chi) & Untwisted 2-Channel NC_2(chi)")
    print("======================================================================")

    def compute_channel_polys(chi: str):
        N = len(chi)
        L_idx = [i for i, c in enumerate(chi) if c == "L"]
        R_idx = [i for i, c in enumerate(chi) if c == "R"]
        s_chi = tuple(L_idx + list(reversed(R_idx)))
        std_ord = tuple(range(N))
        res = {}
        for tag, ord_seq in [("BNC", s_chi), ("Untwisted", std_ord)]:
            c_uv: dict[tuple[int, int], int] = defaultdict(int)
            for p in set_partitions(N):
                if is_nc_in_order(p, ord_seq):
                    bL = sum(1 for blk in p if any(x in L_idx for x in blk))
                    bR = sum(1 for blk in p if any(x in R_idx for x in blk))
                    c_uv[(bL, bR)] += 1
            res[tag] = dict(c_uv)
        return res

    r_llr = compute_channel_polys("LLR")
    assert r_llr["BNC"] == {(1, 1): 2, (2, 1): 3}
    assert not is_symmetric_2d(r_llr["BNC"], 3)
    print(
        f"  [PASS] BNC(LLR) (m=2, n=1): P(u,v) = {fmt_poly_2d(r_llr['BNC'])} "
        f"(asymmetric in u,v: [u^2 v]=3 != 0=[u v^2])."
    )

    r_llrr = compute_channel_polys("LLRR")
    r_lrlr = compute_channel_polys("LRLR")
    r_lrrl = compute_channel_polys("LRRL")
    assert r_llrr["BNC"] == r_lrlr["BNC"] == r_lrrl["BNC"] == {
        (1, 1): 2,
        (1, 2): 3,
        (2, 1): 3,
        (2, 2): 6,
    }
    assert not is_bidual_2d(r_llrr["BNC"], 2)
    print(
        f"  [PASS] CNS word-invariance on BNC at (2,2): P = {fmt_poly_2d(r_llrr['BNC'])}, "
        f"but fails Narayana biduality ([u v]=2 != 6=[u^2 v^2])."
    )

    assert r_llrr["Untwisted"] == {(1, 1): 2, (1, 2): 3, (2, 1): 3, (2, 2): 6}
    assert r_lrlr["Untwisted"] == {(1, 1): 1, (1, 2): 3, (2, 1): 3, (2, 2): 7}
    assert r_llrr["Untwisted"] != r_lrlr["Untwisted"]
    print(
        f"  [PASS] Untwisted 2-channel NC_2(chi) word-dependence at m=n=2:\n"
        f"         chi=LLRR -> {fmt_poly_2d(r_llrr['Untwisted'])}\n"
        f"         chi=LRLR -> {fmt_poly_2d(r_lrlr['Untwisted'])}"
    )


def verify_reading_4_coupled_pairs() -> None:
    print("\n======================================================================")
    print("READING IV: Coupled Pairs (pi_1, pi_2) in NC(n) x NC(n)")
    print("======================================================================")

    def join_part(p1, p2, n: int):
        parent = list(range(n))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for blk in list(p1) + list(p2):
            it = iter(blk)
            first = next(it)
            for x in it:
                ra, rb = find(first), find(x)
                if ra != rb:
                    parent[ra] = rb
        groups = defaultdict(set)
        for x in range(n):
            groups[find(x)].add(x)
        return tuple(frozenset(g) for g in groups.values())

    def blocks_cross(b1, b2) -> bool:
        for X, Y in [(b1, b2), (b2, b1)]:
            for a in X:
                for b in Y:
                    if not (a < b):
                        continue
                    for c in X:
                        if not (b < c):
                            continue
                        for d in Y:
                            if c < d:
                                return True
        return False

    for n in range(1, 6):
        ord_n = tuple(range(n))
        nc_n = [p for p in set_partitions(n) if is_nc_in_order(p, ord_n)]
        nc_set = {frozenset(p) for p in nc_n}
        inter_ord = tuple(range(2 * n))

        c_join: dict[tuple[int, int], int] = defaultdict(int)
        c_mut: dict[tuple[int, int], int] = defaultdict(int)
        c_chain: dict[tuple[int, int], int] = defaultdict(int)
        c_inter: dict[tuple[int, int], int] = defaultdict(int)

        for p1 in nc_n:
            for p2 in nc_n:
                k1, k2 = len(p1), len(p2)
                if frozenset(join_part(p1, p2, n)) in nc_set:
                    c_join[(k1, k2)] += 1
                if not any(blocks_cross(b1, b2) for b1 in p1 for b2 in p2):
                    c_mut[(k1, k2)] += 1
                if all(any(b1 <= b2 for b2 in p2) for b1 in p1):
                    c_chain[(k1, k2)] += 1
                p_inter = tuple(frozenset(2 * x for x in b) for b in p1) + tuple(
                    frozenset(2 * x + 1 for x in b) for b in p2
                )
                if is_nc_in_order(p_inter, inter_ord):
                    c_inter[(k1, k2)] += 1

        nar_prod = {
            (i, j): narayana_1d(n, i) * narayana_1d(n, j)
            for i in range(1, n + 1)
            for j in range(1, n + 1)
        }
        if n <= 3:
            assert dict(c_join) == nar_prod
            assert dict(c_mut) == nar_prod
            print(
                f"  [PASS] Mirage n={n}: Join-NC and Mutual-NC both equal symmetric Narayana "
                f"product N_{n}(u)*N_{n}(v) (total={sum(c_join.values())})."
            )
        elif n == 4:
            assert sum(c_join.values()) == 194
            assert c_join[(2, 2)] == 36 and c_join[(3, 3)] == 34
            assert not is_bidual_2d(c_join, 4)
            assert sum(c_mut.values()) == 165
            assert c_mut[(1, 1)] == 0 and c_mut[(4, 4)] == 1
            assert not is_bidual_2d(c_mut, 4)
            print(
                f"  [PASS] Disproof n=4: Join-NC total=194 (!= 196), [u^3 v^3]=34 != 36=[u^2 v^2]; "
                f"Mutual-NC total=165, [u v]=0 != 1=[u^4 v^4]."
            )
        elif n == 5:
            assert sum(c_join.values()) == 1714  # 2 * 857 (857 prime)
            assert sum(c_mut.values()) == 1168
            print(
                f"  [PASS] Disproof n=5: Join-NC total=1714 (= 2 * 857, != 42^2 = 1764); "
                f"Mutual-NC total=1168."
            )

        if n == 2:
            assert not is_symmetric_2d(c_chain, 2)
            assert c_chain[(2, 1)] == 1 and c_chain.get((1, 2), 0) == 0
            assert not is_bidual_2d(c_inter, 2)
            assert c_inter.get((1, 1), 0) == 0 and c_inter[(2, 2)] == 1
            print(
                f"  [PASS] Disproof n=2: 2-chain pi_1<=pi_2 polynomial {fmt_poly_2d(c_chain)} "
                f"is asymmetric in (u,v); Kreweras interleaved {fmt_poly_2d(c_inter)} fails biduality."
            )

        # Verify Edelman-Kreweras formula on interleaved circle for all n=1..5
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                c = i + j - n - 1
                ek = (
                    (comb(n, n - i) * comb(n, n - j) * comb(n, c)) // n
                    if 0 <= c <= n
                    else 0
                )
                assert c_inter.get((i, j), 0) == ek


def main() -> None:
    verify_reading_1_grid()
    verify_reading_2_poset()
    verify_reading_3_bifree()
    verify_reading_4_coupled_pairs()
    print("\n======================================================================")
    print("ALL VERIFICATION CHECKS PASSED: CONJECTURE 00000004766 IS FALSE.")
    print("======================================================================")


if __name__ == "__main__":
    main()
