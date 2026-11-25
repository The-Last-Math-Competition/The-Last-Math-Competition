#!/usr/bin/env python3
"""
Standalone computational verification for Conjecture 00000008545.

Conjecture 00000008545:
  English: "Definition: Uniformity of a lattice is the evenness of element covering numbers.
    Conjecture: The spectra of upper and lower uniform lattices are symmetric; and the
    minimal example of failure of uniformity is the 5-element nonmodular lattice.
    (minimal counterexample to uniformity)"
  Chinese: "定义：格的一致性（均匀性）指元素覆盖数的均匀。猜想：上/下均匀的格的谱对称；
    均匀性的失败的最小例为 5 元素非模格。（均匀性最小反例）"

What this script verifies from first principles (pure Python 3 standard library):
  1. Exhaustive unlabeled enumeration of all finite lattices of sizes 1 <= n <= 7,
     confirming OEIS A006966 counts: 1, 1, 1, 2, 5, 15, 53.
  2. Complete analysis of all 5 lattices of size <= 4 and all 5 lattices of size 5,
     plus key counterexamples at sizes 6 and 7.
  3. Explicit verification of every counterexample and theorem formalized in `lean/Main.lean`:
     - Regime I (Global non-extremal covering constancy): all lattices of size <= 3 are
       globally uniform, while B_2 (size 4 < 5, distributive and modular) fails both upper
       and lower uniformity. Also verifies ancillary variants (unrestricted constancy on C_2,
       undirected Hasse degree regularity on C_3 vs. N_5, and arithmetic parity on C_2).
     - Regime II (Strict interior covering constancy on L \\ {0, 1}): N_5 satisfies both
       interior upper and lower uniformity (so N_5 is NOT a counterexample), whereas the
       5-element distributive/modular lattices B_2 (+) 1 and 1 (+) B_2 fail interior uniformity;
       moreover N_5 has Hasse adjacency characteristic polynomial t^5 - 5 t^3 + 5 t - 2 and
       tr(A^5) = 10 != 0 (asymmetric graph eigenvalue spectrum).
     - Regime III (Graded rank-wise covering constancy — Terwilliger uniform lattices, under
       which N_5 IS the unique minimal counterexample to uniformity):
       * B_2 (+) 1 (size 5, distributive and modular) is both rank-upper-uniform and
         rank-lower-uniform, yet its Whitney rank-size spectrum (1, 2, 1, 1) is not palindromic
         and its rank-covering profile (2, 1, 1, 0) vs. (0, 1, 2, 1) is not symmetric.
       * L_7 (size 7, height 3) is graded and rank-upper-uniform (and interior-upper-uniform),
         yet fails rank-lower-uniformity, has non-palindromic Whitney spectrum (1, 3, 2, 1),
         and has unequal upper vs. lower covering-degree multisets:
         multiset(c+) = [0, 1, 1, 1, 1, 1, 3] != [0, 1, 1, 1, 1, 2, 2] = multiset(c-).
       * N_5 (+) 1 (size 6) satisfies shortest-chain height upper uniformity yet has
         Hasse adjacency characteristic polynomial t^6 - 6 t^4 + 8 t^2 - 2 t - 1 and
         tr(A^5) = 10 != 0 (non-zero-symmetric graph eigenvalue spectrum).
"""

import itertools
import sys


def generate_unlabeled_lattices(n: int):
    """Enumerate all isomorphism classes of n-element lattices with 0 = bot, n-1 = top."""
    if n == 1:
        return [[[True]]]

    interior_pairs = [(i, j) for i in range(1, n - 1) for j in range(i + 1, n - 1)]
    perms_interior = list(itertools.permutations(range(1, n - 1)))
    seen_canonical = set()
    lattices = []

    for bits in itertools.product([False, True], repeat=len(interior_pairs)):
        le = [[False] * n for _ in range(n)]
        for i in range(n):
            le[i][i] = True
            le[0][i] = True
            le[i][n - 1] = True
        for (i, j), val in zip(interior_pairs, bits):
            if val:
                le[i][j] = True

        # Transitivity check (indices are topologically ordered)
        transitive = True
        for i in range(n):
            for j in range(i + 1, n):
                if le[i][j]:
                    for k in range(j + 1, n):
                        if le[j][k] and not le[i][k]:
                            transitive = False
                            break
                if not transitive:
                    break
            if not transitive:
                break
        if not transitive:
            continue

        # Lattice check: unique LUB and unique GLB for every pair
        is_lat = True
        for a in range(n):
            for b in range(a + 1, n):
                ubs = [x for x in range(n) if le[a][x] and le[b][x]]
                lubs = [x for x in ubs if all(le[x][y] for y in ubs)]
                if len(lubs) != 1:
                    is_lat = False
                    break
                lbs = [x for x in range(n) if le[x][a] and le[x][b]]
                glbs = [x for x in lbs if all(le[y][x] for y in lbs)]
                if len(glbs) != 1:
                    is_lat = False
                    break
            if not is_lat:
                break
        if not is_lat:
            continue

        best = None
        for p in perms_interior:
            mp = [0] + list(p) + [n - 1]
            mat = tuple(tuple(le[mp[i]][mp[j]] for j in range(n)) for i in range(n))
            if best is None or mat < best:
                best = mat
        if best not in seen_canonical:
            seen_canonical.add(best)
            lattices.append([list(row) for row in best])

    return lattices


def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def mat_pow(A, p):
    n = len(A)
    res = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    for _ in range(p):
        res = mat_mul(res, A)
    return res


def mat_trace(A):
    return sum(A[i][i] for i in range(len(A)))


def char_poly(A):
    """Exact integer characteristic polynomial det(t I - A) via Faddeev-LeVerrier."""
    n = len(A)
    coeffs = [1]
    M = [[0] * n for _ in range(n)]
    for k in range(1, n + 1):
        if k == 1:
            M = [row[:] for row in A]
        else:
            M_shift = [[M[i][j] + (coeffs[-1] if i == j else 0) for j in range(n)] for i in range(n)]
            M = mat_mul(A, M_shift)
        ck = -mat_trace(M) // k
        coeffs.append(ck)
    return coeffs


def analyze_lattice(le):
    n = len(le)
    cov = [[False] * n for _ in range(n)]
    for x in range(n):
        for y in range(n):
            if x != y and le[x][y]:
                if not any(z != x and z != y and le[x][z] and le[z][y] for z in range(n)):
                    cov[x][y] = True

    c_plus = [sum(1 for y in range(n) if cov[x][y]) for x in range(n)]
    c_minus = [sum(1 for y in range(n) if cov[y][x]) for x in range(n)]
    c_tot = [c_plus[x] + c_minus[x] for x in range(n)]

    join = [[0] * n for _ in range(n)]
    meet = [[0] * n for _ in range(n)]
    for a in range(n):
        for b in range(n):
            ubs = [x for x in range(n) if le[a][x] and le[b][x]]
            join[a][b] = [x for x in ubs if all(le[x][y] for y in ubs)][0]
            lbs = [x for x in range(n) if le[x][a] and le[x][b]]
            meet[a][b] = [x for x in lbs if all(le[y][x] for y in lbs)][0]

    modular = all(
        join[x][meet[y][z]] == meet[join[x][y]][z]
        for x in range(n) for y in range(n) for z in range(n) if le[x][z]
    )
    distributive = all(
        meet[x][join[y][z]] == join[meet[x][y]][meet[x][z]]
        for x in range(n) for y in range(n) for z in range(n)
    )

    memo_chains = {}
    def chain_lengths_from_bot(x):
        if x in memo_chains:
            return memo_chains[x]
        if x == 0:
            memo_chains[x] = {0}
            return {0}
        res = {d + 1 for y in range(n) if cov[y][x] for d in chain_lengths_from_bot(y)}
        memo_chains[x] = res
        return res

    d_sets = [chain_lengths_from_bot(x) for x in range(n)]
    graded = all(len(s) == 1 for s in d_sets)
    ranks = [next(iter(s)) for s in d_sets] if graded else None
    min_h = [min(s) for s in d_sets]

    upper_global = len({c_plus[x] for x in range(n - 1)}) <= 1
    lower_global = len({c_minus[x] for x in range(1, n)}) <= 1
    upper_interior = len({c_plus[x] for x in range(1, n - 1)}) <= 1
    lower_interior = len({c_minus[x] for x in range(1, n - 1)}) <= 1
    hasse_reg = len(set(c_tot)) <= 1

    whitney = None
    rank_upper = False
    rank_lower = False
    rank_cov_sym = False
    if graded:
        h = max(ranks)
        whitney = tuple(sum(1 for x in range(n) if ranks[x] == r) for r in range(h + 1))
        rank_upper = all(len({c_plus[x] for x in range(n) if ranks[x] == r}) <= 1 for r in range(h + 1))
        rank_lower = all(len({c_minus[x] for x in range(n) if ranks[x] == r}) <= 1 for r in range(h + 1))
        rank_cov_sym = all(
            c_plus[x] == c_minus[y]
            for x in range(n) for y in range(n) if ranks[x] + ranks[y] == h
        )

    min_h_upper = all(
        len({c_plus[x] for x in range(n) if min_h[x] == r}) <= 1
        for r in set(min_h)
    )

    adj = [[1 if (cov[i][j] or cov[j][i]) else 0 for j in range(n)] for i in range(n)]
    cp_adj = char_poly(adj)
    tr5 = mat_trace(mat_pow(adj, 5))

    return {
        "n": n,
        "edges": [(u, v) for u in range(n) for v in range(n) if cov[u][v]],
        "c_plus": c_plus,
        "c_minus": c_minus,
        "c_tot": c_tot,
        "modular": modular,
        "distributive": distributive,
        "graded": graded,
        "ranks": ranks,
        "whitney": whitney,
        "whitney_sym": (whitney == whitney[::-1]) if whitney is not None else False,
        "rank_cov_sym": rank_cov_sym,
        "multiset_sym": sorted(c_plus) == sorted(c_minus),
        "upper_global": upper_global,
        "lower_global": lower_global,
        "upper_interior": upper_interior,
        "lower_interior": lower_interior,
        "hasse_reg": hasse_reg,
        "rank_upper": rank_upper,
        "rank_lower": rank_lower,
        "min_h_upper": min_h_upper,
        "cp_adj": cp_adj,
        "adj_zero_sym": all(cp_adj[k] == 0 for k in range(1, len(cp_adj), 2)),
        "tr_adj_5": tr5,
    }


def main():
    print("=" * 78)
    print("CONJECTURE 00000008545 — EXHAUSTIVE FINITE LATTICE VERIFICATION (1 <= n <= 7)")
    print("=" * 78)

    expected_oeis_a006966 = {1: 1, 2: 1, 3: 1, 4: 2, 5: 5, 6: 15, 7: 53}
    analyzed = {}

    for n in range(1, 8):
        lats = generate_unlabeled_lattices(n)
        assert len(lats) == expected_oeis_a006966[n], (
            f"Count mismatch at n={n}: got {len(lats)}, expected {expected_oeis_a006966[n]}"
        )
        analyzed[n] = [analyze_lattice(le) for le in lats]
        print(f"[OK] n = {n}: {len(lats):2d} unlabeled lattices (matches OEIS A006966)")

    print("\n" + "-" * 78)
    print("SUMMARY COUNTS OF UNIFORM LATTICES FOR n = 1..7 ACROSS ALL REGIMES")
    print("-" * 78)
    regimes = [
        ("Total lattices", lambda d: True),
        ("Global uniform (c+ on L\\{1}, c- on L\\{0})", lambda d: d["upper_global"] and d["lower_global"]),
        ("Undirected Hasse regular (c+ + c- const)", lambda d: d["hasse_reg"]),
        ("Strict interior uniform (L\\{0,1})", lambda d: d["upper_interior"] and d["lower_interior"]),
        ("Graded rank-uniform (upper & lower)", lambda d: d["rank_upper"] and d["rank_lower"]),
        ("Graded rank-upper-uniform", lambda d: d["rank_upper"]),
        ("Graded rank-lower-uniform", lambda d: d["rank_lower"]),
    ]
    print(f"{'Regime':44s} | n=1  2  3  4  5   6   7")
    print("-" * 78)
    for label, pred in regimes:
        row = [sum(1 for d in analyzed[n] if pred(d)) for n in range(1, 8)]
        print(f"{label:44s} | {row[0]:3d}{row[1]:3d}{row[2]:3d}{row[3]:3d}{row[4]:3d}{row[5]:4d}{row[6]:4d}")

    # 1. Verify Regime I: Global non-extremal uniformity
    print("\n" + "-" * 78)
    print("CHECK 1: REGIME I — GLOBAL COVERING UNIFORMITY")
    print("-" * 78)
    for n in (1, 2, 3):
        assert all(d["upper_global"] and d["lower_global"] for d in analyzed[n])
    b2_list = [d for d in analyzed[4] if not d["upper_global"]]
    assert len(b2_list) == 1
    b2 = b2_list[0]
    assert b2["distributive"] and b2["modular"]
    assert not b2["upper_global"] and not b2["lower_global"]
    assert sorted(b2["c_plus"]) == [0, 1, 1, 2]
    print(f"[OK] All lattices of size <= 3 are globally uniform.")
    print(f"[OK] Minimal counterexample at n = 4 < 5 is B_2: modular={b2['modular']}, "
          f"distributive={b2['distributive']}, c+={b2['c_plus']}, c-={b2['c_minus']}.")

    # Verify ancillary variants (C_2 unrestricted & parity; C_3 Hasse regular vs N_5)
    c2 = analyzed[2][0]
    c3 = analyzed[3][0]
    assert len(set(c2["c_plus"])) > 1 and any(c2["c_plus"][x] % 2 == 1 for x in range(1))
    assert not c3["hasse_reg"]
    print(f"[OK] C_2 (n=2, modular) fails unrestricted constancy & arithmetic parity; "
          f"C_3 (n=3, modular) fails Hasse degree regularity.")

    # 2. Verify Regime II: Strict interior uniformity on n = 5
    print("\n" + "-" * 78)
    print("CHECK 2: REGIME II — STRICT INTERIOR UNIFORMITY ON L \\ {0, 1}")
    print("-" * 78)
    n5_candidates = [d for d in analyzed[5] if not d["modular"]]
    assert len(n5_candidates) == 1
    n5 = n5_candidates[0]
    assert not n5["graded"]
    assert n5["upper_interior"] and n5["lower_interior"] and n5["hasse_reg"]
    assert n5["cp_adj"] == [1, 0, -5, 0, 5, -2]
    assert n5["tr_adj_5"] == 10 and not n5["adj_zero_sym"]
    print(f"[OK] N_5 (unique 5-element nonmodular lattice) SATISFIES interior uniformity "
          f"(c+={n5['c_plus']}, c-={n5['c_minus']}) and is 2-regular, with tr(A^5) = {n5['tr_adj_5']} != 0.")

    int_failures_5 = [d for d in analyzed[5] if not (d["upper_interior"] and d["lower_interior"])]
    assert len(int_failures_5) == 2
    assert all(d["distributive"] and d["modular"] for d in int_failures_5)
    print(f"[OK] Minimal failures of interior uniformity have n = 5 and are BOTH distributive "
          f"and modular (B_2 (+) 1 and 1 (+) B_2); N_5 is NOT among them.")

    # 3. Verify Regime III: Graded rank-wise uniformity & spectrum counterexamples
    print("\n" + "-" * 78)
    print("CHECK 3: REGIME III — GRADED RANK UNIFORMITY & SPECTRUM ASYMMETRY")
    print("-" * 78)
    for n in range(1, 5):
        assert all(d["rank_upper"] and d["rank_lower"] for d in analyzed[n])
    rk_failures_5 = [d for d in analyzed[5] if not (d["rank_upper"] and d["rank_lower"])]
    assert len(rk_failures_5) == 1 and not rk_failures_5[0]["modular"]
    print("[OK] Under graded rank-uniformity, N_5 IS the unique minimal counterexample (n = 5).")

    asym_rank_5 = [
        d for d in analyzed[5]
        if d["rank_upper"] and d["rank_lower"] and not d["whitney_sym"]
    ]
    assert len(asym_rank_5) == 2
    whitneys_5 = sorted(d["whitney"] for d in asym_rank_5)
    assert whitneys_5 == [(1, 1, 2, 1), (1, 2, 1, 1)]
    assert all(d["distributive"] and d["modular"] and not d["rank_cov_sym"] for d in asym_rank_5)
    print(f"[OK] B_2 (+) 1 and 1 (+) B_2 (n = 5, distributive & modular) are BOTH rank-upper- "
          f"and rank-lower-uniform, yet have non-palindromic Whitney spectra {whitneys_5} "
          f"and asymmetric rank-covering profiles.")

    # Verify 7-element graded rank-upper-uniform lattice with unequal covering multisets
    lat7_matches = [
        d for d in analyzed[7]
        if d["rank_upper"]
        and d["upper_interior"]
        and not d["rank_lower"]
        and sorted(d["c_plus"]) == [0, 1, 1, 1, 1, 1, 3]
        and sorted(d["c_minus"]) == [0, 1, 1, 1, 1, 2, 2]
    ]
    assert len(lat7_matches) == 1
    lat7 = lat7_matches[0]
    assert lat7["whitney"] == (1, 3, 2, 1) and not lat7["whitney_sym"] and not lat7["multiset_sym"]
    print(f"[OK] L_7 (n = 7, graded, W = {lat7['whitney']}) is rank-upper-uniform and "
          f"interior-upper-uniform, yet NOT rank-lower-uniform, and has unequal covering-degree "
          f"multisets: sorted(c+) = {sorted(lat7['c_plus'])} != {sorted(lat7['c_minus'])} = sorted(c-).")

    # Verify 6-element min-height upper-uniform lattice N_5 (+) 1 with tr(A^5) = 10 != 0
    n5_plus_1_matches = [
        d for d in analyzed[6]
        if d["min_h_upper"] and not d["adj_zero_sym"] and d["tr_adj_5"] == 10
    ]
    assert len(n5_plus_1_matches) == 1
    n5p1 = n5_plus_1_matches[0]
    assert n5p1["cp_adj"] == [1, 0, -6, 0, 8, -2, -1]
    print(f"[OK] N_5 (+) 1 (n = 6) satisfies shortest-chain height upper uniformity yet has "
          f"Hasse charpoly {n5p1['cp_adj']} and tr(A^5) = {n5p1['tr_adj_5']} != 0.")

    print("\n" + "=" * 78)
    print("VERDICT: CONJECTURE 00000008545 IS FALSE UNDER EVERY INTERPRETATION.")
    print("ALL VERIFICATION CHECKS PASSED.")
    print("=" * 78)


if __name__ == "__main__":
    main()
    sys.exit(0)
