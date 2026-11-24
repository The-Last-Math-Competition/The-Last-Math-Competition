#!/usr/bin/env python3
"""
Verification script for Conjecture 00000001242:
"Definition: The lamp lighting game (lit-only sigma-game).
 Conjecture: The graphs with min-lit number at most ceil(n/2) are exactly
 those with an odd bipartition (a lit-only extremal characterization)."

This script exhaustively tests all labelled simple graphs on 1 <= n <= 5 vertices,
all non-isomorphic simple graphs on 1 <= n <= 6 vertices (matching OEIS A000088
and A001349), and infinite counterexample families across all 24 combinations of
standard literature conventions:
  - 2 move rules: open-neighborhood (sigma^-) and closed-neighborhood (sigma^+)
  - 3 min-lit definitions: from all-lit V, worst-case over all S_0 <= V,
    and worst-case over all nonempty S_0 <= V
  - 4 odd-bipartition definitions: exists bipartition with >=1 odd part,
    exists bipartition with both parts odd, every bipartition has >=1 odd part,
    and every bipartition has both parts odd.
"""

from __future__ import annotations
import itertools
import sys


def ceil_half(n: int) -> int:
    """Return ceil(n / 2) = floor((n + 1) / 2)."""
    return (n + 1) // 2


def adj_from_edges(n: int, edges: list[tuple[int, int]]) -> list[int]:
    """Build bitmask adjacency list for an n-vertex simple graph."""
    adj = [0] * n
    for u, v in edges:
        assert 0 <= u < n and 0 <= v < n and u != v
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return adj


def is_connected(n: int, adj: list[int]) -> bool:
    """Check whether an n-vertex graph is connected."""
    if n <= 1:
        return True
    vis = 1
    queue = [0]
    for u in queue:
        nb = adj[u] & ~vis
        while nb:
            lsb = nb & -nb
            v = lsb.bit_length() - 1
            vis |= lsb
            queue.append(v)
            nb ^= lsb
    return vis == (1 << n) - 1


def is_tree(n: int, adj: list[int]) -> bool:
    """Check whether an n-vertex graph is a tree."""
    if not is_connected(n, adj):
        return False
    edge_count = sum(x.bit_count() for x in adj) // 2
    return edge_count == n - 1


def all_bipartitions(n: int, adj: list[int]) -> list[tuple[int, int]]:
    """Return all ordered bipartitions (A, B) of V = {0, ..., n-1} as bitmasks."""
    full = (1 << n) - 1
    result: list[tuple[int, int]] = []
    for a_mask in range(1 << n):
        b_mask = full ^ a_mask
        valid = True
        for u in range(n):
            if (a_mask >> u) & 1:
                if adj[u] & a_mask:
                    valid = False
                    break
            else:
                if adj[u] & b_mask:
                    valid = False
                    break
        if valid:
            result.append((a_mask, b_mask))
    return result


def odd_bipartition_flags(n: int, adj: list[int]) -> dict[str, bool]:
    """Evaluate all four interpretations of 'G has an odd bipartition'."""
    bips = all_bipartitions(n, adj)
    is_bip = len(bips) > 0
    ex_some = any((a.bit_count() % 2 == 1) or (b.bit_count() % 2 == 1) for a, b in bips)
    ex_both = any((a.bit_count() % 2 == 1) and (b.bit_count() % 2 == 1) for a, b in bips)
    fa_some = is_bip and all(
        (a.bit_count() % 2 == 1) or (b.bit_count() % 2 == 1) for a, b in bips
    )
    fa_both = is_bip and all(
        (a.bit_count() % 2 == 1) and (b.bit_count() % 2 == 1) for a, b in bips
    )
    return {
        "is_bipartite": is_bip,
        "ex_some": ex_some,
        "ex_both": ex_both,
        "fa_some": fa_some,
        "fa_both": fa_both,
    }


def min_lit_metrics(n: int, adj: list[int], closed: bool) -> tuple[int, int, int]:
    """
    Compute (minLit_all_lit, minLit_worst_all, minLit_worst_nonempty)
    under open-neighborhood (closed=False) or closed-neighborhood (closed=True)
    lit-only moves.
    """
    num_states = 1 << n
    transitions: list[list[int]] = [[] for _ in range(num_states)]
    for s in range(num_states):
        tmp = s
        while tmp:
            lsb = tmp & -tmp
            v = lsb.bit_length() - 1
            tmp ^= lsb
            toggle = adj[v] | (lsb if closed else 0)
            transitions[s].append(s ^ toggle)

    best_from = [0] * num_states
    for s0 in range(num_states):
        vis = 1 << s0
        queue = [s0]
        best = s0.bit_count()
        for s in queue:
            pc = s.bit_count()
            if pc < best:
                best = pc
            if best == 0:
                break
            for ns in transitions[s]:
                if not ((vis >> ns) & 1):
                    vis |= 1 << ns
                    queue.append(ns)
        best_from[s0] = best

    all_lit = best_from[num_states - 1]
    worst_all = max(best_from)
    worst_nonempty = max(best_from[1:]) if n >= 1 else 0
    return all_lit, worst_all, worst_nonempty


def canonical_graph_key(n: int, adj: list[int]) -> int:
    """Compute canonical adjacency bitmask under S_n vertex permutations (for n <= 6)."""
    best = -1
    for perm in itertools.permutations(range(n)):
        code = 0
        bit = 0
        for i in range(n):
            pi = perm[i]
            row = adj[pi]
            for j in range(i + 1, n):
                if (row >> perm[j]) & 1:
                    code |= 1 << bit
                bit += 1
        if code > best:
            best = code
    return best


def generate_unlabelled_graphs(n: int) -> list[list[int]]:
    """Generate one representative per isomorphism class of simple graphs on n vertices."""
    edges = list(itertools.combinations(range(n), 2))
    # Group by sorted degree sequence first to avoid redundant S_n scans
    by_deg: dict[tuple[int, ...], list[tuple[int, list[int]]]] = {}
    seen_codes_by_deg: dict[tuple[int, ...], set[int]] = {}
    reps: list[list[int]] = []

    perms = list(itertools.permutations(range(n)))
    for mask in range(1 << len(edges)):
        adj = [0] * n
        for idx, (u, v) in enumerate(edges):
            if (mask >> idx) & 1:
                adj[u] |= 1 << v
                adj[v] |= 1 << u
        deg_seq = tuple(sorted(x.bit_count() for x in adj))
        seen = seen_codes_by_deg.setdefault(deg_seq, set())
        if mask in seen:
            continue
        reps.append(adj)
        # Add entire isomorphism orbit of adj to seen
        for perm in perms:
            orb_mask = 0
            bit = 0
            for i in range(n):
                row = adj[perm[i]]
                for j in range(i + 1, n):
                    if (row >> perm[j]) & 1:
                        orb_mask |= 1 << bit
                    bit += 1
            seen.add(orb_mask)
        by_deg.setdefault(deg_seq, []).append((mask, adj))
    return reps


def verify_labelled_census_up_to_5() -> None:
    print("=== 1. Exhaustive Labelled Simple Graph Census (1 <= n <= 5) ===")
    expected_total = {1: 1, 2: 2, 3: 8, 4: 64, 5: 1024}
    for n in range(1, 6):
        bound = ceil_half(n)
        edges = list(itertools.combinations(range(n), 2))
        total = 0
        fwd_fail_open1_some = 0
        bwd_fail_open1_some = 0
        for mask in range(1 << len(edges)):
            total += 1
            adj = [0] * n
            for idx, (u, v) in enumerate(edges):
                if (mask >> idx) & 1:
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
            o1, omax, onemp = min_lit_metrics(n, adj, closed=False)
            c1, cmax, cnemp = min_lit_metrics(n, adj, closed=True)
            assert omax == onemp and cmax == cnemp
            flags = odd_bipartition_flags(n, adj)
            if (o1 <= bound) and not flags["ex_some"]:
                fwd_fail_open1_some += 1
            if flags["ex_some"] and not (o1 <= bound):
                bwd_fail_open1_some += 1
        assert total == expected_total[n]
        print(
            f"  n={n} (ceil={bound}): {total:4d} labelled graphs | "
            f"sigma^- all-lit vs ex_some: fail(=>)={fwd_fail_open1_some:3d}, "
            f"fail(<=)={bwd_fail_open1_some:2d}"
        )


def verify_unlabelled_census_up_to_6() -> None:
    print("\n=== 2. Exhaustive Unlabelled Graph Census (1 <= n <= 6, All 24 Conventions) ===")
    oeis_a000088 = {1: 1, 2: 2, 3: 4, 4: 11, 5: 34, 6: 156}
    oeis_a001349 = {1: 1, 2: 1, 3: 2, 4: 6, 5: 21, 6: 112}

    ml_keys = [
        "open_all_lit",
        "open_worst_all",
        "open_worst_nonempty",
        "closed_all_lit",
        "closed_worst_all",
        "closed_worst_nonempty",
    ]
    bip_keys = ["ex_some", "ex_both", "fa_some", "fa_both"]

    totals_fwd = {(mk, bk, sc): 0 for mk in ml_keys for bk in bip_keys for sc in ("all", "conn", "bip_conn", "tree")}
    totals_bwd = {(mk, bk, sc): 0 for mk in ml_keys for bk in bip_keys for sc in ("all", "conn", "bip_conn", "tree")}

    for n in range(1, 7):
        bound = ceil_half(n)
        reps = generate_unlabelled_graphs(n)
        conn_reps = [adj for adj in reps if is_connected(n, adj)]
        assert len(reps) == oeis_a000088[n], f"n={n}: got {len(reps)}"
        assert len(conn_reps) == oeis_a001349[n], f"n={n}: got {len(conn_reps)}"
        print(
            f"  n={n} (ceil={bound}): {len(reps):3d} non-isomorphic graphs "
            f"({len(conn_reps):3d} connected) [matches OEIS A000088 & A001349]"
        )

        for adj in reps:
            conn = is_connected(n, adj)
            tree = is_tree(n, adj)
            flags = odd_bipartition_flags(n, adj)
            bip_conn = conn and flags["is_bipartite"]

            o1, omax, onemp = min_lit_metrics(n, adj, closed=False)
            c1, cmax, cnemp = min_lit_metrics(n, adj, closed=True)
            mls = {
                "open_all_lit": o1,
                "open_worst_all": omax,
                "open_worst_nonempty": onemp,
                "closed_all_lit": c1,
                "closed_worst_all": cmax,
                "closed_worst_nonempty": cnemp,
            }

            scopes = {
                "all": True,
                "conn": conn,
                "bip_conn": bip_conn,
                "tree": tree,
            }
            for mk, mv in mls.items():
                lhs = mv <= bound
                for bk in bip_keys:
                    rhs = flags[bk]
                    for sc, active in scopes.items():
                        if not active:
                            continue
                        if lhs and not rhs:
                            totals_fwd[(mk, bk, sc)] += 1
                        if rhs and not lhs:
                            totals_bwd[(mk, bk, sc)] += 1

    print("\n  Summary across 1 <= n <= 6 non-isomorphic graphs (all 24 conventions):")
    for mk in ml_keys:
        for bk in bip_keys:
            f_all = totals_fwd[(mk, bk, "all")]
            b_all = totals_bwd[(mk, bk, "all")]
            f_conn = totals_fwd[(mk, bk, "conn")]
            f_bipc = totals_fwd[(mk, bk, "bip_conn")]
            f_tree = totals_fwd[(mk, bk, "tree")]
            assert f_all > 0 and f_conn > 0 and f_bipc > 0 and f_tree > 0, (
                f"Expected counterexamples in every scope for {(mk, bk)}"
            )
            print(
                f"    {mk:21s} | {bk:7s} -> "
                f"fail(=>) [all={f_all:3d}, conn={f_conn:3d}, bip_conn={f_bipc:2d}, tree={f_tree:2d}], "
                f"fail(<=) [all={b_all:2d}]"
            )


def verify_specific_witnesses_and_families() -> None:
    print("\n=== 3. Explicit Witnesses and Infinite Family Verification ===")

    # 3a. Positive non-vacuity witness: K_2 (n = 2)
    adj_k2 = adj_from_edges(2, [(0, 1)])
    assert is_connected(2, adj_k2) and is_tree(2, adj_k2)
    f_k2 = odd_bipartition_flags(2, adj_k2)
    assert all(f_k2[k] for k in ("is_bipartite", "ex_some", "ex_both", "fa_some", "fa_both"))
    assert min_lit_metrics(2, adj_k2, closed=False) == (1, 1, 1)
    assert min_lit_metrics(2, adj_k2, closed=True) == (0, 1, 1)
    print("  [PASS] Positive witness K_2 (n=2): connected, odd-odd bipartition (1,1), minLit <= 1 under all 6 variants.")

    # 3b. Non-bipartite connected family: K_n for 3 <= n <= 9
    for n in range(3, 10):
        edges = list(itertools.combinations(range(n), 2))
        adj = adj_from_edges(n, edges)
        assert is_connected(n, adj)
        flags = odd_bipartition_flags(n, adj)
        assert not flags["is_bipartite"]
        assert not any(flags[k] for k in ("ex_some", "ex_both", "fa_some", "fa_both"))
        o1, omax, onemp = min_lit_metrics(n, adj, closed=False)
        c1, cmax, cnemp = min_lit_metrics(n, adj, closed=True)
        bound = ceil_half(n)
        assert o1 == 1 <= bound
        assert omax == onemp == bound
        assert c1 == 0 <= bound
        assert cmax == cnemp == n // 2 <= bound
    print("  [PASS] Complete graphs K_n (3 <= n <= 9): connected, non-bipartite, minLit(K_n) <= ceil(n/2) under all 6 variants.")

    # 3c. Connected bipartite even-part family: K_{2k, 2k} for k = 1, 2 (n = 4, 8)
    for k in (1, 2):
        n = 4 * k
        edges = [(u, 2 * k + v) for u in range(2 * k) for v in range(2 * k)]
        adj = adj_from_edges(n, edges)
        assert is_connected(n, adj)
        flags = odd_bipartition_flags(n, adj)
        assert flags["is_bipartite"]
        assert not any(flags[b] for b in ("ex_some", "ex_both", "fa_some", "fa_both"))
        o1, omax, onemp = min_lit_metrics(n, adj, closed=False)
        c1, cmax, cnemp = min_lit_metrics(n, adj, closed=True)
        bound = ceil_half(n)
        assert bound == 2 * k
        assert o1 == 2 * k <= bound and omax == onemp == 2 * k <= bound
        assert c1 == 0 <= bound and cmax == cnemp <= bound
    print("  [PASS] Balanced even complete bipartite graphs K_{2k,2k} (k=1,2; n=4,8): connected bipartite, no odd bipartition, minLit <= 2k under all 6 variants.")

    # 3d. Tree counterexample: P_4 (n = 4)
    adj_p4 = adj_from_edges(4, [(0, 1), (1, 2), (2, 3)])
    assert is_tree(4, adj_p4)
    f_p4 = odd_bipartition_flags(4, adj_p4)
    assert f_p4["is_bipartite"] and not any(f_p4[b] for b in ("ex_some", "ex_both", "fa_some", "fa_both"))
    assert min_lit_metrics(4, adj_p4, closed=False) == (1, 1, 1)
    assert min_lit_metrics(4, adj_p4, closed=True) == (0, 0, 0)
    print("  [PASS] Path tree P_4 (n=4): tree with unique bipartition (2,2) (no odd part), minLit(P_4) <= 1 < 2 under all 6 variants.")

    # 3e. Converse counterexamples under sigma^-: Empty_{2m} and K_2 + Empty_{2m}
    for m in range(1, 5):
        n_emp = 2 * m
        adj_emp = adj_from_edges(n_emp, [])
        f_emp = odd_bipartition_flags(n_emp, adj_emp)
        assert f_emp["ex_some"] and f_emp["ex_both"]
        o1, omax, onemp = min_lit_metrics(n_emp, adj_emp, closed=False)
        assert o1 == omax == onemp == 2 * m > ceil_half(n_emp)

        n_k2e = 2 * m + 2
        adj_k2e = adj_from_edges(n_k2e, [(0, 1)])
        f_k2e = odd_bipartition_flags(n_k2e, adj_k2e)
        assert f_k2e["ex_some"] and f_k2e["ex_both"]
        o1_k, omax_k, onemp_k = min_lit_metrics(n_k2e, adj_k2e, closed=False)
        assert o1_k == omax_k == onemp_k == 2 * m + 1 > ceil_half(n_k2e)
    print("  [PASS] Converse counterexamples Empty_{2m} and K_2 + Empty_{2m} (1 <= m <= 4): odd-odd bipartition, yet sigma^- minLit > ceil(n/2).")

    # 3f. Connected non-triviality witness for sigma^- worst-case: K_{2,2,2} (octahedron, n = 6)
    oct_edges = [
        (u, v)
        for p1, p2 in [((0, 1), (2, 3)), ((0, 1), (4, 5)), ((2, 3), (4, 5))]
        for u in p1
        for v in p2
    ]
    adj_oct = adj_from_edges(6, oct_edges)
    assert is_connected(6, adj_oct)
    o1_oct, omax_oct, onemp_oct = min_lit_metrics(6, adj_oct, closed=False)
    assert o1_oct == 2 and omax_oct == onemp_oct == 4 > ceil_half(6)
    print("  [PASS] Connected non-triviality witness K_{2,2,2} (n=6): connected, sigma^- worst-case minLit = 4 > 3 = ceil(6/2).")


def main() -> int:
    verify_labelled_census_up_to_5()
    verify_unlabelled_census_up_to_6()
    verify_specific_witnesses_and_families()
    print("\nALL VERIFICATION CHECKS PASSED.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
