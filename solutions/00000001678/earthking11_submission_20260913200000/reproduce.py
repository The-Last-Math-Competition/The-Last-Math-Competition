#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001678.

    Conjecture: the difference between the zero forcing number Z and the path
    cover number P on trees takes values in {0, 1}, with an explicit tree
    classification; moreover the trees with difference one are *exactly* the
    odd-diameter trees admitting a perfect matching.

This script provides computational corroboration for the refutation of the
"exactly" clause.  The witness is the path P_4:

  * Z(P_4) = 1, computed by brute force over all colourings with the
    colour-change closure;
  * P(P_4) = 1, computed by exhaustive search over all path covers;
  * hence Z - P = 0, not 1;
  * while diameter(P_4) = 3 is odd and P_4 has a perfect matching.

More generally the script:

  (1) for n = 1..10 computes Z(P_n) and P(P_n) by brute force, and asserts that
      every odd-diameter P_n admitting a perfect matching has Z - P = 0;
  (2) enumerates all trees on up to 10 vertices and reports
        # trees with Z - P = 1            (expected 0), and
        # odd-diameter trees with a perfect matching (expected > 0).
      Since the AIM theorem (Barioli-Fallat-Hogben et al.) gives Z(T) = P(T)
      for every tree, the difference-one class is empty while odd-diameter
      trees with perfect matchings certainly exist: the classification is false.

Trees are enumerated exhaustively over all Pruefer sequences for n <= 8 (where
the n^(n-2) labelled count is tractable: at most 16807 for n = 8), and for
n = 9, 10 by the standard canonical construction of rooted trees followed by
deduplication on the unrooted canonical form (the labelled count 10^8 is not
tractable).  Both methods are cross-validated on n <= 8.

Standard library only.  Python 3.8+.
"""

import sys
from functools import lru_cache
from itertools import product


# ---------------------------------------------------------------------------
# graphs: adjacency lists are Python lists of neighbour lists
# ---------------------------------------------------------------------------

def path_adj(n):
    """Adjacency list of the path P_n on vertices 0, ..., n-1."""
    return [[w for w in (v - 1, v + 1) if 0 <= w < n] for v in range(n)]


def edge_set(nbr):
    """All undirected edges of a graph, as sorted tuples."""
    return sorted({(min(v, w), max(v, w)) for v in range(len(nbr)) for w in nbr[v]})


def diameter(nbr):
    """Diameter of a connected graph, by BFS from every vertex."""
    n = len(nbr)
    if n <= 1:
        return 0
    best = 0
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        queue = [s]
        head = 0
        while head < len(queue):
            x = queue[head]
            head += 1
            for w in nbr[x]:
                if dist[w] < 0:
                    dist[w] = dist[x] + 1
                    queue.append(w)
        best = max(best, max(dist))
    return best


def has_perfect_matching(nbr):
    """Whether a graph has a perfect matching, by exact recursive search."""
    n = len(nbr)
    memo = {}

    def rec(mask):
        if mask == 0:
            return True
        if mask in memo:
            return memo[mask]
        v = (mask & -mask).bit_length() - 1  # lowest present vertex
        res = False
        for w in nbr[v]:
            if (mask >> w) & 1:
                if rec(mask & ~(1 << v) & ~(1 << w)):
                    res = True
                    break
        memo[mask] = res
        return res

    return rec((1 << n) - 1)


# ---------------------------------------------------------------------------
# zero forcing number: brute force over all subsets + colour-change closure
# ---------------------------------------------------------------------------

def zero_forcing_number(nbr):
    """Z(G) = minimum size of a zero forcing set, by brute force.

    A vertex u that is black and has exactly one white neighbour v forces v;
    repeat until no change.  This is the colour-change rule.
    """
    n = len(nbr)
    full = (1 << n) - 1

    def closure(start):
        black = start
        while True:
            newly = 0
            for u in range(n):
                if not (black >> u) & 1:
                    continue
                white = [w for w in nbr[u] if not (black >> w) & 1]
                if len(white) == 1:
                    newly |= 1 << white[0]
            if newly == 0:
                return black
            black |= newly

    best = n
    for subset in range(1 << n):
        if closure(subset) == full:
            size = bin(subset).count("1")
            if size < best:
                best = size
    return best


# ---------------------------------------------------------------------------
# path cover number: brute force over all path covers
# ---------------------------------------------------------------------------

def is_path_set(nbr, subset):
    """Whether the vertex set `subset` induces a path."""
    verts = [v for v in range(len(nbr)) if (subset >> v) & 1]
    if not verts:
        return False
    for v in verts:
        if sum(1 for w in nbr[v] if (subset >> w) & 1) > 2:
            return False
    # connectivity of the induced subgraph, by BFS
    seen = {verts[0]}
    stack = [verts[0]]
    while stack:
        x = stack.pop()
        for w in nbr[x]:
            if (subset >> w) & 1 and w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == len(verts)


def path_cover_number(nbr):
    """P(G) = minimum number of vertex-disjoint induced paths covering V(G).

    Exact search: repeatedly cover the lowest uncovered vertex with one of the
    precomputed path-inducing vertex sets contained in the uncovered part.
    """
    n = len(nbr)
    path_sets = [S for S in range(1, 1 << n) if is_path_set(nbr, S)]

    @lru_cache(maxsize=None)
    def rec(remaining):
        if remaining == 0:
            return 0
        v = (remaining & -remaining).bit_length() - 1
        best = n + 1
        for S in path_sets:
            if (S >> v) & 1 and (S & remaining) == S:
                cand = 1 + rec(remaining & ~S)
                if cand < best:
                    best = cand
        return best

    return rec((1 << n) - 1)


# ---------------------------------------------------------------------------
# non-isomorphic trees: Pruefer enumeration (small n) and canonical rooted
# trees (larger n)
# ---------------------------------------------------------------------------

def prufer_to_adj(seq, n):
    """Build the labelled tree encoded by a Pruefer sequence."""
    if n == 1:
        return [[]]
    if n == 2:
        return [[1], [0]]
    deg = [1] * n
    for x in seq:
        deg[x] += 1
    nbr = [[] for _ in range(n)]
    leaves = sorted(v for v in range(n) if deg[v] == 1)

    def pop_leaf():
        leaf = leaves.pop(0)
        return leaf

    def push_leaf(v):
        # keep `leaves` sorted (small lists)
        lo, hi = 0, len(leaves)
        while lo < hi:
            mid = (lo + hi) // 2
            if leaves[mid] < v:
                lo = mid + 1
            else:
                hi = mid
        leaves.insert(lo, v)

    for x in seq:
        leaf = pop_leaf()
        nbr[leaf].append(x)
        nbr[x].append(leaf)
        deg[leaf] -= 1
        deg[x] -= 1
        if deg[x] == 1:
            push_leaf(x)
    u = pop_leaf()
    v = pop_leaf()
    nbr[u].append(v)
    nbr[v].append(u)
    return [sorted(a) for a in nbr]


def tree_centers(nbr):
    """Centres of a tree (one vertex, or two adjacent vertices).

    Standard leaf-stripping: repeatedly delete all current leaves until at most
    two vertices remain.
    """
    n = len(nbr)
    if n == 1:
        return [0]
    deg = [len(nbr[v]) for v in range(n)]
    removed = [False] * n
    leaves = [v for v in range(n) if deg[v] <= 1]
    remaining = n
    while remaining > 2:
        remaining -= len(leaves)
        new_leaves = []
        for v in leaves:
            removed[v] = True
            for w in nbr[v]:
                if not removed[w]:
                    deg[w] -= 1
                    if deg[w] == 1:
                        new_leaves.append(w)
        leaves = new_leaves
    return [v for v in range(n) if not removed[v]]


def tree_canonical(nbr):
    """Canonical string of an unrooted tree (AHU canonical form at the centre)."""
    n = len(nbr)
    if n == 1:
        return "()"

    def rooted(v, parent):
        subs = sorted(rooted(w, v) for w in nbr[v] if w != parent)
        return "(" + "".join(subs) + ")"

    centres = tree_centers(nbr)
    if len(centres) == 1:
        return rooted(centres[0], -1)
    a, b = centres
    ha, hb = rooted(a, b), rooted(b, a)
    return "{" + "".join(sorted((ha, hb))) + "}"


def rooted_shapes(n, by_size):
    """All rooted tree shapes with n nodes, as sorted nested tuples.

    A rooted tree is a root plus an unordered multiset of rooted subtrees whose
    sizes sum to n - 1.  Multisets of canonical shapes are generated by choosing
    multiplicities, so every rooted shape is produced exactly once.
    """
    if n == 1:
        return [()]
    items = [(s, h) for s in range(1, n) for h in by_size[s]]
    result = set()

    def rec(idx, remaining, chosen):
        if remaining == 0:
            result.add(tuple(sorted(chosen)))
            return
        if idx >= len(items):
            return
        size, shape = items[idx]
        k = 0
        while k * size <= remaining:
            rec(idx + 1, remaining - k * size, chosen + [shape] * k)
            k += 1

    rec(0, n - 1, [])
    return sorted(result, key=repr)


def rooted_to_adj(shape):
    """Adjacency list of the tree underlying a nested-tuple rooted shape."""
    nbr = []

    def build(node, parent):
        idx = len(nbr)
        nbr.append([])
        if parent is not None:
            nbr[idx].append(parent)
            nbr[parent].append(idx)
        for child in node:
            build(child, idx)

    build(shape, None)
    return [sorted(a) for a in nbr]


def rooted_tables(max_n):
    tables = {1: rooted_shapes(1, {})}
    for n in range(2, max_n + 1):
        tables[n] = rooted_shapes(n, tables)
    return tables


def trees_via_rooted(max_n):
    """Non-isomorphic trees on 2..max_n vertices, keyed by canonical form."""
    tables = rooted_tables(max_n)
    out = {}
    for n in range(2, max_n + 1):
        for shape in tables[n]:
            nbr = rooted_to_adj(shape)
            out.setdefault(tree_canonical(nbr), nbr)
    return list(out.values())


def trees_via_prufer(n):
    """All labelled trees on n vertices via Pruefer sequences, deduplicated."""
    out = {}
    for seq in product(range(n), repeat=n - 2):
        nbr = prufer_to_adj(seq, n)
        out.setdefault(tree_canonical(nbr), nbr)
    return list(out.values())


# ---------------------------------------------------------------------------
# reported checks
# ---------------------------------------------------------------------------

KNOWN_ISOMORPHIC_COUNTS = {1: 1, 2: 1, 3: 1, 4: 2, 5: 3, 6: 6, 7: 11, 8: 23, 9: 47, 10: 106}


def check_path_family():
    """Table for P_n, n = 1..10, plus the required assert."""
    print("[1] The path family P_n, n = 1..10 (Z and P by brute force)")
    print()
    header = f"    {'n':>2} | {'Z(P_n)':>6} | {'P(P_n)':>6} | {'Z-P':>3} | "
    header += f"{'diam':>4} | {'odd?':>4} | {'perf match?':>11}"
    print(header)
    print("    " + "-" * (len(header) - 4))

    rows = []
    bad = []
    for n in range(1, 11):
        nbr = path_adj(n)
        z = zero_forcing_number(nbr)
        p = path_cover_number(nbr)
        diam = diameter(nbr)
        odd = (diam % 2 == 1)
        pm = has_perfect_matching(nbr)
        rows.append((n, z, p, z - p, diam, odd, pm))
        print(f"    {n:>2} | {z:>6} | {p:>6} | {z - p:>3} | "
              f"{diam:>4} | {str(odd):>4} | {str(pm):>11}")
        if odd and pm and z - p != 0:
            bad.append(n)

    print()
    # The required assertion: every odd-diameter P_n with a perfect matching has
    # difference 0 (so none of them lies in the difference-one class).
    rhs_family = [r for r in rows if r[5] and r[6]]
    assert rhs_family, "expected odd-diameter P_n with a perfect matching"
    for (_n, z, p, _d, _diam, _odd, _pm) in rhs_family:
        assert z - p == 0, f"expected Z-P = 0 for P_{_n}, got {z - p}"
    assert not bad, f"unexpected nonzero differences: {bad}"

    # Stronger context: the AIM theorem predicts Z = P on every tree.
    aim_ok = all(z == p for (_n, z, p, _d, _diam, _odd, _pm) in rows)
    print(f"    odd-diameter P_n with a perfect matching: "
          f"{[r[0] for r in rhs_family]} -> all have Z-P = 0")
    print(f"    every P_n has Z(P_n) = P(P_n): {aim_ok}")
    assert aim_ok, "expected Z = P for every path"
    print()
    return rows, rhs_family


def check_all_trees():
    """Brute force all trees up to 10 vertices; report the two counts."""
    max_n = 10
    print("[2] All trees on 1..10 vertices (exhaustive over isomorphism classes)")

    # Cross-validate the two generators on n <= 8.
    for n in range(2, 9):
        via_pruefer = {tree_canonical(t) for t in trees_via_prufer(n)}
        via_rooted = {tree_canonical(t)
                      for t in trees_via_rooted(n) if len(t) == n}
        assert via_pruefer == via_rooted, f"generator mismatch at n = {n}"
        assert len(via_pruefer) == KNOWN_ISOMORPHIC_COUNTS[n], (
            f"expected {KNOWN_ISOMORPHIC_COUNTS[n]} trees on {n} vertices, "
            f"found {len(via_pruefer)}")
    print("    generators (Pruefer n<=8 vs canonical rooted trees) cross-validated")

    print()
    print(f"    {'n':>2} | {'#trees':>6} | {'Z=P':>4} | {'Z-P=1':>5} | "
          f"{'odd diam':>8} | {'odd & match':>11}")
    print("    " + "-" * 62)

    total_trees = 0
    total_diff_one = 0
    total_rhs = 0
    trees = list(trees_via_rooted(max_n))
    trees.append([[]])  # the single vertex, P_1
    trees.sort(key=lambda a: (len(a), tree_canonical(a)))

    by_n = {}
    for nbr in trees:
        n = len(nbr)
        z = zero_forcing_number(nbr)
        p = path_cover_number(nbr)
        diam = diameter(nbr)
        odd = (diam % 2 == 1)
        pm = has_perfect_matching(nbr)
        rec = by_n.setdefault(n, {"trees": 0, "zp": 0, "diff1": 0, "odd": 0, "rhs": 0})
        rec["trees"] += 1
        rec["zp"] += int(z == p)
        rec["diff1"] += int(z - p == 1)
        rec["odd"] += int(odd)
        rec["rhs"] += int(odd and pm)
        total_trees += 1
        total_diff_one += int(z - p == 1)
        total_rhs += int(odd and pm)

    for n in sorted(by_n):
        r = by_n[n]
        print(f"    {n:>2} | {r['trees']:>6} | {r['zp']:>4} | {r['diff1']:>5} | "
              f"{r['odd']:>8} | {r['rhs']:>11}")

    print()
    print(f"    total trees (1..10 vertices)....................... {total_trees}")
    print(f"    with Z - P = 1 (the conjectured difference-one class) {total_diff_one}")
    print(f"    with odd diameter and a perfect matching............. {total_rhs}")
    print(f"    with Z = P (AIM theorem)............................. "
          f"{sum(r['zp'] for r in by_n.values())}")

    # The classification fails: the difference-one class is empty, while the
    # odd-diameter trees with a perfect matching are abundant.
    assert total_diff_one == 0, "expected no tree with Z - P = 1"
    assert total_rhs > 0, "expected some odd-diameter tree with a perfect matching"
    print()
    return total_trees, total_diff_one, total_rhs


def main():
    line = "=" * 72
    print(line)
    print("Disproof of conjecture 00000001678 -- reproduction")
    print(line)
    print()
    print("The trees with difference one are NOT exactly the odd-diameter trees")
    print("admitting a perfect matching: P_4 (and P_2, P_6, ...) are odd-diameter")
    print("trees with a perfect matching but have Z - P = 0.")
    print()

    rows, rhs_family = check_path_family()
    total_trees, total_diff_one, total_rhs = check_all_trees()

    print(line)
    checks_ok = (
        any(n == 4 and z == 1 and p == 1 and z - p == 0 and diam == 3 and pm
            for (n, z, p, _d, diam, _odd, pm) in rows)
        and all(z - p == 0 for (_n, z, p, _d, _diam, _odd, _pm) in rhs_family)
        and total_diff_one == 0
        and total_rhs > 0
        and total_trees > 0
    )
    if checks_ok:
        print("PASS: P_4 has Z = 1, P = 1, Z - P = 0, odd diameter 3 and a")
        print("      perfect matching, so the 'exactly' clause is FALSE.")
        print(f"      Over all {total_trees} trees on 1..10 vertices: "
              f"{total_diff_one} trees have Z - P = 1, while")
        print(f"      {total_rhs} have odd diameter and a perfect matching. "
              f"Classification refuted.")
        print(line)
        return 0
    print("FAIL: a claimed refutation check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    sys.exit(main())
