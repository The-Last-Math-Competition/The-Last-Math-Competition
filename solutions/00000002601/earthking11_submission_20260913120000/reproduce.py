#!/usr/bin/env python3
"""Reproducibility check for the disproof of conjecture 00000002601.

Conjecture (as stated in conjectures/00000002601.md):
    The maximum number of fixed points of a monotone self-map of an n-element
    finite lattice equals the length of a maximal chain, attained on
    distributive lattices; the maximum drops strictly on non-distributive
    lattices, the drop being the minimal number of embedded N5 sublattices.

Refutation:
    The identity map is monotone on every finite lattice and fixes all n
    elements.  Hence the maximum number of fixed points is exactly n, the
    trivial upper bound.  On the 4-element distributive lattice
    B2 = {0, a, b, 1} the identity fixes 4 elements while a maximal chain
    has 3 elements (2 edges).  So the claimed equality fails, already on a
    distributive lattice, under either reading of "length" (elements or edges).

This script brute-forces all monotone self-maps of
    B2 (distributive, 4 elements, 4^4      = 256      maps),
    B3 (distributive, 8 elements, backtracking over 8^8 = 16.7M candidates),
    N5 (non-distributive, 5 elements, 5^5   = 3125     maps),
and prints the maximum number of fixed points next to the maximal chain
length.  It exits 0; a non-zero "conjecture holds" verdict would be a FAIL.
"""

import sys
from itertools import product


# --------------------------------------------------------------------------
# lattices
# --------------------------------------------------------------------------
# Each lattice is a pair (n, le) with le(i, j) a bool: element i <= element j.

def make_b2():
    # 0 = bottom, 1 = a, 2 = b, 3 = top; a and b incomparable.
    def le(x, y):
        return x == y or x == 0 or y == 3
    return 4, le


def make_b3():
    # Elements are bitmasks of subsets of {0,1,2}; order is inclusion.
    def le(x, y):
        return (x & y) == x
    return 8, le


def make_n5():
    # 0 = bottom, 1 = a, 2 = b, 3 = c, 4 = top.
    # 0 < a < b < top and 0 < a < c < top, with b and c incomparable.
    covers = {0: (1,), 1: (2, 3), 2: (4,), 3: (4,), 4: ()}
    reach = {x: set() for x in range(5)}

    def dfs(x):
        if x not in reach[x]:
            reach[x].add(x)
        for y in covers[x]:
            dfs(y)
            reach[x] |= reach[y]

    for x in range(5):
        dfs(x)

    def le(x, y):
        return y in reach[x]
    return 5, le


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------
def max_chain_length(n, le):
    """Longest chain, counted in elements (edges = elements - 1)."""
    # elements sorted so that predecessors come first
    order = sorted(range(n), key=lambda x: sum(1 for y in range(n) if le(y, x) and y != x))
    best = [1] * n
    for x in order:
        for y in order:
            if y != x and le(y, x):
                if best[y] + 1 > best[x]:
                    best[x] = best[y] + 1
    return max(best)


def is_monotone(f, n, le):
    for x in range(n):
        for y in range(n):
            if le(x, y) and not le(f[x], f[y]):
                return False
    return True


def fixed_points(f):
    return sum(1 for i, v in enumerate(f) if i == v)


def brute_force(n, le):
    """Exhaustive scan of all n^n self-maps (use only for small n)."""
    count_mono = 0
    max_fix = -1
    max_fix_nonid = -1
    for f in product(range(n), repeat=n):
        if not is_monotone(f, n, le):
            continue
        count_mono += 1
        fp = fixed_points(f)
        if fp > max_fix:
            max_fix = fp
        if f != tuple(range(n)) and fp > max_fix_nonid:
            max_fix_nonid = fp
    return count_mono, max_fix, max_fix_nonid


def backtrack_monotone(n, le):
    """Enumerate exactly the monotone self-maps by DFS with pruning.

    Returns (number of monotone maps, max fixed points, max fixed points
    among non-identity maps).  Assigns values in an order in which every
    strict predecessor of an element is assigned before it, so partial
    monotonicity checks are complete.
    """
    # number of strict predecessors, then value, as a topological order
    preds = {x: sum(1 for y in range(n) if y != x and le(y, x)) for x in range(n)}
    order = sorted(range(n), key=lambda x: (preds[x], x))
    f = [None] * n
    ident = tuple(range(n))
    stats = {"count": 0, "max": -1, "max_nonid": -1}

    def dfs(i):
        if i == n:
            stats["count"] += 1
            fp = fixed_points(f)
            if fp > stats["max"]:
                stats["max"] = fp
            if tuple(f) != ident and fp > stats["max_nonid"]:
                stats["max_nonid"] = fp
            return
        x = order[i]
        for v in range(n):
            ok = True
            for j in range(i):
                y = order[j]
                fy = f[y]
                if le(y, x) and not le(fy, v):
                    ok = False
                    break
                if le(x, y) and not le(v, fy):
                    ok = False
                    break
            if ok:
                f[x] = v
                dfs(i + 1)
                f[x] = None

    dfs(0)
    return stats["count"], stats["max"], stats["max_nonid"]


# --------------------------------------------------------------------------
# run
# --------------------------------------------------------------------------
def main():
    results = []

    n, le = make_b2()
    cm, mf, mfn = brute_force(n, le)
    chain = max_chain_length(n, le)
    results.append(("B2 (distributive)", n, cm, mf, mfn, chain))

    n, le = make_b3()
    cm, mf, mfn = backtrack_monotone(n, le)
    chain = max_chain_length(n, le)
    results.append(("B3 (distributive)", n, cm, mf, mfn, chain))

    n, le = make_n5()
    cm, mf, mfn = brute_force(n, le)
    chain = max_chain_length(n, le)
    results.append(("N5 (non-distributive)", n, cm, mf, mfn, chain))

    print("conjecture 00000002601: max #fixed points vs maximal chain length")
    print("=" * 78)
    all_refuted = True
    for name, n, cm, mf, mfn, chain in results:
        edges = chain - 1
        ref_elem = mf != chain
        ref_edge = mf != edges
        verdict = "REFUTED" if (ref_elem and ref_edge) else "not refuted"
        if not (ref_elem and ref_edge):
            all_refuted = False
        print(f"{name}: |L|={n}")
        print(f"    monotone self-maps enumerated : {cm}")
        print(f"    max #fixed points             : {mf}"
              f"   (identity fixes {n}; non-identity max {mfn})")
        print(f"    maximal chain elements (edges): {chain} ({edges})")
        print(f"    max #fixed == chain elements? : {mf == chain}   -> {verdict}")
        print(f"    max #fixed == chain edges?    : {mf == edges}   -> {verdict}")
        print("-" * 78)

    print()
    print("The identity map is monotone and fixes all n elements on EVERY finite")
    print("lattice, so max #fixed = n (the trivial upper bound); a maximal chain")
    print("has at most n elements and at most n-1 edges.  Equality fails as soon")
    print("as some element lies off a maximal chain, e.g. already on B2.")
    print()
    if all_refuted:
        print("PASS: conjecture 00000002601 is FALSE on all tested lattices "
              "(both readings of chain length).")
        return 0
    print("FAIL: conjecture survived on some lattice; refutation incomplete.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
