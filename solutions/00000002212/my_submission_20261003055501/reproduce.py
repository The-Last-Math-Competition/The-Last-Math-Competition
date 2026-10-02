#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002212.

The catenary degree c(H) of a numerical semigroup H (sup over elements n
of the minimal chain threshold connecting any two factorizations of n,
factorization distance = sup norm on exponent vectors) is NOT a function
of min(a,b,c) for 3-generated semigroups:

    c(<5,6,7>)  = 4   vs  c(<5,6,25>) = 5   (both min 5)
    c(<6,7,8>)  = 4   vs  c(<6,7,35>) = 7   (both min 6)

Exit 0 iff all checks pass.
"""
import sys
from collections import defaultdict


def catenary_of_semigroup(a, b, c, N, sparse_T=14):
    """c(n) for all n <= N via incremental factorization-set DP and
    bottleneck spanning tree (sparse Kruskal with bucketing)."""
    Z = {0: {(0, 0, 0)}}
    best, bestn = 0, None
    hist = []
    for n in range(1, N + 1):
        cur = set()
        for gi, i in ((a, 0), (b, 1), (c, 2)):
            for z in Z.get(n - gi, ()):
                cur.add(z[:i] + (z[i] + 1,) + z[i + 1:])
        Z[n] = cur
        if len(cur) < 2:
            hist.append(None)
            continue
        pts = list(cur)
        idx = {z: i for i, z in enumerate(pts)}
        parent = list(range(len(pts)))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        edges = []
        buckets = defaultdict(list)
        B = sparse_T + 1
        for z in pts:
            buckets[tuple(v // B for v in z)].append(z)
        for z in pts:
            bx = tuple(v // B for v in z)
            for db in ((0, 0, 0), (1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0),
                       (0, 0, 1), (0, 0, -1), (1, 1, 0), (1, -1, 0), (-1, 1, 0),
                       (-1, -1, 0), (1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1),
                       (0, 1, 1), (0, 1, -1), (0, -1, 1), (0, -1, -1), (1, 1, 1),
                       (1, 1, -1), (1, -1, 1), (-1, 1, 1), (1, -1, -1), (-1, 1, -1),
                       (-1, -1, 1), (-1, -1, -1)):
                for z2 in buckets.get(tuple(bv + dv for bv, dv in zip(bx, db)), ()):
                    if z2 > z:
                        d = max(abs(p - q) for p, q in zip(z, z2))
                        if d <= sparse_T:
                            edges.append((d, z, z2))
        edges.sort()
        comps = len(pts)
        maxedge = 0
        for d, z, z2 in edges:
            ri, rj = find(idx[z]), find(idx[z2])
            if ri != rj:
                parent[ri] = rj
                comps -= 1
                maxedge = max(maxedge, d)
                if comps == 1:
                    break
        cn = maxedge if comps == 1 else sparse_T + 1
        hist.append(cn)
        if cn > best:
            best, bestn = cn, n
    return best, bestn, hist


def factorizations(g, n):
    a, b, c = g
    out = set()
    for z1 in range(n // a + 1):
        for z2 in range((n - a * z1) // b + 1):
            R = n - a * z1 - b * z2
            if R % c == 0:
                out.add((z1, z2, R // c))
    return out


def supdist(z, z2):
    return max(abs(p - q) for p, q in zip(z, z2))


def main():
    cases = [((5, 6, 7), 4), ((5, 6, 25), 5), ((6, 7, 8), 4), ((6, 7, 35), 7)]
    for g, expected in cases:
        N = g[0] * g[1] * g[2] + max(g) + min(g)
        best, bestn, hist = catenary_of_semigroup(*g, N)
        tail = sorted({h for h in hist[N // 2:] if h is not None})
        print(f"c<{g[0]},{g[1]},{g[2]}> = {best} (attained at n = {bestn}); "
              f"stability window [{N // 2},{N}]: {tail}")
        assert best == expected, (g, best, expected)
        assert max(tail) == expected, "window must not exceed the max"

    # witness factorization sets exactly as kernel-certified in Main.lean
    assert factorizations((5, 6, 7), 30) == {(0, 5, 0), (1, 3, 1), (2, 1, 2), (6, 0, 0)}
    assert factorizations((5, 6, 7), 35) == {(0, 0, 5), (1, 5, 0), (2, 3, 1),
                                             (3, 1, 2), (7, 0, 0)}
    assert factorizations((5, 6, 7), 42) == {(0, 0, 6), (0, 7, 0), (1, 5, 1),
                                             (2, 3, 2), (3, 1, 3), (6, 2, 0), (7, 0, 1)}
    assert factorizations((5, 6, 25), 25) == {(0, 0, 1), (5, 0, 0)}
    assert factorizations((5, 6, 25), 30) == {(0, 5, 0), (1, 0, 1), (6, 0, 0)}
    print("witness factorization sets match the Lean kernel — OK")

    # c(30) = 4 for <5,6,7>: (6,0,0) isolated at t=3, connected at t=4
    Z30 = sorted(factorizations((5, 6, 7), 30))
    assert all(supdist((6, 0, 0), z) > 3 for z in Z30 if z != (6, 0, 0))
    assert supdist((6, 0, 0), (2, 1, 2)) == 4
    assert supdist((2, 1, 2), (1, 3, 1)) == 2
    assert supdist((1, 3, 1), (0, 5, 0)) == 2
    # c(25) = 5 for <5,6,25>: two-point set at sup-distance 5
    assert supdist((5, 0, 0), (0, 0, 1)) == 5
    print("witness distance tables (c(30)=4, c(25)=5) — OK")

    print("ALL CHECKS PASS — same min(a,b,c), different catenary degrees")
    return 0


if __name__ == "__main__":
    sys.exit(main())
