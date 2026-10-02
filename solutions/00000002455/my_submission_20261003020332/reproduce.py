#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002455.

1. C(200,2) = 19900 unordered pairs; a DAG has at most one directed edge
   per unordered pair (both directions = a 2-cycle), so <= 19900 edges:
   finite, not aleph-0.
2. General identity 2*C(n,2) = n(n-1), checked for n = 1..200.
3. Brute force: every acyclic orientation of every subgraph of K_n
   (n <= 4) has at most C(n,2) edges, and the complete acyclic
   orientation (tournament) has exactly C(n,2).
Exit 0 iff all checks pass.
"""
import sys
from itertools import combinations


def is_acyclic(edges, n):
    """Kahn's algorithm."""
    indeg = [0] * n
    adj = [[] for _ in range(n)]
    for a, b in edges:
        indeg[b] += 1
        adj[a].append(b)
    q = [v for v in range(n) if indeg[v] == 0]
    seen = 0
    while q:
        u = q.pop()
        seen += 1
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)
    return seen == n


def main():
    # (1) pair count
    assert 200 * 199 // 2 == 19900
    print("C(200,2) = 19900: a 200-vertex DAG has <= 19900 edges (finite)")

    # (2) general identity
    for n in range(1, 201):
        assert 2 * (n * (n - 1) // 2) == n * (n - 1)
    print("2*C(n,2) = n(n-1) for n = 1..200")

    # (3) brute force acyclic orientations (n <= 4)
    for n in range(1, 5):
        pairs = list(combinations(range(n), 2))
        maxedges = 0
        for mask in range(2 ** len(pairs)):
            chosen = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
            if len(chosen) <= maxedges:
                continue
            # try both orientations for each chosen edge; check acyclic
            import itertools as it
            for orient in it.product([0, 1], repeat=len(chosen)):
                directed = [(a, b) if o == 0 else (b, a)
                            for (a, b), o in zip(chosen, orient)]
                if is_acyclic(directed, n):
                    maxedges = max(maxedges, len(directed))
        expected = n * (n - 1) // 2
        print(f"n = {n}: max DAG edges = {maxedges} (= C(n,2) = {expected})")
        assert maxedges == expected

    print("ALL CHECKS PASS — DAG edge count is bounded by C(n,2), finite; "
          "aleph-0 edges impossible")
    return 0


if __name__ == "__main__":
    sys.exit(main())
