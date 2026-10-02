#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000003730.

Scans ALL 1024 graphs on 5 vertices (numpy eigenvalues):
  - energy of K5 = 8 (the maximum);
  - complete bipartite graphs on 5 vertices have energy <= 2*sqrt(6) ≈ 4.899;
  - so the maximum energy is NOT attained by a complete bipartite graph.
Exit 0 iff all checks pass.
"""
import sys
import itertools
import numpy as np


def energy(edges, n=5):
    A = np.zeros((n, n))
    for a, b in edges:
        A[a][b] = A[b][a] = 1.0
    return float(np.abs(np.linalg.eigvalsh(A)).sum())


def main():
    n = 5
    all_pairs = list(itertools.combinations(range(n), 2))
    best = -1.0
    best_edges = None
    bip_best = -1.0
    for mask in range(2 ** len(all_pairs)):
        edges = [all_pairs[i] for i in range(len(all_pairs)) if mask >> i & 1]
        e = energy(edges, n)
        if e > best:
            best, best_edges = e, edges
        # bipartite check: 2-colorable
        color = {}
        bip = True
        for start in range(n):
            if start in color:
                continue
            color[start] = 0
            stack = [start]
            while stack:
                u = stack.pop()
                for a, b in edges:
                    if a == u:
                        v = b
                    elif b == u:
                        v = a
                    else:
                        continue
                    if v not in color:
                        color[v] = 1 - color[u]
                        stack.append(v)
                    elif color[v] == color[u]:
                        bip = False
        if bip:
            bip_best = max(bip_best, e)  # (context only: all bipartite graphs)
    print(f"max energy over all graphs on 5 vertices: {best:.4f} "
          f"(edges = {len(best_edges)})")
    # complete bipartite graphs K_{m,n}, m+n=5
    cb_best = -1.0
    for m in range(1, 5):
        nn = 5 - m
        e = 2 * (m * nn) ** 0.5
        cb_best = max(cb_best, e)
        print(f"  K_{m},{nn}: energy 2*sqrt({m}*{nn}) = {e:.4f}")
    assert abs(best - 8) < 1e-6
    assert len(best_edges) == 10  # K5
    assert abs(cb_best - 2 * 6 ** 0.5) < 1e-6
    assert best > cb_best
    print("ALL CHECKS PASS — K5 energy 8 > best complete bipartite 2*sqrt(6)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
