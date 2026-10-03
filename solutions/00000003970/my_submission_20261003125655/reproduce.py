#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000003970 (REFUTED).

Conjecture: two graphs with identical connected-subgraph counts but
different adjacency spectra exist; the MINIMAL vertex number is 6
or 7.

Refutation: at n = 5 (induced reading) G1 = K3 + 2K1 and
G2 = P3 + K2 have identical connected-induced-subgraph counts
(5, 3, 1, 0, 0) but different spectra: x^2(x-2)(x+1)^2 vs
x(x^2-2)(x^2-1). And at n <= 4 exhaustive enumeration gives NO
separation at all: the minimal number is 5, not 6 or 7.
"""

import numpy as np
from itertools import combinations

def adjacency(G, n):
    A = np.zeros((n, n))
    for i, j in G:
        A[i][j] = A[j][i] = 1
    return A

def connected_counts(G, n):
    A = adjacency(G, n)
    counts = [0] * (n + 1)
    def connected(S):
        S = list(S)
        if len(S) <= 1:
            return True
        seen = {S[0]}; stack = [S[0]]
        while stack:
            u = stack.pop()
            for v in S:
                if A[u][v] and v not in seen:
                    seen.add(v); stack.append(v)
        return len(seen) == len(S)
    for k in range(1, n + 1):
        for S in combinations(range(n), k):
            if connected(S):
                counts[k] += 1
    return counts

# ---------- gate 1: the certified n = 5 pair ----------
G1 = [(0,1),(1,2),(0,2)]          # K3 + 2K1
G2 = [(0,1),(1,2),(3,4)]          # P3 + K2
c1, c2 = connected_counts(G1, 5), connected_counts(G2, 5)
assert c1 == c2 == [0, 5, 3, 1, 0, 0]
e1 = np.sort(np.linalg.eigvalsh(adjacency(G1, 5)))
e2 = np.sort(np.linalg.eigvalsh(adjacency(G2, 5)))
assert not np.allclose(e1, e2)
print("G1 = K3+2K1 and G2 = P3+K2 (n=5): identical counts", c1[1:],)
print("spectra:", e1, "vs", e2, "— different — OK")

# ---------- gate 2: no separation for n <= 4 (exhaustive) ----------
def has_separation(n):
    graphs = []
    pairs = list(combinations(range(n), 2))
    for mask in range(2 ** len(pairs)):
        G = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        A = adjacency(G, n)
        ev = tuple(np.round(np.sort(np.linalg.eigvalsh(A)), 9))
        cc = tuple(connected_counts(G, n))
        graphs.append((cc, ev))
    from collections import defaultdict
    by_counts = defaultdict(set)
    for cc, ev in graphs:
        by_counts[cc].add(ev)
    return any(len(evs) > 1 for evs in by_counts.values())

for n in (2, 3, 4):
    assert not has_separation(n)
    print(f"n = {n}: exhaustive over all 2^(n choose 2) graphs — NO separation — OK")

print("\nminimal vertex number = 5 (not 6 or 7) — conjecture REFUTED")
