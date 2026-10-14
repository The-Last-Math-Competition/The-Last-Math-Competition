#!/usr/bin/env python3
"""Independent exact checks. This program is evidence, not the Lean proof."""
from fractions import Fraction
from itertools import combinations, product
from collections import defaultdict
import json


def incidence(n, edges):
    a = [[Fraction(0) for _ in edges] for _ in range(n)]
    for j, (u, v) in enumerate(edges):
        a[u][j] -= 1
        a[v][j] += 1
    return a


def rank(a):
    a = [row[:] for row in a]
    if not a:
        return 0
    n, m, r = len(a), len(a[0]), 0
    for c in range(m):
        p = next((i for i in range(r, n) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        pivot = a[r][c]
        a[r] = [x / pivot for x in a[r]]
        for i in range(n):
            if i != r:
                q = a[i][c]
                a[i] = [x - q * y for x, y in zip(a[i], a[r])]
        r += 1
        if r == n:
            break
    return r


def chromatic(n, edges):
    for k in range(1, n + 1):
        for coloring in product(range(k), repeat=n):
            if all(coloring[u] != coloring[v] for u, v in edges):
                return k
    raise AssertionError('Every n-vertex graph is n-colorable')


def inspect(n, edges):
    b = incidence(n, edges)
    r = rank(b)
    return {'vertices': n, 'oriented_edges': edges,
            'incidence_matrix': [[int(x) for x in row] for row in b],
            'rank_over_Q': r, 'kernel_dimension_over_Q': len(edges) - r,
            'chromatic_number_exhaustive': chromatic(n, edges)}


def connected(n, edges):
    seen = {0}
    while True:
        nxt = seen | {v for u, v in edges if u in seen} | {u for u, v in edges if v in seen}
        if nxt == seen:
            return len(seen) == n
        seen = nxt


segment = inspect(2, [(0, 1)])
square = inspect(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
assert segment['kernel_dimension_over_Q'] == 0
assert square['kernel_dimension_over_Q'] == 1
assert segment['chromatic_number_exhaustive'] == square['chromatic_number_exhaustive'] == 2

counts = defaultdict(int)
values = defaultdict(set)
for n in range(1, 6):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        edges = [e for i, e in enumerate(pairs) if (mask >> i) & 1]
        counts[n] += 1
        if connected(n, edges):
            chi = chromatic(n, edges)
            beta = len(edges) - rank(incidence(n, edges))
            values[chi].add(beta)

result = {
    'scope': 'Independent exact arithmetic and finite enumeration; not a proof dependency',
    'witnesses': {'K2': segment, 'C4': square},
    'all_labeled_simple_graphs_checked_by_order': dict(counts),
    'total_graphs_checked': sum(counts.values()),
    'connected_graph_first_Betti_values_by_chromatic_number': {
        k: sorted(v) for k, v in sorted(values.items())},
}
print(json.dumps(result, indent=2))
