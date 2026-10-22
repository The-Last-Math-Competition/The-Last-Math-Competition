"""Exact independent finite checks for the 9305 counterexample.

No external libraries or numerical approximations are used.  This verifier is
not an oracle for Lean: the arbitrary-graph and arbitrary-mixture arguments
are proved in Main.lean.
"""
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, permutations
import json


def graph(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v
        adj[u].add(v)
        adj[v].add(u)
    return adj


def ball(adj, root, radius):
    dist = {root: 0}
    queue = deque([root])
    while queue:
        u = queue.popleft()
        if dist[u] < radius:
            for v in adj[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    queue.append(v)
    return set(dist)


def canonical_rooted(adj, vertices, root):
    others = sorted(vertices - {root})
    forms = []
    for order_tail in permutations(others):
        order = (root,) + order_tail
        forms.append(tuple(int(order[j] in adj[order[i]])
                           for i in range(len(order))
                           for j in range(i + 1, len(order))))
    return len(vertices), min(forms)


P3 = graph(3, [(0, 1), (1, 2)])
PATTERNS = {canonical_rooted(P3, {0, 1, 2}, r) for r in range(3)}
assert len(PATTERNS) == 2  # endpoints have the same rooted isomorphism class
TARGET = Counter(canonical_rooted(P3, {0, 1, 2}, r) for r in range(3))
TARGET = {key: Fraction(count, 3) for key, count in TARGET.items()}
assert sorted(TARGET.values()) == [Fraction(1, 3), Fraction(2, 3)]


def obstruction(adj, root):
    vertices = ball(adj, root, 2)
    return len(vertices) == 3 and canonical_rooted(adj, vertices, root) in PATTERNS


checked_roots = 0
checked_obstructions = 0
checked_regular = 0
for n in range(1, 7):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        adj = graph(n, [edge for bit, edge in enumerate(pairs) if mask & (1 << bit)])
        regular = len({len(row) for row in adj}) == 1
        checked_regular += regular
        for root in range(n):
            checked_roots += 1
            if obstruction(adj, root):
                checked_obstructions += 1
                # Full degrees, not merely degrees within a truncated ball.
                assert any(len(adj[root]) != len(adj[v]) for v in adj[root])
                assert not regular

# A radius-two P3 ball does not identify the whole connected graph.
P4 = graph(4, [(0, 1), (1, 2), (2, 3)])
assert obstruction(P4, 0)
assert len(ball(P4, 0, 4)) == 4

for copies in range(1, 41):
    n = 3 * copies
    adj = graph(n, [(3*i, 3*i+1) for i in range(copies)]
                + [(3*i+1, 3*i+2) for i in range(copies)])
    counts = Counter()
    for root in range(n):
        component = ball(adj, root, n)
        assert len(component) == 3
        counts[canonical_rooted(adj, component, root)] += 1
        assert obstruction(adj, root)
    law = {key: Fraction(count, n) for key, count in counts.items()}
    assert law == TARGET

print(json.dumps({
    "status": "PASS",
    "exhaustive_graph_max_vertices": 6,
    "checked_roots": checked_roots,
    "checked_radius_two_obstructions": checked_obstructions,
    "checked_regular_graphs": checked_regular,
    "uniform_root_sequences_checked": 40,
    "endpoint_class_mass": "2/3",
    "middle_class_mass": "1/3",
    "warning_case_P4_endpoint": "checked: ball=P3 but component=P4",
}, indent=2))
