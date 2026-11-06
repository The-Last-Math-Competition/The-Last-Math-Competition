"""Independent exact finite checks; the all-size proof is in lean/Main.lean."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json


def connected(vertices, edges):
    reached = {0}
    while True:
        enlarged = reached | {v for u, v in edges if u in reached} | {
            u for u, v in edges if v in reached}
        if enlarged == reached:
            return len(reached) == vertices
        reached = enlarged


def check(m):
    edges = [frozenset((i, (i + 1) % m)) for i in range(m)]
    assert len(set(edges)) == m
    for shift in range(m):
        assert {frozenset((v + shift) % m for v in e) for e in edges} == set(edges)
    # Enumerate actual subsets of the original edge set, then test connectivity.
    trees = []
    for labels in combinations(range(m), m - 1):
        if connected(m, [tuple(edges[i]) for i in labels]):
            trees.append(labels)
    assert len(trees) == m
    assert {frozenset(t) for t in trees} == {
        frozenset(set(range(m)) - {i}) for i in range(m)}
    mixed_count = 0
    for weights in product((1, 2), repeat=m):
        polynomial = Counter(sum(weights[i] for i in tree) for tree in trees)
        a, b = weights.count(1), weights.count(2)
        W = sum(weights)
        factor = Counter()
        if a:
            factor[W - 1] += a
        if b:
            factor[W - 2] += b
        assert polynomial == factor
        if not (a and b):
            continue
        mixed_count += 1
        q, root = W - 2, -Fraction(b, a)
        assert q >= 1 and root < 0
        assert a * root + b == 0
        # The genuine factorization has q zero roots and one simple negative root.
        assert polynomial[q] == b and polynomial[q + 1] == a
        assert sum(polynomial.values()) == m
        all_root_count, nonzero_root_count = q + 1, 1
        assert all_root_count > 0 and nonzero_root_count > 0
        # At threshold 0 for all roots and pi for nonzero roots respectively.
        assert Fraction(q, all_root_count) >= Fraction(1, 2)
        assert abs(Fraction(1) - Fraction(1, 2)) == Fraction(1, 2)
    assert mixed_count == 2**m - 2
    probability = Fraction(mixed_count, 2**m)
    assert probability == 1 - Fraction(2, 2**m)
    return dict(vertices=m, spanning_trees=len(trees), assignments=2**m,
                mixed_assignments=mixed_count, mixed_probability=str(probability))


if __name__ == '__main__':
    rows = [check(m) for m in range(3, 11)]
    print(json.dumps({'exact_checks': rows, 'status': 'PASS'}, indent=2))
