#!/usr/bin/env python3
"""Independent graph-set enumeration; Python stdlib only; exact fractions."""
from itertools import combinations, permutations
from fractions import Fraction
from math import comb
from pathlib import Path
import json


def powerset(items):
    items = tuple(items)
    for k in range(len(items) + 1):
        for subset in combinations(items, k):
            yield frozenset(subset)


def edge(a, b):
    return tuple(sorted((a, b)))


def cycles(n, k):
    result = set()
    for seq in permutations(range(n), k):
        result.add(frozenset(edge(seq[i], seq[(i+1) % k]) for i in range(k)))
    assert len(result) == (comb(n, 3) if k == 3 else 3 * comb(n, 4))
    return result


def strict_balance(vertices, edges):
    checked = 0
    for vs in powerset(vertices):
        if not vs:
            continue
        available = {e for e in edges if set(e) <= vs}
        for es in powerset(available):
            if vs == vertices and es == edges:
                continue
            assert len(es) * len(vertices) < len(edges) * len(vs)
            checked += 1
    return checked

triangle = frozenset({(0, 1), (0, 2), (1, 2)})
square = frozenset({(0, 1), (1, 2), (2, 3), (0, 3)})
report = {'strict_balance_subgraphs_checked': {
    'C3': strict_balance(frozenset(range(3)), triangle),
    'C4': strict_balance(frozenset(range(4)), square)}, 'checks': []}
for n in (4, 5):
    edges = tuple(combinations(range(n), 2))
    ts, ss = cycles(n, 3), cycles(n, 4)
    ps = (Fraction(1, 4), Fraction(1, 2), Fraction(1))
    mass = {p: Fraction(0) for p in ps}
    et = mass.copy()
    es = mass.copy()
    histogram = [[0, 0, 0] for _ in range(len(edges) + 1)]
    for g in powerset(edges):
        nt = sum(c <= g for c in ts)
        ns = sum(c <= g for c in ss)
        m = len(g)
        histogram[m][0] += 1
        histogram[m][1] += nt
        histogram[m][2] += ns
        for p in ps:
            # Multiply the independent Bernoulli factors edge by edge.
            weight = Fraction(1)
            for e in edges:
                weight *= p if e in g else 1-p
            mass[p] += weight
            et[p] += nt * weight
            es[p] += ns * weight
    assert sum(row[0] for row in histogram) == 2**len(edges)
    if n == 4:
        assert histogram == [[1,0,0],[6,0,0],[15,0,0],[20,4,0],
                             [15,12,3],[6,12,6],[1,4,3]]
    for p in ps:
        assert mass[p] == 1
        assert et[p] == comb(n, 3) * p**3
        assert es[p] == 3 * comb(n, 4) * p**4
        assert et[p] / es[p] == Fraction(4, 3*(n-3)) / p
        report['checks'].append({'n': n, 'p': str(p), 'mass': str(mass[p]),
            'triangle_expectation': str(et[p]), 'square_expectation': str(es[p]),
            'ratio': str(et[p]/es[p])})
    report[f'histogram_n{n}'] = histogram
report['status'] = 'All exact independent graph-enumeration checks passed.'
path = Path(__file__).with_name('independent.json')
path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
