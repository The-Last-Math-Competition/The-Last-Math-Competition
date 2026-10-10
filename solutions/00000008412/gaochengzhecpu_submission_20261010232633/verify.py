"""Exact discovery and independent enumeration of the submitted witness.

Standard-library Python only. The formal proof does not trust this program.
"""
from collections import Counter
from itertools import combinations, product
import json

G = list(product(range(3), repeat=3))
ZERO = (0, 0, 0)
D = {
    (0, 0, 1), (0, 1, 0), (0, 1, 1), (0, 1, 2),
    (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1),
    (1, 2, 0), (1, 2, 2), (2, 0, 1), (2, 1, 2), (2, 2, 1),
}

def cycle(x):
    return x[1:] + x[:1]

def add(x, y):
    return tuple((a + b) % 3 for a, b in zip(x, y))

def sub(x, y):
    return tuple((a - b) % 3 for a, b in zip(x, y))

def neg(x):
    return tuple(-a % 3 for a in x)

def differences(S):
    return Counter(sub(x, y) for x in S for y in S)

def discover():
    """Search unions of coordinate-cycle orbits, as in the original discovery."""
    unseen = set(G) - {ZERO}
    orbits = []
    while unseen:
        x = min(unseen)
        orbit = {x, cycle(x), cycle(cycle(x))}
        unseen -= orbit
        orbits.append(orbit)
    fixed = [s for s in orbits if len(s) == 1]
    triples = [s for s in orbits if len(s) == 3]
    for one in fixed:
        for four in combinations(triples, 4):
            candidate = set().union(one, *four)
            if candidate & {neg(x) for x in candidate}:
                continue
            counts = differences(candidate)
            if all(counts[g] == 6 for g in G if g != ZERO):
                return candidate
    raise AssertionError('No witness found')

assert discover() == D
assert len(G) == 27 and len(D) == 13 and ZERO not in D
counts = differences(D)
assert counts[ZERO] == 13
assert all(counts[g] == 6 for g in G if g != ZERO)
assert {x for x in D if sub(x, (0, 0, 1)) in D} == {
    (0, 1, 0), (0, 1, 1), (0, 1, 2), (1, 0, 1), (1, 1, 1), (1, 2, 0),
}
assert {cycle(x) for x in G} == set(G)
assert all(cycle(add(x, y)) == add(cycle(x), cycle(y)) for x in G for y in G)
assert all(cycle(cycle(cycle(x))) == x for x in G)
assert {cycle(x) for x in D} == D
# Every integer scalar map on this exponent-three group reduces modulo three.
assert all(any(cycle(x) != tuple(n*a % 3 for a in x) for x in G) for n in range(3))
assert cycle((1, 0, 0)) == (0, 0, 1)
assert 27 % 2 == 1 and 27 % 16 != 0 and 27 % 32 != 0

print(json.dumps({
    'status': 'PASS', 'group_order': 27, 'parameters': [27, 13, 6],
    'D': sorted(D), 'all_26_nonzero_difference_counts': 6,
    'count_table': [[counts[(a, b, c)] for b, c in product(range(3), repeat=2)]
                    for a in range(3)],
    'coordinate_cycle_is_automorphism': True,
    'coordinate_cycle_fixes_D': True,
    'coordinate_cycle_is_nonnumerical': True,
}, indent=2))
