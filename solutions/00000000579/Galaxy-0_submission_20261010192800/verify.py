#!/usr/bin/env python3
"""Independent exact arithmetic checks. Not used as an oracle by Lean."""
from itertools import product
from math import comb

MASKS = range(16)
EDGES = [(i, (i + 1) % 4) for i in range(4)]

def subset(a, b):
    return a & b == a

def components(s):
    parent = list(range(4))
    def find(v):
        while parent[v] != v:
            v = parent[v]
        return v
    for i, (u, v) in enumerate(EDGES):
        if s >> i & 1:
            parent[find(u)] = find(v)
    return len({find(v) for v in range(4)})

def rank(s):
    return 4 - components(s)

def dual_rank(s):
    return s.bit_count() + rank(15 ^ s) - rank(15)

def flat(r, a, b):
    return subset(a, b) and all(
        r(a | (1 << e)) > r(a)
        for e in range(4) if b >> e & 1 and not a >> e & 1)

def chi(r, a, b, i):
    return sum((-1) ** (s.bit_count() - a.bit_count())
               for s in MASKS if subset(a, s) and subset(s, b)
               and r(b) - r(s) == i)

def kl(r, a, b, i):
    if i == 0:
        return 1
    if i == 1 and r is rank and a == 0 and b == 15:
        return 2
    return 0

def rhs(r, a, b, i):
    return sum(chi(r, a, f, j) * kl(r, f, b, i - j)
               for f in MASKS if subset(a, f) and flat(r, f, b)
               for j in range(i + 1))

for s in MASKS:
    assert rank(s) == min(3, s.bit_count())
    assert dual_rank(s) == min(1, s.bit_count())
for r in (rank, dual_rank):
    for a, b in product(MASKS, repeat=2):
        assert r(a | b) + r(a & b) <= r(a) + r(b)
        if subset(a, b):
            assert r(a) <= r(b)
        if flat(r, a, b):
            for i in range(9):
                d = r(b) - r(a)
                lhs = kl(r, a, b, d - i) if i <= d else 0
                assert lhs == rhs(r, a, b, i), (r.__name__, a, b, i)
print('All 16 graphic and dual ranks and both matroid rank axioms checked.')
print('Every loopless interval recurrence checked through coefficient 8.')
print('Lean additionally proves all higher coefficients vanish symbolically.')

chromatic = [sum((-1) ** s.bit_count() for s in MASKS if components(s) == i)
             for i in range(5)]
assert chromatic == [0, -3, 6, -4, 1]
characteristic = [chi(rank, 0, 15, i) for i in range(4)]
assert characteristic == [-3, 6, -4, 1]
for colors in range(6):
    actual = sum(all(c[u] != c[v] for u, v in EDGES)
                 for c in product(range(colors), repeat=4))
    expected = sum(n * colors ** i for i, n in enumerate(chromatic))
    assert actual == expected
value = sum(n * (-1) ** i for i, n in enumerate(chromatic))
assert value == 14
assert sum(n * (-1) ** i for i, n in enumerate(characteristic)) == -14
assert 2 % 14 != 0
print('Chromatic coefficients:', chromatic)
print('Matroid characteristic coefficients:', characteristic)
print('Direct coloring counts agree for 0 through 5 colors.')
print('P_M(t) = 1 + 2t; P_dual(t) = 1; difference at 1 = 2; |chi(-1)| = 14.')
print('PASS: 14 does not divide 2.')
