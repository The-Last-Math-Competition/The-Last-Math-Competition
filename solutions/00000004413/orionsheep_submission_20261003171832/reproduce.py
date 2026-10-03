#!/usr/bin/env python3
"""Refutation check for conjecture 00000004413.

Conjecture: in any bounded-degree graph limit (degree bound d), the measure
of cycles of length l is at most (d-1)^l / (2l), attained by the d-regular
tree limit.

Counterexample: the triangle K3, viewed as the graphing on the 3-element
probability space, has degree bound d = 2 and its number of undirected
3-cycles is 1. The claimed bound is (2-1)^3 / (2*3) = 1/6 < 1.

Moreover the d-regular tree contains NO cycles at all, so its cycle measure
is 0 -- it cannot attain the positive bound (d-1)^l/(2l); the claimed
expression is actually the *expected* cycle count of a random d-regular
graph (Bollobas/Wormald), a typical value rather than an upper bound.
"""
from fractions import Fraction
from itertools import combinations, permutations

def brute_cycles(adj, l):
    """Number of distinct undirected cycles of length l in a simple graph."""
    n = len(adj)
    def edges_of(cyc):
        return frozenset(
            frozenset((cyc[i], cyc[(i + 1) % l])) for i in range(l)
        )
    seen = set()
    for perm in permutations(range(n), l):
        if all(adj[perm[i]][perm[(i + 1) % l]] for i in range(l)):
            seen.add(edges_of(perm))
    return len(seen)

def claimed_bound(d, l):
    return Fraction((d - 1) ** l, 2 * l)

# --- K3 ---
K3 = [[False if i == j else True for j in range(3)] for i in range(3)]
deg = [sum(row) for row in K3]
assert max(deg) == 2, deg
c3 = brute_cycles(K3, 3)
b = claimed_bound(2, 3)
print(f"K3: degree bound d=2, cycles of length 3 = {c3}")
print(f"claimed upper bound (d-1)^l/(2l) = 1^3/6 = {b} = {float(b):.4f}")
assert Fraction(c3, 1) > b, "refutation failed"
print(f"VIOLATION: {c3} > {b}  -- bound fails on the simplest bounded-degree graph")

# --- d-regular tree: cycle count is 0, so it can never ATTAIN the bound ---
# The infinite d-regular tree has no cycles; locally-tree-like limits have
# vanishing cycle density. Hence the bound is never "attained" by trees.
for d in (2, 3, 4):
    for l in (3, 4, 5):
        tree_count = 0  # a tree has no cycles
        assert Fraction(tree_count) < claimed_bound(d, l)
print("Tree check: d-regular tree has cycle measure 0 < (d-1)^l/(2l);")
print("the bound is NOT attained by trees -- the optimality claim is false too.")

# --- context: what (d-1)^l/(2l) really is ---
print("\nContext: (d-1)^l/(2l) is the mean of the Poisson limit for the number")
print("of l-cycles in a uniformly random d-regular graph (Bollobas/Wormald).")
print("It is a typical/expected value, not a universal upper bound.")

print("\nVERDICT:REFUTABLE")
