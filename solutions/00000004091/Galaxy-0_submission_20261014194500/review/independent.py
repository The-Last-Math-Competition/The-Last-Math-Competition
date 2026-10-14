#!/usr/bin/env python3
"""Independent exact checks of TLMC 4091 graph witnesses.

These are supplemental tests, never a proof oracle for Lean or topology.
"""
from fractions import Fraction
from itertools import product


def chromatic_number(n, edges):
    for k in range(n + 1):
        for colors in product(range(k), repeat=n):
            if all(colors[a] != colors[b] for a, b in edges):
                return k, colors
    raise AssertionError("Every finite simple graph is n-colorable")


def incidence(n, edges):
    return [[Fraction(int(v == b) - int(v == a)) for a, b in edges]
            for v in range(n)]


def rank(matrix):
    a = [row[:] for row in matrix]
    r = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        coeff = a[r][col]
        a[r] = [x / coeff for x in a[r]]
        for i in range(len(a)):
            if i != r:
                coeff = a[i][col]
                a[i] = [x - coeff * y for x, y in zip(a[i], a[r])]
        r += 1
    return r


def is_connected(n, edges):
    seen = {0}
    while True:
        more = {b for a, b in edges if a in seen}
        more |= {a for a, b in edges if b in seen}
        if more <= seen:
            return len(seen) == n
        seen |= more


def main():
    graphs = [
        ("K2", 2, [(0, 1)], 0),
        ("C4", 4, [(0, 1), (1, 2), (2, 3), (3, 0)], 1),
    ]
    for name, n, edges, expected in graphs:
        assert all(0 <= a < n and 0 <= b < n and a != b for a, b in edges)
        assert len({frozenset(e) for e in edges}) == len(edges)
        assert is_connected(n, edges)
        chi, witness = chromatic_number(n, edges)
        assert chi == 2
        a = incidence(n, edges)
        boundary_rank = rank(a)
        cycle_rank = len(edges) - boundary_rank
        assert cycle_rank == expected
        assert cycle_rank == len(edges) - n + 1
        print(f"{name}: simple connected; chromatic minimum {chi}; coloring {witness}; "
              f"rational incidence rank {boundary_rank}; kernel dimension {cycle_rank}")
    print("PASS: same chromatic minimum, different exact rational cycle dimensions")


if __name__ == "__main__":
    main()
