#!/usr/bin/env python3
"""Brute-force refutation of conjecture 00000001676.

The conjecture claims that the isoperimetric profile of the n x n torus grid
C_n [] C_n (the Cartesian product of two cycles) is

    ip(m) = ceil(4 * sqrt(n*m - m^2))     for all m <= n^2/2,

attained by diagonal cuts.

This script exhaustively computes the true minimum edge boundary over all
m-vertex subsets of C_n [] C_n for n = 3 and n = 4, prints the results next to
the conjectured formula, flags the part of the stated range where the radicand
n*m - m^2 is negative (so the formula is not even real), and reports PASS/FAIL.

Standard library only.
"""

import itertools
import math
import sys


# --------------------------------------------------------------------------
# Torus grid C_n [] C_n
# --------------------------------------------------------------------------

def torus_adjacency(n):
    """Adjacency bitmasks of C_n [] C_n; vertex (i, j) is index i*n + j.

    Vertices differ in exactly one coordinate, and coordinates are taken mod n
    (the wrap-around of the cycles).
    """
    adj = [0] * (n * n)
    for i in range(n):
        for j in range(n):
            v = i * n + j
            for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                w = ((i + di) % n) * n + ((j + dj) % n)
                adj[v] |= 1 << w
    return adj


def popcount(x):
    return bin(x).count("1")


def edge_boundary(mask, adj):
    """Number of edges with exactly one endpoint in the vertex set `mask`.

    Counting, for every v in the set, its neighbours outside the set counts
    each crossing edge exactly once.
    """
    total = 0
    m = mask
    while m:
        low = m & -m
        v = low.bit_length() - 1
        total += popcount(adj[v] & ~mask)
        m &= m - 1
    return total


def brute_force_min_boundary(n, m):
    """Minimum edge boundary over all m-subsets of the n*n torus vertices."""
    adj = torus_adjacency(n)
    best = None
    for comb in itertools.combinations(range(n * n), m):
        mask = 0
        for v in comb:
            mask |= 1 << v
        b = edge_boundary(mask, adj)
        if best is None or b < best:
            best = b
    return best


# --------------------------------------------------------------------------
# Conjectured formula
# --------------------------------------------------------------------------

def conjectured(n, m):
    """ceil(4 * sqrt(n*m - m^2)); None when the radicand is negative (not real)."""
    radicand = n * m - m * m
    if radicand < 0:
        return None
    return math.ceil(4.0 * math.sqrt(radicand))


def radicand(n, m):
    return n * m - m * m


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def main():
    ok = True
    findings = []

    for n in (3, 4):
        total = n * n
        mmax = total // 2  # m <= n^2/2, and n^2/2 is never an integer issue here
        print(f"=== C_{n} [] C_{n}  ({total} vertices, {total * 4 // 2} edges), "
              f"stated range m = 1..{mmax} (m <= n^2/2 = {total / 2}) ===")
        print(f"{'m':>3} | {'true ip(m)':>10} | {'formula':>9} | {'radicand':>9} | status")
        print("-" * 58)
        for m in range(1, mmax + 1):
            true_ip = brute_force_min_boundary(n, m)
            f = conjectured(n, m)
            rad = radicand(n, m)
            if f is None:
                status = "ILL-POSED (negative radicand, formula not real)"
                findings.append((n, m, true_ip, f, rad))
            elif f != true_ip:
                status = "WRONG (formula != true)"
                findings.append((n, m, true_ip, f, rad))
            else:
                status = "ok"
            fstr = "undefined" if f is None else str(f)
            print(f"{m:>3} | {true_ip:>10} | {fstr:>9} | {rad:>9} | {status}")
        print()

    # --- headline checks ---------------------------------------------------
    true_33 = brute_force_min_boundary(3, 3)
    form_33 = conjectured(3, 3)
    true_31 = brute_force_min_boundary(3, 1)
    form_31 = conjectured(3, 1)

    print("Headline counterexamples")
    print(f"  n = 3, m = 3 : true ip = {true_33}, formula = {form_33}"
          f"  -> {'PASS (mismatch)' if form_33 != true_33 else 'FAIL'}")
    print(f"  n = 3, m = 1 : true ip = {true_31}, formula = {form_31}"
          f"  -> {'PASS (mismatch)' if form_31 != true_31 else 'FAIL'}")
    print(f"  n = 3, m = 4 : radicand = {radicand(3, 4)} (< 0 while m <= n^2/2 = 4.5)"
          f"  -> {'PASS (ill-posed)' if radicand(3, 4) < 0 else 'FAIL'}")
    print()

    if not (true_33 == 6 and form_33 == 0 and form_33 != true_33):
        ok = False
    if not (true_31 == 4 and form_31 == 6):
        ok = False
    if not (radicand(3, 4) < 0):
        ok = False
    # the ill-posed range must actually occur inside the stated range
    if not any(n == 3 and m == 4 for (n, m, *_rest) in findings):
        ok = False

    n_wrong = sum(1 for (_n, _m, t, f, _r) in findings if f is not None)
    n_ill = sum(1 for (_n, _m, _t, f, _r) in findings if f is None)
    print(f"Summary: {n_wrong} defined values where the formula is wrong, "
          f"{n_ill} stated-range values where it is not real.")
    print("RESULT: PASS" if ok else "RESULT: FAIL")
    return 0


if __name__ == "__main__":
    sys.exit(main())
