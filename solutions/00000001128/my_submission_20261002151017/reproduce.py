#!/usr/bin/env python3
"""
Reproduction script for the disproof of TLMC conjecture 00000001128.

Conjecture (verbatim): "Definition: M(w,j) is the maximal monomial coefficient in the
degree-j part of the Schubert polynomial S_w. Conjecture: M(w,j) equals
min(j, l(w), ceil(l(w)/2))! times a lattice-path count C(w), ..."

Counterexample: w = 321 in S_3. We recompute S_321 exactly (two independent ways),
extract M(321,3) = 1, note the conjectured factor is min(3,3,2)! = 2, and observe that
2 does not divide 1, so the conjecture would force the lattice-path count
C(321) = 1/2 -- not an integer. Falsified.

Run: python3 reproduce.py   (exits 0 with FALSIFIED, asserts everything along the way)
"""
from fractions import Fraction
from itertools import combinations
from math import ceil, factorial
from collections import defaultdict


def inv(w):
    """Length / inversion count of permutation w given in one-line notation."""
    return sum(1 for i in range(len(w)) for j in range(i + 1, len(w)) if w[i] > w[j])


def lis(w):
    """Longest increasing subsequence length."""
    best = [1] * len(w)
    for i in range(len(w)):
        for k in range(i):
            if w[k] < w[i]:
                best[i] = max(best[i], best[k] + 1)
    return max(best)


# ---------------------------------------------------------------------------
# Method 1: down-transition recurrence
#   S_id = 1,   S_w = sum over i with l(w t_i) < l(w) of  x_i * S_{w t_i}
# Polynomial = dict {exponent tuple (e_1,...,e_n): integer coefficient}.
# ---------------------------------------------------------------------------
def schubert(w):
    w = tuple(w)
    n = len(w)
    memo = {}

    def rec(v):
        if v in memo:
            return memo[v]
        if all(v[i] < v[i + 1] for i in range(n - 1)):  # identity
            memo[v] = {tuple([0] * n): 1}
            return memo[v]
        res = defaultdict(int)
        for i in range(n - 1):
            if v[i] > v[i + 1]:
                u = list(v)
                u[i], u[i + 1] = u[i + 1], u[i]
                for mono, c in rec(tuple(u)).items():
                    e = list(mono)
                    e[i] += 1
                    res[tuple(e)] += c
        memo[v] = dict(res)
        return memo[v]

    return rec(w)


# ---------------------------------------------------------------------------
# Method 2 (independent): top Schubert polynomial product formula
#   S_{w0, S_n} = prod_{1 <= i < j <= n} (x_i + x_{i+1} + ... + x_{j-1})
# ---------------------------------------------------------------------------
def schubert_w0(n):
    poly = defaultdict(int)
    poly[tuple([0] * n)] = 1
    for i, j in combinations(range(1, n + 1), 2):  # pairs (i, j), 1-indexed
        new = defaultdict(int)
        for mono, c in poly.items():
            for s in range(i - 1, j - 1):  # x_{i} + ... + x_{j-1}, 0-indexed shift
                e = list(mono)
                e[s] += 1
                new[tuple(e)] += c
        poly = new
    return dict(poly)


def deg_part(poly, j):
    return {m: c for m, c in poly.items() if sum(m) == j}


def max_coeff(poly):
    return max(poly.values())


def main():
    w = (3, 2, 1)
    j = 3

    l = inv(w)
    lis_len = lis(w)
    print(f"w = {w}  (one-line notation)")
    print(f"l(w) = inv(321) = {l}")
    print(f"LIS(321) = {lis_len}")
    assert l == 3

    p1 = schubert(w)
    p2 = schubert_w0(3)
    print(f"S_321 via down-transition recurrence : {dict(sorted(p1.items()))}")
    print(f"S_321 via w0 product formula         : {dict(sorted(p2.items()))}")
    assert p1 == p2, "the two independent computations must agree"

    assert all(sum(m) == j for m in p1), "S_321 is homogeneous of degree 3"
    part = deg_part(p1, j)
    print(f"degree-{j} part: {part}  (whole polynomial, homogeneous)")

    M = max_coeff(part)
    print(f"M(321, {j}) = max monomial coefficient = {M}")
    assert M == 1

    k = min(j, l, ceil(l / 2))
    print(f"min(j, l(w), ceil(l(w)/2)) = min({j}, {l}, {ceil(l / 2)}) = {k}")
    print(f"k! = {factorial(k)}")
    assert (k, factorial(k)) == (2, 2)

    C = Fraction(M, factorial(k))
    print(f"conjecture would force C(321) = M / k! = {C}")
    assert C.denominator != 1, "C is an integer: conjecture would NOT be falsified here"
    print(f"C(321) = {C} is not a non-negative integer -> not a lattice-path count")

    print()
    print("FALSIFIED: conjecture 00000001128 fails at w = 321, j = 3 "
          "(M = 1, k! = 2, 2 does not divide 1).")


if __name__ == "__main__":
    main()
