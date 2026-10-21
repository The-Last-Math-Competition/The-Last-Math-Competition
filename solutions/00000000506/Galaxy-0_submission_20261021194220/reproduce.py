#!/usr/bin/env python3
"""Supplemental finite tests. The universal result is proved separately in Lean."""
from itertools import product
import json

ZERO = frozenset()
ONE = frozenset({(0, 0)})
X = frozenset({(1, 0)})
Y = frozenset({(0, 1)})

def add(p, q):
    return p ^ q

def mul(p, q):
    result = set()
    for a, b in p:
        for c, d in q:
            term = (a + c, b + d)
            if term in result:
                result.remove(term)
            else:
                result.add(term)
    return frozenset(result)

def polys(degree):
    monomials = [(i, j) for i in range(degree + 1)
                 for j in range(degree + 1 - i)]
    return [frozenset(m for m, bit in zip(monomials, bits) if bit)
            for bits in product((0, 1), repeat=len(monomials))]

def koszul(h):
    return mul(Y, h), mul(X, h)

def residual(p):
    return (0, 0) in p

def kernel_pair(a, b):
    return add(mul(X, a), mul(Y, b)) == ZERO

def main():
    small = polys(2)
    kernel = {(a, b) for a in small for b in small if kernel_pair(a, b)}
    expected = {koszul(h) for h in polys(1)}
    assert kernel == expected
    for p in small:
        assert add(p, p) == ZERO
        assert mul(ONE, p) == p
        for q in small:
            assert mul(p, q) == mul(q, p)
            assert residual(mul(p, q)) == (residual(p) and residual(q))
            for r in [ZERO, ONE, X, Y, add(X, Y)]:
                assert mul(mul(p, q), r) == mul(p, mul(q, r))
                assert mul(p, add(q, r)) == add(mul(p, q), mul(p, r))
    generator = koszul(ONE)
    assert generator == (Y, X)
    assert kernel_pair(*generator)
    assert residual(ONE)
    assert all(i + j + 1 == 2 for p in generator for i, j in p)
    assert {i + j + 2 for i, j in ONE} == {2}
    result = {
        "status": "PASS",
        "coefficient_field": "F_2",
        "ring": "F_2[X,Y]",
        "ideal_generators": ["X", "Y"],
        "syzygy_generator": ["Y", "X"],
        "minimal_resolution": "0 -> R(-2) -> R(-1)^2 -> (X,Y) -> 0",
        "first_betti_support": [2],
        "polynomials_total_degree_at_most_2": len(small),
        "exhaustive_pairs_checked": len(small) ** 2,
        "kernel_pairs_found": len(kernel),
        "ring_associativity_and_distributivity_cases": len(small) ** 2 * 5,
        "scope": "finite diagnostic checks only; the Lean proof is universal"
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
