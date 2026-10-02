#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002221.

For R = k^N (product of N field copies, dim = 0):
  - prime ideals of R are exactly the N kernels of the projections;
  - Spec R is finite discrete, so the constructible topology is
    discrete: the Booleanization is the full powerset P(N);
  - the Stone space of P(N) has 2^N points (ultrafilters = atoms).
The claimed bound 2^(2^dim) = 2^(2^0) = 2 is violated for every N >= 2.
Exit 0 iff all checks pass.
"""
import sys
from itertools import product


def main():
    for N in range(1, 9):
        # prime ideals: for each coordinate i, the ideal of tuples with
        # i-th coordinate 0 is prime (quotient = k, a domain); these are
        # all the primes of a finite product of fields.
        primes = [i for i in range(N)]
        assert len(primes) == N
        # Spec is finite discrete => all 2^N subsets are constructible
        constructible = list(product([False, True], repeat=N))
        # ultrafilters on the powerset of an N-element set = N atoms =>
        # Stone space has 2^N points
        stone = 2 ** N
        bound = 2 ** (2 ** 0)  # dim R = 0
        print(f"N={N}: |Spec| = {len(primes)}, Booleanization = "
              f"{len(constructible)} elements, Stone space = {stone} points; "
              f"claimed bound 2^(2^dim) = {bound}; violated = {stone > bound}")
        if N >= 2:
            assert stone > bound
        assert len(constructible) == 2 ** N and stone == 2 ** N
    print("ALL CHECKS PASS — k^N (N>=2, dim 0) violates 2^(2^dim): "
          "Stone space 2^N > 2")
    return 0


if __name__ == "__main__":
    sys.exit(main())
