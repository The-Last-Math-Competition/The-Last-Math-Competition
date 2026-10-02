#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002310.

Exhaustively computes the base size of the natural action of S_9 on
{0,...,8}: the minimal size of a point set whose pointwise stabilizer
is trivial. Expected: 8. Also exhibits, for every 7-subset, a nontrivial
permutation fixing it pointwise.
Exit 0 iff all checks pass.
"""
import sys
from itertools import permutations, combinations


def main():
    pts = list(range(9))
    perms = list(permutations(pts))   # all 362880 elements of S_9

    def fixes(p, subset):
        return all(p[x] == x for x in subset)

    # minimal base size: smallest k such that some k-subset has trivial
    # pointwise stabilizer
    for k in range(1, 10):
        good = any(
            sum(1 for p in perms if fixes(p, subset)) == 1
            for subset in combinations(range(9), k)
        )
        print(f"base size {k}: {'some' if good else 'no'} subset has trivial stabilizer")
        if good:
            assert k == 8, f"expected minimal base 8, got {k}"
            break
    assert k == 8

    # every 7-subset has a nontrivial pointwise stabilizer
    for subset in combinations(range(9), 7):
        rest = [x for x in range(9) if x not in subset]
        assert len(rest) == 2
        a, b = rest
        p = list(range(9))
        p[a], p[b] = b, a
        p = tuple(p)
        assert fixes(p, subset) and p != tuple(range(9))
    print("every 7-subset has a nontrivial pointwise stabilizer (a transposition)")

    print("ALL CHECKS PASS — b(S_9, natural action) = 8 > 7")
    return 0


if __name__ == "__main__":
    sys.exit(main())
