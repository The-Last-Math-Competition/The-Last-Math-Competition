#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000000030.

Under the definitions as given, "S subset [N] is intersective" means S
meets every nonempty subset of [N] -- i.e. S = [N] (singletons are
nonempty).  The instance N = 4, A = {1, 2} satisfies the size
hypothesis for every c >= 0 (|A| = 2 = 4^{1/2} >= 4^{1/2-c}) while its
square image {1, 4} misses the nonempty witness {3}: not intersective.
Exit 0 iff all checks pass.
"""
from itertools import combinations
import sys


def main():
    N = 4
    A = {1, 2}
    squares = {a * a for a in A}
    assert squares == {1, 4}
    # size hypothesis: |A| = 2 >= N^{1/2 - c} for every c >= 0
    import math
    for c in (0.0, 0.01, 0.1, 0.25, 0.49):
        bound = N ** (0.5 - c)
        assert len(A) >= bound - 1e-12, (c, bound)
    print("instance N=4, A={1,2}: |A| = 2 >= 4^(1/2-c) for all c >= 0 — OK")

    # intersectivity test: meets EVERY nonempty D subset [N]?
    universe = range(1, N + 1)
    all_nonempty_D = [set(c) for r in range(1, N + 1)
                      for c in combinations(universe, r)]
    meets_all = all(squares & D for D in all_nonempty_D)
    assert not meets_all
    witnesses = [D for D in all_nonempty_D if not (squares & D)]
    print(f"witnesses disjoint from {sorted(squares)}: "
          f"{[sorted(D) for D in witnesses]}")
    assert {3} in [set(w) for w in witnesses]

    # general principle: S meets every nonempty subset iff S = [N]
    for r in range(0, N + 1):
        for S in combinations(universe, r):
            Sset = set(S)
            meets = all(Sset & D for D in all_nonempty_D)
            assert meets == (Sset == set(universe)), Sset
    print("S meets every nonempty subset of [N] iff S = [N] — OK")

    # the singleton witness {3}: nonempty (density 1/4 > 0), disjoint
    assert {3} and not (squares & {3})
    print("witness {3}: nonempty, disjoint from the square image — OK")

    print("ALL CHECKS PASS — the sparse square image is not intersective")
    return 0


if __name__ == "__main__":
    sys.exit(main())
