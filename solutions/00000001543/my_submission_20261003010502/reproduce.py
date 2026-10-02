#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001543.

1. n equally spaced collinear points determine exactly n-1 distinct
   distances (checked by brute force for n = 2..300).
2. (n-1)^3 < n^4 for all n >= 2 in a wide range (the ratio fact).
3. For every C in 1..50, at n = 2*C^3: C^3 * (n-1)^3 < n^4, i.e. the
   collinear count n-1 is below (1/C) * n^(4/3) at that n -- the
   claimed lower bound fails for every reciprocal-integer constant.
Exit 0 iff all checks pass.
"""
import sys


def main():
    # (1) collinear distinct distances
    for n in range(2, 301):
        pts = list(range(1, n + 1))
        dists = {abs(x - y) for x in pts for y in pts if x != y}
        assert len(dists) == n - 1, (n, len(dists))
    print("collinear equally spaced: distinct distances = n - 1 for n = 2..300")

    # (2) ratio fact
    for n in range(2, 5000):
        assert (n - 1) ** 3 < n ** 4
    print("(n-1)^3 < n^4 for all n in [2, 5000)")

    # (3) the witnesses
    for C in range(1, 51):
        n = 2 * C ** 3
        assert n >= 2
        assert C ** 3 * (n - 1) ** 3 < n ** 4, (C, n)
        # equivalently: n - 1 < (1/C) * n^(4/3) at this n
        assert (n - 1) * C ** 3 < n ** 4
    print("witness n = 2*C^3 works for all C in 1..50: "
          "C^3*(n-1)^3 < n^4, i.e. n-1 < (1/C)*n^(4/3)")

    # ratio decay
    for n in (10, 100, 1000, 10000):
        print(f"  n={n}: (n-1)/n^(4/3) = {(n - 1) / n ** (4 / 3):.4f}")
    print("ALL CHECKS PASS — collinear points refute the uniform c*n^(4/3) bound")
    return 0


if __name__ == "__main__":
    sys.exit(main())
