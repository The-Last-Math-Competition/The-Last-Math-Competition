#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000003479.

1. Deterministic counting bound: a harmonious coloring of an m-edge
   graph with h colors needs 2m <= h(h-1), i.e. h >= sqrt(2m).
2. Anchor at n = 1000, p = 1/2: typical m >= n^2/6 forces h >= 578,
   while the claimed law gives sqrt(n*p) = sqrt(500) < 23.
3. Monte-Carlo: G(1000, 1/2) essentially always has m >= n^2/6.
Exit 0 iff all checks pass.
"""
import sys
import random


def main():
    # (1) counting bound: h(h-1) >= 2m => h >= ceil((1+sqrt(1+8m))/2)
    def h_lower(pair_bound):
        h = 1
        while h * (h - 1) < pair_bound:
            h += 1
        return h

    # typical: m >= n^2/6 = 166667, so 2m >= 333334 = the pair bound
    assert h_lower(333334) == 578
    print(f"counting bound: 2m >= 333334 forces h >= {h_lower(333334)}")
    assert 577 * 576 == 332352 < 333334 <= 578 * 577

    # claimed value at n = 1000, p = 1/2
    claimed = (1000 * 0.5) ** 0.5
    print(f"claimed law value sqrt(n*p) = sqrt(500) = {claimed:.2f} < 23")
    assert 23 * 23 < 333333
    assert 578 > 23 * 25

    # (2) Monte-Carlo: typical edge count of G(1000, 1/2)
    random.seed(0)
    n, p = 1000, 0.5
    lows = 0
    trials = 200
    for _ in range(trials):
        m = sum(1 for i in range(n) for j in range(i + 1, n)
                if random.random() < p)
        if m < n * n // 6:
            lows += 1
    print(f"G(1000,1/2): m < n^2/6 in {lows}/{trials} samples "
          f"(n^2/6 = {n * n // 6})")
    assert lows <= 2  # Chernoff: w.h.p. m >= n^2/6

    print("ALL CHECKS PASS — claimed sqrt(n*p) law fails by a factor of > 25")
    return 0


if __name__ == "__main__":
    sys.exit(main())
