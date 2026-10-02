#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000003423.

1. P3 = 1-2-3: H(1->2) = 1 exactly (forced step).
2. Triangle (add edge {1,3}): solve the hitting-time system exactly:
   H1 = H3 = 2.
3. So adding the edge INCREASED H(1->2) from 1 to 2 > 1: the claimed
   monotone decrease is false. Confirmed by Monte-Carlo simulation.
Exit 0 iff all checks pass.
"""
import sys
from fractions import Fraction
import random


def solve_exact():
    # H1 = 1 + H3/2 ; H3 = 1 + H1/2  -> in halves: 2H1 = 2 + H3 ; 2H3 = 2 + H1
    # solve exactly with fractions
    # manual 2x2 solve: [[2, -1], [-1, 2]] * [H1, H3] = [2, 2]
    det = Fraction(2 * 2 - (-1) * (-1))
    h1 = Fraction(2 * 2 - (-1) * 2) / det
    h3 = Fraction(2 * 2 - (-1) * 2) / det
    return det, h1, h3


def main():
    # (1) path
    print("P3: from 1 the unique neighbor is 2, so H(1->2) = 1")
    H_path = 1

    # (2) triangle exact
    det, h1, h3 = solve_exact()
    print(f"triangle: det = {det}, H1 = H3 = {h1}")
    assert det == 3
    assert h1 == 2 and h3 == 2
    # substitution check
    assert h1 == 1 + h3 / 2 and h3 == 1 + h1 / 2
    assert h1 > H_path

    # (3) Monte-Carlo confirmation
    random.seed(0)
    steps = []
    for _ in range(20000):
        cur, n = 1, 0
        while cur != 2:
            cur = random.choice([x for x in (1, 2, 3) if x != cur])
            n += 1
        steps.append(n)
    avg = sum(steps) / len(steps)
    print(f"triangle walk simulation: mean H(1->2) ≈ {avg:.3f} (exact 2)")
    assert 1.8 < avg < 2.2

    print("ALL CHECKS PASS — adding edge {1,3} increased H(1->2) from 1 to 2")
    return 0


if __name__ == "__main__":
    sys.exit(main())
