#!/usr/bin/env python3
"""Numerical reproduction for the rule-3 disproof of conjecture 00000001283.

Claim under test (from conjectures/00000001283.md):

    A nim-equation is an integer solution of x (+) y = x * y with x, y >= 1,
    where (+) is binary addition without carry.  Conjecture: the only solutions
    are (2,2) and (0,0); for all other candidate pairs with x, y > 2, the
    difference between the nim-sum and the product is a sign flip of a power
    of two.

This script refutes the sentence in three independent ways:

  1. (2,2) is NOT a solution: 2 (+) 2 = 0 while 2 * 2 = 4.
  2. There are actually NO solutions with x, y >= 1 at all; the only
     non-negative solution is (0,0) (which lies outside the stated domain).
  3. The "sign flip of a power of two" clause is false: over x, y in [3,499]
     only a tiny minority of pairs have (x (+) y) - x*y equal to +-2^j.

Standard library only.  Exit code 0 on success (OVERALL: PASS), 1 on failure.
"""

import sys

LIMIT = 500          # brute-force box 0 <= x, y < LIMIT
LO, HI = 3, 499      # box for the second clause: x, y in [LO, HI]


def nim_sum(x, y):
    """Binary addition without carry = bitwise XOR."""
    return x ^ y


def is_signed_power_of_two(d):
    """True iff d == +2^j or d == -2^j for some integer j >= 0."""
    a = abs(d)
    return a > 0 and (a & (a - 1)) == 0


def solutions_in_box(limit, lo=0):
    """All (x, y) with lo <= x, y < limit satisfying x (+) y = x * y."""
    return [(x, y) for x in range(lo, limit) for y in range(lo, limit)
            if nim_sum(x, y) == x * y]


def main():
    ok = True

    print("Conjecture 00000001283 -- solutions of x (+) y = x * y")
    print("=" * 66)

    # 1. The explicit counterexample (2,2).
    xs, ys = nim_sum(2, 2), 2 * 2
    print("[1] The pair (2,2) listed as a solution:")
    print(f"    2 (+) 2 = {xs},  2 * 2 = {ys}")
    if xs != ys:
        print(f"    PASS: {xs} != {ys}, so (2,2) is NOT a solution")
    else:
        ok = False
        print("    FAIL: (2,2) unexpectedly solves the equation")

    # 2. Full solution set over the box 0 <= x, y < LIMIT.
    sols = solutions_in_box(LIMIT)
    print(f"[2] Solution set over 0 <= x, y < {LIMIT}: {sols}")
    if sols == [(0, 0)]:
        print("    PASS: the only solution is (0,0), which is outside x, y >= 1")
    else:
        ok = False
        print(f"    FAIL: expected [(0,0)], got {sols}")

    # 2b. Restricted to the stated domain x, y >= 1 (and the x, y >= 2
    #     sub-case used in the proof).
    pos = solutions_in_box(LIMIT, lo=1)
    print(f"[2b] Solutions with 1 <= x, y < {LIMIT}: {pos}")
    if pos == []:
        print("    PASS: no solutions with x, y >= 1 (domain of the conjecture)")
    else:
        ok = False
        print(f"    FAIL: expected [], got {pos}")

    # 3. Second clause: count pairs whose difference is +-2^j.
    total = 0
    powers = 0
    violations = 0
    examples = []
    for x in range(LO, HI + 1):
        for y in range(LO, HI + 1):
            total += 1
            d = nim_sum(x, y) - x * y
            if is_signed_power_of_two(d):
                powers += 1
            else:
                violations += 1
                if len(examples) < 4:
                    examples.append((x, y, nim_sum(x, y), x * y, d))
    print(f"[3] Clause 2 over x, y in [{LO},{HI}] ({total} pairs)")
    print(f"    differences equal to +-2^j : {powers}")
    print(f"    violating that clause       : {violations}")
    print(f"    examples (x, y, x(+)y, x*y, diff): {examples}")
    expected_powers = 39
    if powers == expected_powers and violations == total - expected_powers:
        print(f"    PASS: {violations} pairs violate the clause "
              f"(only {powers} satisfy it)")
    else:
        ok = False
        print(f"    FAIL: expected {expected_powers} satisfying pairs, "
              f"got {powers}")

    # 3b. The concrete pair (3,3) used in the Lean/LaTeX proof.
    x = y = 3
    d = nim_sum(x, y) - x * y
    print(f"[3b] Concrete failure at (3,3): ({x} (+) {y}) - {x}*{y} = "
          f"{nim_sum(x, y)} - {x * y} = {d}")
    if d == -9 and not is_signed_power_of_two(d):
        print("    PASS: -9 is not +-2^j")
    else:
        ok = False
        print("    FAIL: -9 should not be a signed power of two")

    print("=" * 66)
    print("OVERALL:", "PASS" if ok else "FAIL")
    print("Verdict: conjecture 00000001283 is FALSE.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
