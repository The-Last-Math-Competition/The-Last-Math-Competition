#!/usr/bin/env python3
"""Reproduction script for the disproof of conjecture 00000000427.

Standard library only.  It performs three independent checks:

(a) exact values of the conjectured formula

        F(n) = 2^{floor(n^2/4)} * prod_{i=1..n} (2i-1)!! / i!

    for n = 1..10, and whether each value is an integer;

(b) verification that the 2-adic valuation of F(n) is negative for every
    n in [4, 400];

(c) exhaustive enumeration of the order ideals of the product poset [n]^3
    for n = 1..4 -- i.e. plane partitions in the n-cube -- together with the
    count of those invariant under all permutations of the three coordinates.

The script prints a PASS/FAIL summary and exits with status 0 on success.
"""

from fractions import Fraction
from itertools import permutations
import sys


# --------------------------------------------------------------------------
# (a) exact rational values of F
# --------------------------------------------------------------------------

def odd_double_factorial(i):
    """(2i-1)!! = 1 * 3 * 5 * ... * (2i-1), with (2*0-1)!! = 1."""
    result = 1
    for j in range(1, i + 1):
        result *= 2 * j - 1
    return result


def factorial(i):
    result = 1
    for j in range(2, i + 1):
        result *= j
    return result


def F(n):
    """The conjectured formula as an exact Fraction."""
    value = Fraction(2 ** (n * n // 4), 1)
    for i in range(1, n + 1):
        value *= Fraction(odd_double_factorial(i), factorial(i))
    return value


def v2_int(x):
    """2-adic valuation of a non-zero integer."""
    x = abs(x)
    if x == 0:
        raise ValueError("v2 of zero is undefined")
    count = 0
    while x % 2 == 0:
        x //= 2
        count += 1
    return count


def v2_frac(q):
    """2-adic valuation of a non-zero Fraction."""
    return v2_int(q.numerator) - v2_int(q.denominator)


def v2_F_closed(n):
    """v2(F(n)) computed from the closed form floor(n^2/4) - sum_i v2(i!).

    This equals v2_frac(F(n)) by the valuation identity proved in main.tex;
    it avoids manipulating enormous exact factorials for large n.
    """
    D = 0
    for i in range(1, n + 1):
        power = 2
        while power <= i:
            D += i // power
            power *= 2
    return n * n // 4 - D


def check_values():
    print("=" * 70)
    print("(a) exact values of F(n) for n = 1..10")
    print("=" * 70)

    expected = {1: Fraction(1), 2: Fraction(3), 3: Fraction(15),
                4: Fraction(525, 2)}
    ok = True
    for n in range(1, 11):
        q = F(n)
        is_int = (q.denominator == 1)
        print("  F({:2d}) = {:<28} integer={}".format(n, str(q), is_int))
        if n in expected and q != expected[n]:
            ok = False
            print("      !! expected {}".format(expected[n]))

    if F(1) != 1 or F(2) != 3 or F(3) != 15:
        ok = False
        print("  !! F(1), F(2), F(3) should be 1, 3, 15")
    if F(4) != Fraction(525, 2):
        ok = False
        print("  !! F(4) should be 525/2")
    if F(4).denominator == 1:
        ok = False
        print("  !! F(4) must not be an integer")
    for n in range(4, 11):
        if F(n).denominator == 1:
            ok = False
            print("  !! F({}) must not be an integer".format(n))

    print("  [a] {}".format("PASS" if ok else "FAIL"))
    return ok


# --------------------------------------------------------------------------
# (b) v2(F(n)) < 0 for all n in [4, 400]
# --------------------------------------------------------------------------

def check_valuation():
    print()
    print("=" * 70)
    print("(b) v2(F(n)) < 0 for all n in [4, 400]")
    print("=" * 70)

    # Cross-validate the closed form against exact rationals on a range where
    # the exact computation is still cheap.
    ok = True
    for n in range(1, 31):
        if v2_F_closed(n) != v2_frac(F(n)):
            ok = False
            print("  !! closed form disagrees at n={}".format(n))
    if ok:
        print("  closed form v2(F(n)) cross-checked against exact Fraction "
              "for n = 1..30: OK")

    negative = [n for n in range(4, 401) if v2_F_closed(n) < 0]
    bad = [n for n in range(4, 401) if v2_F_closed(n) >= 0]
    print("  checked n = 4..400: {} values with v2 < 0, {} values with v2 >= 0"
          .format(len(negative), len(bad)))
    for n in (4, 5, 6, 7, 8):
        print("    v2(F({})) = {}".format(n, v2_F_closed(n)))
    if bad:
        ok = False
        print("  !! non-negative valuations at {}".format(bad))

    print("  [b] {}".format("PASS" if ok else "FAIL"))
    return ok


# --------------------------------------------------------------------------
# (c) exhaustive order-ideal enumeration for [n]^3
# --------------------------------------------------------------------------

def enumerate_ideals(n):
    """Return (total_ideals, invariant_ideals) for the poset [n]^3.

    Order ideals are enumerated exactly once by scanning a linear extension
    and deciding, for each element, whether to include it; an element may be
    included only when all of its predecessors are already included.  Each
    leaf of the decision tree is one order ideal.

    A subset of the cube is invariant under permuting the three coordinates
    iff, for every permutation orbit, it contains either all or none of the
    orbit; this is what makes the invariance test a finite orbit check.
    """
    elements = [(i, j, k) for i in range(n) for j in range(n) for k in range(n)]
    size = len(elements)
    index = {e: t for t, e in enumerate(elements)}

    # Immediate predecessors (coordinatewise cover) as bitmasks.
    predecessors = []
    for (i, j, k) in elements:
        mask = 0
        if i > 0:
            mask |= 1 << index[(i - 1, j, k)]
        if j > 0:
            mask |= 1 << index[(i, j - 1, k)]
        if k > 0:
            mask |= 1 << index[(i, j, k - 1)]
        predecessors.append(mask)

    # Orbits of the elements under the S_3 action permuting coordinates.
    seen = set()
    orbits = []
    for e in elements:
        if e in seen:
            continue
        orbit = set(permutations(e))
        seen |= orbit
        mask = 0
        for q in orbit:
            mask |= 1 << index[q]
        orbits.append(mask)

    counter = {"total": 0, "invariant": 0}

    def rec(t, ideal):
        if t == size:
            counter["total"] += 1
            for orbit in orbits:
                piece = ideal & orbit
                if piece != 0 and piece != orbit:
                    return
            counter["invariant"] += 1
            return
        # Exclude element t (allowed always).
        rec(t + 1, ideal)
        # Include element t (allowed iff all predecessors are in the ideal).
        if predecessors[t] & ~ideal == 0:
            rec(t + 1, ideal | (1 << t))

    rec(0, 0)
    return counter["total"], counter["invariant"]


def check_enumeration():
    print()
    print("=" * 70)
    print("(c) exhaustive order ideals of [n]^3, n = 1..4")
    print("=" * 70)

    expected_total = {1: 2, 2: 20, 3: 980, 4: 232848}
    expected_inv = {1: 2, 2: 5, 3: 16, 4: 66}
    ok = True
    for n in range(1, 5):
        total, inv = enumerate_ideals(n)
        good = (total == expected_total[n] and inv == expected_inv[n])
        ok = ok and good
        print("  n={}: MacMahon total = {:<7} S3-invariant = {:<3} {}".format(
            n, total, inv, "OK" if good else
            "!! expected {} / {}".format(expected_total[n], expected_inv[n])))
    print("  MacMahon totals 2, 20, 980, 232848 reproduced "
          "(validates the enumerator)")
    print("  invariant counts 2, 5, 16, 66 vs conjectured 1, 3, 15, 525/2")
    print("  [c] {}".format("PASS" if ok else "FAIL"))
    return ok


def main():
    a = check_values()
    b = check_valuation()
    c = check_enumeration()

    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print("  (a) exact values / non-integrality  : {}".format("PASS" if a else "FAIL"))
    print("  (b) v2(F(n)) < 0 for n in [4, 400]  : {}".format("PASS" if b else "FAIL"))
    print("  (c) order-ideal enumeration         : {}".format("PASS" if c else "FAIL"))
    overall = a and b and c
    print("  OVERALL                             : {}".format(
        "PASS" if overall else "FAIL"))
    print()
    print("Conclusion: F(4) = 525/2 is not an integer, and neither is F(n) for")
    print("any n >= 4; a count at t = 1 is a non-negative integer, so conjecture")
    print("00000000427 is FALSE.")
    return 0 if overall else 1


if __name__ == "__main__":
    sys.exit(main())
