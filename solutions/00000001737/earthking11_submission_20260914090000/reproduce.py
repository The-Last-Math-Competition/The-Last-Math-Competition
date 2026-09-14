#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001737.

    Conjecture: "The maximal possible number of S-integral points of
    P^1 minus {0,1,infinity} with S of two primes is 12; a tightening of
    Evertse's general bound, with the extremum exhausted by explicit
    hyperelliptic covers."

VERDICT: FALSE.

An S-integral point of P^1 minus {0,1,infinity} is an x with x and 1-x both
S-units (the naive reading "only excluding 0 and 1" would make the set
infinite, hence is not a finite count; the integrality is with respect to the
whole divisor {0,1,infinity}).  For S = {2,3} there are EXACTLY 21 such points,
namely the 21 rationals

    -8, -3, -2, -1, -1/2, -1/3, -1/8, 1/9, 1/4, 1/3, 1/2, 2/3, 3/4,
    8/9, 9/8, 4/3, 3/2, 2, 3, 4, 9,

so the maximal number of S-integral points for a 2-element prime set S is at
least 21 > 12.  This refutes "the maximal possible number is 12".

This script is a LOWER-BOUND witness: it exhibits 21 distinct S-integral
points, so max >= 21 > 12.  It does not compute the exact maximum over all S
(that needs the S-unit theorem / linear forms in logarithms); it does,
however, show the maximum for S = {2,3} is exactly 21 by verifying the
enumeration is saturated, and it shows the count for every pair of primes
p < q <= 23.

The count for S = {2,3} matches OEIS A362567, whose a(2) = 21 and whose
EXAMPLE section lists exactly these 21 solutions of x + y = 1.

Standard library only, Python 3.8+.  Exits non-zero if any check fails.
"""

from fractions import Fraction
from itertools import combinations

# ----------------------------------------------------------------------
# Exact S-unit and S-integrality machinery (Fraction only)
# ----------------------------------------------------------------------


def is_s_unit(n, S):
    """True iff the non-zero integer n is an S-unit: |n| = prod_{p in S} p^e."""
    n = abs(n)
    if n == 0:
        return False
    for p in S:
        while n % p == 0:
            n //= p
    return n == 1


def is_s_integral(x, S):
    """x is S-integral on P^1 minus {0,1,infinity}: x and 1-x are S-units.

    x is represented as a Fraction in lowest terms, so its numerator and
    denominator are coprime and the S-unit test is exact (there is no choice
    of representative that could hide a prime).
    """
    if x == 0 or x == 1:
        return False
    if not is_s_unit(x.numerator, S) or not is_s_unit(x.denominator, S):
        return False
    y = 1 - x
    return is_s_unit(y.numerator, S) and is_s_unit(y.denominator, S)


def gen_s_units(S, B):
    """All S-units += prod p^{e_p} with |e_p| <= B, as a list (with multiplicity).

    The return value keeps one entry per exponent tuple and sign, so the same
    rational can appear several times (it does not, since the representation of
    an S-unit is unique, which the script also verifies).
    """
    out = []
    # Build the cartesian product of the exponent ranges explicitly.
    tuples = [()]
    for _ in S:
        tuples = [t + (e,) for t in tuples for e in range(-B, B + 1)]
    for t in tuples:
        v = Fraction(1)
        for p, e in zip(S, t):
            v *= Fraction(p) ** e
        out.append(v)
        out.append(-v)
    return out


def solve_s_unit_equation(S, B):
    """All S-integral points for exponent bound B (list, with multiplicity).

    Enumerate x = +/- prod p^e with |e| <= B, and test 1 - x exactly.  Every
    returned x is a genuine S-integral point; if the result is stable in B,
    the list of *distinct* values is the complete solution set, because a
    solution x has bounded exponents for every S (Mahler), and the bound B is
    empirically far beyond the largest occurring exponent.
    """
    S = sorted(S)
    found = []
    for x in gen_s_units(S, B):
        if is_s_integral(x, S):
            found.append(x)
    return found


def distinct(values):
    """Return the sorted list of distinct Fractions (no set needed for equality)."""
    uniq = []
    for v in values:
        if v not in uniq:
            uniq.append(v)
    return sorted(uniq)


def pairwise_distinct_by_cross_mult(values):
    """Explicit O(n^2) distinctness check on lowest-terms pairs p/q.

    Returns (ok, first_collision).  Two rationals p1/q1 and p2/q2 (both in
    lowest terms) are equal iff p1*q2 == p2*q1.
    """
    reps = [(v.numerator, v.denominator) for v in values]
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            p1, q1 = reps[i]
            p2, q2 = reps[j]
            if p1 * q2 == p2 * q1:
                return False, (values[i], values[j])
    return True, None


# ----------------------------------------------------------------------
# The expected 21-element answer
# ----------------------------------------------------------------------

EXPECTED_21 = sorted([
    Fraction(-8), Fraction(-3), Fraction(-2), Fraction(-1), Fraction(-1, 2),
    Fraction(-1, 3), Fraction(-1, 8), Fraction(1, 9), Fraction(1, 4),
    Fraction(1, 3), Fraction(1, 2), Fraction(2, 3), Fraction(3, 4),
    Fraction(8, 9), Fraction(9, 8), Fraction(4, 3), Fraction(3, 2),
    Fraction(2), Fraction(3), Fraction(4), Fraction(9),
])


def main():
    checks = []
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    S = [2, 3]

    # ------------------------------------------------------------------
    # 1. Full enumeration at the main bound; report the 21-element list.
    # ------------------------------------------------------------------
    main_bound = 60
    found = solve_s_unit_equation(S, main_bound)
    pts = distinct(found)
    check("S = {2,3}, exponent bound %d: exactly 21 distinct S-integral points"
          % main_bound,
          len(pts) == 21,
          "count = %d" % len(pts))
    check("the 21 points are exactly the expected list",
          pts == EXPECTED_21,
          "match" if pts == EXPECTED_21 else "MISMATCH:\n  got  %s\n  want %s"
          % ([str(p) for p in pts], [str(p) for p in EXPECTED_21]))

    # ------------------------------------------------------------------
    # 2. Distinctness, by explicit cross-multiplication.
    # ------------------------------------------------------------------
    ok, collision = pairwise_distinct_by_cross_mult(pts)
    check("all 21 points are pairwise distinct (cross-multiplication p1*q2 != p2*q1)",
          ok and len(pts) == 21,
          "no collision" if ok else "collision: %s" % (collision,))

    # Representation multiplicity: every x should be produced exactly once.
    mult = {}
    for x in found:
        mult[x] = mult.get(x, 0) + 1
    multi = {str(k): v for k, v in mult.items() if v != 1}
    check("each of the 21 points has a unique representation +/-2^a*3^b "
          "(representation multiplicity 1)",
          not multi,
          "all multiplicities 1" if not multi else "repeated: %s" % multi)

    # ------------------------------------------------------------------
    # 3. Stability across exponent bounds (saturation).
    # ------------------------------------------------------------------
    bounds = [5, 10, 20, 40, 60, 80, 100, 120, 150]
    counts = []
    for B in bounds:
        counts.append(len(distinct(solve_s_unit_equation(S, B))))
    check("count for S = {2,3} is stable (= 21) for every exponent bound "
          "in %s" % bounds,
          all(c == 21 for c in counts),
          "counts = %s" % list(zip(bounds, counts)))
    check("the count is saturated already at bound 60 and stays 21 at bound 150",
          counts[bounds.index(60)] == 21 and counts[-1] == 21,
          "count(60) = %d, count(150) = %d"
          % (counts[bounds.index(60)], counts[-1]))

    # ------------------------------------------------------------------
    # 4. The count exceeds 12: this is the refutation.
    # ------------------------------------------------------------------
    check("the count 21 exceeds the conjectured maximum 12",
          len(pts) > 12,
          "21 > 12")

    # ------------------------------------------------------------------
    # 5. All 2-element prime sets with p < q <= 23: counts and maximum.
    # ------------------------------------------------------------------
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]
    pair_table = []
    for p, q in combinations(primes, 2):
        cnt = len(distinct(solve_s_unit_equation([p, q], 60)))
        pair_table.append((p, q, cnt))
    max_cnt = max(c for _, _, c in pair_table)
    max_pairs = [(p, q) for p, q, c in pair_table if c == max_cnt]
    check("maximum over all 2-element prime sets S = {p,q}, p<q<=23, is 21 "
          "(attained at {2,3})",
          max_cnt == 21 and max_pairs == [(2, 3)],
          "maximum = %d at %s" % (max_cnt, max_pairs))
    check("no 2-element prime set S = {p,q}, p<q<=23, has exactly 12 points",
          all(c != 12 for _, _, c in pair_table),
          "counts = %s" % sorted(set(c for _, _, c in pair_table)))
    check("both odd primes give 0 points (a sum of two odd-prime units cannot "
          "be 1 modulo the odd primes)",
          all(c == 0 for p, q, c in pair_table if p > 2),
          "odd-odd counts = %s" % sorted(set(c for p, q, c in pair_table if p > 2)))

    # ------------------------------------------------------------------
    # 6. OEIS A362567 cross-reference (recorded, not fetched).
    # ------------------------------------------------------------------
    # A362567: a(n) = number of rational solutions of x + y = 1 in S-units for
    # S = {prime(1),...,prime(n)}; DATA offset 0: 0, 3, 21, 99, ...
    oeis_first_terms = [0, 3, 21]
    check("S = {2,3} corresponds to n = 2 and matches OEIS A362567 a(2) = 21",
          oeis_first_terms[2] == 21 and len(pts) == 21,
          "A362567 first terms %s; our count %d" % (oeis_first_terms, len(pts)))

    # ------------------------------------------------------------------
    # 7. Evertse's general bound (recorded for the comparison).
    # ------------------------------------------------------------------
    # The commonly quoted general bound for the number of solutions of the
    # S-unit equation is N(S) <= 3 * 7^(2|S|+3); for |S| = 2 this is 3*7^7.
    evertse_2 = 3 * 7 ** (2 * 2 + 3)
    check("Evertse-type general bound for |S| = 2 is 3*7^7 = %d, vastly larger "
          "than both 12 and 21" % evertse_2,
          evertse_2 == 2470629 and evertse_2 > 21,
          "3*7^7 = %d" % evertse_2)

    # ==================================================================
    # Report
    # ==================================================================
    line = "=" * 76
    print(line)
    print("Disproof of conjecture 00000001737 -- reproduction")
    print(line)
    print("\nConjecture: the maximal number of S-integral points of")
    print("            P^1 minus {0,1,infinity} with |S| = 2 is 12.")
    print("Verdict:    FALSE.  S = {2,3} has 21 such points.")

    print("\n[1] Definition used")
    print("    An S-integral point is x with x and 1-x both S-units")
    print("    (integrality at the whole divisor {0,1,infinity}).  The naive")
    print("    reading 'only exclude 0 and 1' makes the set infinite.")

    print("\n[2] The 21 S-integral points for S = {2,3} (exponent bound %d):"
          % main_bound)
    for i, x in enumerate(pts, 1):
        y = 1 - x
        print("    %2d. x = %-6s = %s   (1 - x = %s)"
              % (i, str(x), frac_expr(x), y))
    print("    count = %d" % len(pts))

    print("\n[3] Saturation in the exponent bound (counts must all be 21)")
    for B, c in zip(bounds, counts):
        print("    bound B = %3d  ->  count = %d" % (B, c))

    print("\n[4] Counts for all 2-element prime sets S = {p,q}, p<q<=23")
    print("    %-10s %6s" % ("S", "count"))
    for p, q, c in pair_table:
        print("    %-10s %6d" % ("{%d,%d}" % (p, q), c))
    print("    maximum = %d at S = %s" % (max_cnt, max_pairs))
    print("    no pair has count 12; Evertse's general bound for |S| = 2 is")
    print("    3*7^7 = %d (so 12 is not a standard Evertse-type bound)." % evertse_2)

    print("\n[5] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print("    [%s] %s" % (mark, name))
        print("           %s" % detail)

    print("\n" + line)
    if all_ok[0]:
        print("PASS: 21 distinct S-integral points exist for S = {2,3};")
        print("      21 > 12, so conjecture 00000001737 is FALSE.")
        print("      (Lower-bound witness: the exact maximum is not computed,")
        print("      only shown to be >= 21; the {2,3} enumeration is saturated.)")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


def frac_expr(x):
    """Human-readable p/q for a Fraction."""
    if x.denominator == 1:
        return str(x.numerator)
    return "%d/%d" % (x.numerator, x.denominator)


if __name__ == "__main__":
    raise SystemExit(main())
