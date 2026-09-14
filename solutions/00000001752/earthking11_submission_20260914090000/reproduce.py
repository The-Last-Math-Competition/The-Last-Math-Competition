#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001752.

Conjecture (auto-generated), quoted from conjectures/00000001752.md:

    Definition: The Mark values of primitive permutation characters of S_n are
    the averages of fixed points (by subset size).  Conjecture: The Mark values
    in the 2-transitive case have a complete closed form:
    M_k = (k! * S(n,k)) / |G| (given by the Burnside average of subset counts);
    agreeing case-by-case with the ATLAS.

The file itself specifies the right-hand side as a *Burnside average of subset
counts*, so we read the asserted equation literally:

    (1/|S_n|) * sum_{g in S_n} #{ k-subsets of {1..n} fixed by g }
        =  k! * S(n,k) / n! .

The conjecture is FALSE.  For S_n acting on k-subsets (1 <= k <= n-1) the action
is transitive, so by Burnside's lemma the left side is the number of orbits,
namely 1.  For the in-scope (sharply) 2-transitive action of S_3 on 1-subsets,

    LHS = (3 + 1 + 1 + 1 + 0 + 0) / 6 = 6/6 = 1,
    RHS = 1! * S(3,1) / 6 = 1 * 1 / 6 = 1/6,

and 1 != 1/6.  Cross-multiplying: 1*6 = 6 while 1*1 = 1, and 6 != 1.

This script is pure Python 3 standard library (no sympy, no numpy).  It exits
non-zero if any check fails.
"""

import sys
from fractions import Fraction
from itertools import product, combinations
from math import factorial


# ---------------------------------------------------------------------------
# Group-theoretic enumeration (exact, finite)
# ---------------------------------------------------------------------------

def all_functions(n):
    """All n^n functions {0,...,n-1} -> {0,...,n-1}, as value tuples."""
    return list(product(range(n), repeat=n))


def is_bijection(f, n):
    """A function is a permutation iff its n values are pairwise distinct."""
    return len(set(f)) == n


def symmetric_group(n):
    """Enumerate S_n: the n! bijections among the n^n functions."""
    return [f for f in all_functions(n) if is_bijection(f, n)]


def k_subsets(n, k):
    """All k-subsets of {0,...,n-1}, as sorted tuples."""
    return list(combinations(range(n), k))


def fixes(f, subset):
    """True iff the permutation f maps the subset onto itself (setwise)."""
    return {f[x] for x in subset} == set(subset)


def fix_count(f, subsets):
    """Fix_k(f) = number of k-subsets fixed by f."""
    return sum(1 for s in subsets if fixes(f, s))


def burnside_sum(group, subsets):
    """sum_{g in group} Fix_k(g)."""
    return sum(fix_count(f, subsets) for f in group)


def burnside_average(group, subsets):
    """(1/|G|) * sum_g Fix_k(g), as an exact rational."""
    return Fraction(burnside_sum(group, subsets), len(group))


# ---------------------------------------------------------------------------
# Stirling numbers of the second kind (self-written recurrence, no library)
# ---------------------------------------------------------------------------

def stirling2(n, k):
    """S(n,k): number of partitions of an n-set into k non-empty blocks.

    Recurrence S(n,k) = k*S(n-1,k) + S(n-1,k-1), with S(0,0)=1 and S(n,0)=0
    for n>0.  Exact integer arithmetic, built as a Pascal-style table.
    """
    if n < 0 or k < 0:
        return 0
    # dp[j] = S(i, j) for the current i
    dp = [0] * (k + 1)
    dp[0] = 1                      # S(0,0) = 1
    for i in range(1, n + 1):
        nxt = [0] * (k + 1)
        for j in range(1, k + 1):
            nxt[j] = j * dp[j] + dp[j - 1]
        dp = nxt
    return dp[k]


def conjecture_formula(n, k):
    """The conjectured value k! * S(n,k) / n!, as an exact rational."""
    return Fraction(factorial(k) * stirling2(n, k), factorial(n))


# ---------------------------------------------------------------------------
# 2-transitivity: orbit count on ordered pairs of distinct k-subsets
# ---------------------------------------------------------------------------

def orbits_on_ordered_distinct_pairs(group, subsets, n):
    """Number of G-orbits on {(A,B) : A,B k-subsets, A != B}, and #pairs.

    The action on k-subsets is 2-transitive iff there is at least one ordered
    pair of distinct k-subsets and all of them form a single orbit.
    """
    pairs = [(a, b) for a in subsets for b in subsets if a != b]
    if not pairs:
        return 0, 0
    remaining = set(pairs)
    orbits = 0
    while remaining:
        seed = next(iter(remaining))
        orbits += 1
        stack = [seed]
        remaining.discard(seed)
        while stack:
            a, b = stack.pop()
            for f in group:
                img = (tuple(sorted(f[x] for x in a)),
                       tuple(sorted(f[x] for x in b)))
                if img in remaining:
                    remaining.discard(img)
                    stack.append(img)
    return orbits, len(pairs)


def is_two_transitive(group, subsets, n):
    """2-transitive iff >=1 ordered pair and exactly one orbit on them."""
    orbits, npairs = orbits_on_ordered_distinct_pairs(group, subsets, n)
    return orbits == 1 and npairs > 0, orbits, npairs


# ---------------------------------------------------------------------------
# Reporting helpers
# ---------------------------------------------------------------------------

CHECKS = []


def check(name, ok, detail):
    CHECKS.append((name, bool(ok), detail))


def fmt(frac):
    """Render an exact Fraction as 'p/q' (or 'p' when integral)."""
    return str(frac.numerator) if frac.denominator == 1 else f"{frac.numerator}/{frac.denominator}"


def main():
    line = "=" * 74
    print(line)
    print("Disproof of conjecture 00000001752 -- reproduction")
    print(line)

    # ------------------------------------------------------------------
    # 1. S_3 and the decisive in-scope witness (n, k) = (3, 1)
    # ------------------------------------------------------------------
    n = 3
    s3 = symmetric_group(n)
    check("S_3 enumerated from all 3^3 = 27 functions Fin 3 -> Fin 3: |S_3| = 6",
          len(all_functions(n)) == 27 and len(s3) == 6,
          f"27 functions, {len(s3)} bijections")

    subsets1 = k_subsets(n, 1)   # {0}, {1}, {2}
    subsets2 = k_subsets(n, 2)   # {0,1}, {0,2}, {1,2}
    check("1-subsets and 2-subsets of {0,1,2} are complementary families "
          "(|X_1| = |X_2| = 3)",
          len(subsets1) == 3 and len(subsets2) == 3,
          f"{subsets1} and {subsets2}")

    fix1 = [fix_count(f, subsets1) for f in s3]
    fix2 = [fix_count(f, subsets2) for f in s3]
    fix1_sorted = sorted(fix1, reverse=True)
    fix2_sorted = sorted(fix2, reverse=True)

    print("\n[1] S_3 acting on 1-subsets (the natural sharply 2-transitive action)")
    print(f"    fixed-point counts Fix_1 over the 6 elements: {fix1_sorted}")
    print(f"    Burnside numerator sum_g Fix_1(g) = {sum(fix1)}")
    check("S_3, k = 1: Fix_1 = [3,1,1,1,0,0] (identity fixes 3, each of the "
          "three transpositions fixes 1, each of the two 3-cycles fixes 0)",
          fix1_sorted == [3, 1, 1, 1, 0, 0],
          f"sorted Fix_1 = {fix1_sorted}")

    bs1 = burnside_sum(s3, subsets1)
    avg1 = burnside_average(s3, subsets1)
    f1 = conjecture_formula(n, 1)
    check("S_3, k = 1: Burnside numerator is 6 = sum of [3,1,1,1,0,0], so the "
          "Burnside average is 6/6 = 1",
          bs1 == 6 and avg1 == Fraction(1, 1),
          f"sum = {bs1}, average = {fmt(avg1)}")
    check("S_3, k = 1: LHS (Burnside average, = number of orbits) = 1; "
          "RHS (formula 1!*S(3,1)/3!) = 1/6; and 1 != 1/6",
          avg1 == Fraction(1, 1) and f1 == Fraction(1, 6) and avg1 != f1,
          f"LHS = {fmt(avg1)}, RHS = {fmt(f1)}, difference = {fmt(avg1 - f1)}")

    # Cross-multiplication of 1 and 1/6: 1*6 = 6 vs 1*1 = 1.
    check("Cross-multiplication of 1 = 1/1 and 1/6: 1*6 = 6 and 1*1 = 1, "
          "and 6 != 1",
          1 * 6 != 1 * 1,
          f"1*6 = {1*6}, 1*1 = {1*1}, 6 != 1")

    check("S_3 acting on 1-subsets is 2-transitive (in scope): the action is "
          "sharply 2-transitive, |S_3| = 3*2 = 6",
          is_two_transitive(s3, subsets1, n)[0],
          f"orbits on ordered distinct pairs = {is_two_transitive(s3, subsets1, n)[1]}")

    # ------------------------------------------------------------------
    # 2. k = 2 for S_3: the isolated coincidence (in scope, but agrees)
    # ------------------------------------------------------------------
    fix2_sorted = sorted(fix2, reverse=True)
    bs2 = burnside_sum(s3, subsets2)
    avg2 = burnside_average(s3, subsets2)
    f2 = conjecture_formula(n, 2)
    print("\n[2] S_3 acting on 2-subsets (also 2-transitive: complement of k = 1)")
    print(f"    fixed-point counts Fix_2 over the 6 elements: {fix2_sorted}")
    check("S_3, k = 2: Fix_2 = [3,1,1,1,0,0] (a 2-subset is fixed iff its "
          "complementary singleton is), Burnside average = 1",
          fix2_sorted == [3, 1, 1, 1, 0, 0] and avg2 == Fraction(1, 1),
          f"sorted Fix_2 = {fix2_sorted}, average = {fmt(avg2)}")
    check("S_3, k = 2: the formula happens to agree: 2!*S(3,2)/3! = "
          f"2*{stirling2(3,2)}/6 = {fmt(f2)} = 1",
          f2 == Fraction(1, 1) == avg2,
          f"RHS = {fmt(f2)} = LHS = {fmt(avg2)}; the isolated coincidence "
          "(n,k) = (3,2)")
    check("S_3 acting on 2-subsets is 2-transitive",
          is_two_transitive(s3, subsets2, n)[0],
          f"orbits on ordered distinct pairs = {is_two_transitive(s3, subsets2, n)[1]}")

    # ------------------------------------------------------------------
    # 3. The full in-scope 2-transitive range and the general mismatch
    # ------------------------------------------------------------------
    print("\n[3] 2-transitive range of S_n on k-subsets, and LHS vs RHS")
    print(f"    {'n':>2}  {'k':>2}  {'2-transitive':>12}  {'LHS (Burnside)':>15}  "
          f"{'RHS (formula)':>14}  agree?")
    tt_cases = []
    agree_cases = []
    mismatch_cases = []
    for nn in range(2, 8):
        group = symmetric_group(nn)
        for kk in range(1, nn):          # k = n gives a single subset, not in range
            subs = k_subsets(nn, kk)
            two_t, orbits, npairs = is_two_transitive(group, subs, nn)
            lhs = burnside_average(group, subs)
            rhs = conjecture_formula(nn, kk)
            agree = (lhs == rhs)
            if two_t:
                tt_cases.append((nn, kk))
                if agree:
                    agree_cases.append((nn, kk))
                else:
                    mismatch_cases.append((nn, kk))
                print(f"    {nn:>2}  {kk:>2}  {'yes':>12}  {fmt(lhs):>15}  "
                      f"{fmt(rhs):>14}  {'yes' if agree else 'NO'}")
    check("Among all 2-transitive cases with 2 <= n <= 7, the Burnside average "
          "is always 1 (orbit count) and the formula fails except (3,2)",
          agree_cases == [(3, 2)] and len(mismatch_cases) == len(tt_cases) - 1,
          f"2-transitive cases: {tt_cases}; agreements: {agree_cases} "
          f"(the isolated coincidence (3,2)); mismatches: {mismatch_cases}")

    # Closed forms on the 2-transitive range: k=1 -> 1/n!, k=n-1 -> (n-1)/2.
    closed_ok = True
    for nn in range(2, 12):
        if conjecture_formula(nn, 1) != Fraction(1, factorial(nn)):
            closed_ok = False
        if conjecture_formula(nn, nn - 1) != Fraction(nn - 1, 2):
            closed_ok = False
    check("On the 2-transitive range the formula has the closed forms "
          "k=1: 1/n! and k=n-1: (n-1)/2; both differ from 1 for n >= 2 "
          "(k=1) and n >= 4 (k=n-1)",
          closed_ok,
          "k=1 gives 1/2, 1/6, 1/24, ... ; k=n-1 gives 1/2 (n=2), 1 (n=3), "
          "3/2 (n=4), 2 (n=5), ...")

    # ------------------------------------------------------------------
    # 4. Non-integrality: an ATLAS Mark is an integer
    # ------------------------------------------------------------------
    frac_vals = {c: conjecture_formula(*c) for c in [(3, 1), (4, 2), (5, 1),
                                                     (5, 2), (5, 4), (4, 1)]}
    nonint = {c: v for c, v in frac_vals.items() if v.denominator != 1}
    check("The formula value is non-integral in most cases (1/6, 7/12, ...), "
          "whereas an ATLAS Mark is an integer",
          len(nonint) >= 3,
          "; ".join(f"M_{c[1]}(S_{c[0]}) = {fmt(v)}" for c, v in frac_vals.items()))

    # ------------------------------------------------------------------
    # 5. Out-of-scope illustration: S_4 on 2-subsets is NOT 2-transitive
    # ------------------------------------------------------------------
    n4 = 4
    s4 = symmetric_group(n4)
    sub42 = k_subsets(n4, 2)
    two4, orbits4, npairs4 = is_two_transitive(s4, sub42, n4)
    lhs4 = burnside_average(s4, sub42)
    rhs4 = conjecture_formula(n4, 2)
    check("S_4 on 2-subsets is NOT 2-transitive: ordered distinct pairs split "
          "into intersecting and disjoint orbits; the identity still fails "
          "(LHS = 1, RHS = 7/12), and this case is OUT of the 2-transitive scope",
          (not two4) and lhs4 == Fraction(1, 1) and rhs4 == Fraction(7, 12)
          and lhs4 != rhs4,
          f"orbits on ordered distinct pairs = {orbits4} (pairs = {npairs4}); "
          f"LHS = {fmt(lhs4)}, RHS = {fmt(rhs4)}")

    # ------------------------------------------------------------------
    # 6. Sanity of the self-written Stirling routine
    # ------------------------------------------------------------------
    table = {c: stirling2(*c) for c in [(0, 0), (3, 1), (3, 2), (4, 2), (5, 2),
                                        (5, 3), (6, 3)]}
    check("Stirling routine: S(0,0)=1, S(3,1)=1, S(3,2)=3, S(4,2)=7, "
          "S(5,2)=15, S(5,3)=25, S(6,3)=90 (matches the standard table)",
          table == {(0, 0): 1, (3, 1): 1, (3, 2): 3, (4, 2): 7, (5, 2): 15,
                    (5, 3): 25, (6, 3): 90},
          str(table))
    check("Stirling recurrence cross-check: n*S(n,k) via direct block recursion "
          "matches the table for n <= 7",
          all(stirling2(nn, kk) ==
              (kk * stirling2(nn - 1, kk) + stirling2(nn - 1, kk - 1))
              for nn in range(1, 8) for kk in range(1, nn + 1)),
          "S(n,k) = k*S(n-1,k) + S(n-1,k-1) verified for 1 <= k <= n <= 7")

    # ------------------------------------------------------------------
    # 7. Report
    # ------------------------------------------------------------------
    print("\n[4] Checks")
    ok_all = True
    for name, ok, detail in CHECKS:
        ok_all = ok_all and ok
        print(f"    [{'ok  ' if ok else 'FAIL'}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if ok_all:
        print("PASS: all checks verified; conjecture 00000001752 is FALSE.")
        print("  In-scope witness: S_3 acting 2-transitively on 1-subsets has")
        print("  Burnside average (3+1+1+1+0+0)/6 = 1, while the conjectured")
        print("  formula gives 1!*S(3,1)/6 = 1/6, and 1 != 1/6 (6 != 1).")
        print("  The Burnside average is always 1 (transitive action), while")
        print("  k!*S(n,k)/n! = 1 only in the isolated coincidence (n,k)=(3,2).")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    sys.exit(main())
