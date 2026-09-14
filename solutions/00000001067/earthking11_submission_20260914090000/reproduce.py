#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001067.

    Definition: A B_h set (unique h-fold sums).
    Conjecture: The maximal B_2 set in F_p has size ceil(sqrt p) + O(1),
                and the O(1) term equals 0 for p = 3 mod 4
                (an exact B_2 result).

The conjecture is FALSE.  We read "B_2 set with unique 2-fold sums" in the
standard STRONG Sidon sense: all unordered sums a + b with a <= b (repetition
allowed) are distinct.  For a strong Sidon set S of size k in F_p the k(k-1)
ordered differences a - b (a != b) are pairwise distinct and nonzero, hence
k(k-1) <= p - 1.

Witness: p = 19 (which is 3 mod 4).  Here ceil(sqrt 19) = 5, but the maximum
strong Sidon set in F_19 has size 4.  An explicit 4-set is {0,1,3,7}, whose
pairwise sums 0,1,2,3,4,6,7,8,10,14 are all distinct.  No 5-element strong
Sidon set exists: the difference bound gives 5*4 = 20 > 18 = p - 1, and an
exhaustive check of all C(19,5) = 11628 five-subsets finds none.

This script:
  * verifies {0,1,3,7} is strong Sidon by listing all 10 pairwise sums;
  * verifies all C(19,5) = 11628 five-subsets of F_19 fail;
  * computes the maximum STRONG Sidon size in F_p for
    p = 7, 11, 19, 23, 31, 43, 47, 59 by exhaustive backtracking;
  * verifies the difference-count bound k(k-1) <= p-1 on every maximal set;
  * verifies the equivalence "strong Sidon <=> ordered differences distinct"
    exhaustively (all subsets for p = 7, 11; all subsets of size <= 6 for
    p = 19, 23);
  * verifies every inclusion-maximal strong Sidon set in F_19 has size 4;
  * reports the WEAK Sidon maxima (only sums of two distinct elements unique)
    for the same primes, and checks the (weaker) bound C(k,2) <= p;
  * cross-checks p = 43 via Bruck-Ryser-Chowla (a size-7 set would be a
    perfect (43,7,1) difference set, i.e. a projective plane of order 6, which
    BRC rules out because 6 = 2 mod 4 is not a sum of two squares);
  * compares the maxima with ceil(sqrt p).

Python 3 standard library only.  Exits non-zero if any check fails.
"""

import math
import sys
from itertools import combinations

PRIMES = [7, 11, 19, 23, 31, 43, 47, 59]

# The independently known values (also produced by the searches below).
EXPECTED_STRONG = {7: 3, 11: 3, 19: 4, 23: 5, 31: 6, 43: 6, 47: 6, 59: 7}
EXPECTED_WEAK = {7: 4, 11: 5, 19: 6, 23: 6, 31: 7, 43: 8, 47: 8, 59: 9}


def ceil_sqrt(n):
    """Exact integer ceiling of sqrt(n), without floating point."""
    c = math.isqrt(n)
    return c if c * c == n else c + 1


# ----------------------------------------------------------------------
# Sidon predicates (exact, exhaustive)
# ----------------------------------------------------------------------

def strong_sums(S, p):
    """All unordered sums a + b (a <= b, repetition allowed) of S in F_p."""
    S = list(S)
    return [(S[i] + S[j]) % p for i in range(len(S)) for j in range(i, len(S))]


def is_strong_sidon(S, p):
    """Strong Sidon (B_2 with unique 2-fold sums): all a+b, a <= b, distinct."""
    s = strong_sums(S, p)
    return len(set(s)) == len(s)


def weak_sums(S, p):
    """All sums a + b of two DISTINCT elements of S in F_p."""
    S = list(S)
    return [(S[i] + S[j]) % p
            for i in range(len(S)) for j in range(i + 1, len(S))]


def is_weak_sidon(S, p):
    """Weak Sidon: all sums of two distinct elements are distinct."""
    s = weak_sums(S, p)
    return len(set(s)) == len(s)


def differences(S, p):
    """The k(k-1) ordered differences a - b (a != b) in F_p."""
    S = list(S)
    return [(a - b) % p for a in S for b in S if a != b]


def diff_distinct(S, p):
    """True iff the ordered differences are pairwise distinct (then nonzero)."""
    d = differences(S, p)
    return len(set(d)) == len(d)


# ----------------------------------------------------------------------
# Backtracking maximum searches
#
# Translation invariance: if S is strong/weak Sidon, then so is S + c, because
# every sum is shifted by the injective map z |-> z + 2c.  Hence a maximum set
# may be assumed to contain 0.  The WLOG-zero searches below are therefore
# exhaustive; `*_full` (no WLOG) is used to validate them independently.
# ----------------------------------------------------------------------

def max_strong_sidon(p, wlog_zero=True):
    """Maximum size of a strong Sidon subset of F_p, by backtracking.

    Elements are added in increasing order.  When x is appended to a partial
    set `cur`, the new sums are 2x and x + s (s in cur); they must be distinct
    among themselves and disjoint from the existing sums.  The bitmask `sums`
    holds the existing sums.
    """
    best = 0
    best_set = ()

    def dfs(cur, sums, start):
        nonlocal best, best_set
        if len(cur) > best:
            best, best_set = len(cur), tuple(cur)
        if len(cur) + (p - start) <= best:      # cannot reach `best` any more
            return
        for x in range(start, p):
            b2 = 1 << ((2 * x) % p)
            if sums & b2:                       # 2x collides with an old sum
                continue
            new = b2
            ok = True
            for s in cur:
                b = 1 << ((x + s) % p)
                if new & b or sums & b:
                    ok = False
                    break
                new |= b
            if not ok:
                continue
            cur.append(x)
            dfs(cur, sums | new, x + 1)
            cur.pop()

    if wlog_zero:
        dfs([0], 1, 1)                          # sums of {0} are {0+0 = 0}
    else:
        dfs([], 0, 0)
    return best, best_set


def max_weak_sidon(p, wlog_zero=True):
    """Maximum size of a WEAK Sidon subset of F_p, by backtracking.

    Only pairs of distinct elements matter, so repeated sums 2x are free.
    For a partial set of size m the m(m-1)/2 pair sums are distinct, giving the
    counting bound C(k,2) <= p for a set of size k.
    """
    best = 0
    best_set = ()

    def dfs(cur, pairsums, start):
        nonlocal best, best_set
        if len(cur) > best:
            best, best_set = len(cur), tuple(cur)
        if len(cur) + (p - start) <= best:
            return
        for x in range(start, p):
            new = 0
            ok = True
            for s in cur:
                b = 1 << ((x + s) % p)
                if new & b or pairsums & b:
                    ok = False
                    break
                new |= b
            if not ok:
                continue
            cur.append(x)
            dfs(cur, pairsums | new, x + 1)
            cur.pop()

    if wlog_zero:
        dfs([0], 0, 1)
    else:
        dfs([], 0, 0)
    return best, best_set


# ----------------------------------------------------------------------
# Enumerations and helpers
# ----------------------------------------------------------------------

def strong_sidon_subsets(p):
    """Enumerate every strong Sidon subset of F_p (as increasing tuples)."""
    out = []

    def dfs(cur, sums, start):
        out.append(tuple(cur))
        for x in range(start, p):
            b2 = 1 << ((2 * x) % p)
            if sums & b2:
                continue
            new = b2
            ok = True
            for s in cur:
                b = 1 << ((x + s) % p)
                if new & b or sums & b:
                    ok = False
                    break
                new |= b
            if not ok:
                continue
            cur.append(x)
            dfs(cur, sums | new, x + 1)
            cur.pop()

    dfs([], 0, 0)
    return out


def equivalence_check(p, max_size):
    """Count mismatches of 'strong Sidon <=> differences distinct' over all
    subsets of F_p with size <= max_size.  Returns (n_checked, n_mismatch)."""
    checked = mism = 0
    for k in range(0, max_size + 1):
        for S in combinations(range(p), k):
            checked += 1
            if is_strong_sidon(S, p) != diff_distinct(S, p):
                mism += 1
    return checked, mism


def is_sum_of_two_squares(n):
    a = 0
    while a * a <= n:
        b = math.isqrt(n - a * a)
        if b * b == n - a * a:
            return True
        a += 1
    return False


# ----------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------

def main():
    checks = []
    failed = []

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        if not ok:
            failed.append(name)

    # ------------------------------------------------------------------
    # 1. The explicit witness {0,1,3,7} in F_19
    # ------------------------------------------------------------------
    W = (0, 1, 3, 7)
    ws = sorted(strong_sums(W, 19))
    check("{0,1,3,7} is strong Sidon in F_19 (10 pairwise sums distinct)",
          is_strong_sidon(W, 19) == (ws == [0, 1, 2, 3, 4, 6, 7, 8, 10, 14]),
          "pairwise sums sorted = %s" % ws)

    # ------------------------------------------------------------------
    # 2. All C(19,5) = 11628 five-subsets of F_19 fail to be strong Sidon
    # ------------------------------------------------------------------
    total5 = 0
    sidon5_subsets = 0
    for S in combinations(range(19), 5):
        total5 += 1
        if is_strong_sidon(S, 19):
            sidon5_subsets += 1
    check("all C(19,5) = 11628 five-subsets of F_19 fail to be strong Sidon",
          total5 == 11628 and sidon5_subsets == 0,
          "enumerated %d five-subsets; strong Sidon among them: %d"
          % (total5, sidon5_subsets))

    # ------------------------------------------------------------------
    # 3. Maximum STRONG Sidon size, exhaustive backtracking
    # ------------------------------------------------------------------
    strong_max = {}
    strong_set = {}
    for p in PRIMES:
        k, S = max_strong_sidon(p)
        strong_max[p] = k
        strong_set[p] = S
        check("max strong Sidon size in F_%d is %d (witness %s, sums %s)"
              % (p, k, S, sorted(strong_sums(S, p))),
              is_strong_sidon(S, p) and len(set(S)) == k,
              "witness is a strong Sidon %d-set, so the maximum is >= %d"
              % (k, k))

    check("strong maxima match the independently known values",
          strong_max == EXPECTED_STRONG,
          "computed %s, expected %s" % (strong_max, EXPECTED_STRONG))

    small = [p for p in PRIMES if p <= 23]
    detail = []
    agree = True
    for p in small:
        kf, _ = max_strong_sidon(p, wlog_zero=False)
        agree = agree and (kf == strong_max[p])
        detail.append("p=%d: full=%d wlog0=%d" % (p, kf, strong_max[p]))
    check("strong WLOG-0 search == unrestricted full search (p <= 23)",
          agree, "; ".join(detail))

    # ------------------------------------------------------------------
    # 4. Difference-count bound k(k-1) <= p-1
    # ------------------------------------------------------------------
    for p in PRIMES:
        k = strong_max[p]
        d = differences(strong_set[p], p)
        bound_ok = (k * (k - 1) <= p - 1)
        distinct_ok = (len(set(d)) == len(d)) and (0 not in d)
        check("p=%d: max k=%d satisfies k(k-1)=%d <= p-1=%d; the witness has "
              "%d pairwise-distinct nonzero differences"
              % (p, k, k * (k - 1), p - 1, len(d)),
              bound_ok and distinct_ok,
              "bound holds and its hypothesis (differences distinct+nonzero) "
              "is satisfied by the witness")

    check("p=19: size 5 forbidden by the difference bound (5*4=20 > 18=p-1)",
          5 * 4 > 19 - 1,
          "a 5-element strong Sidon set would need 20 distinct nonzero "
          "differences in the 18-element group F_19^* -- impossible")

    check("p=11: size 4 forbidden by the difference bound (4*3=12 > 10=p-1)",
          4 * 3 > 11 - 1,
          "so p=11 is already a counterexample: max 3, not ceil(sqrt 11)=4")

    count_rules_out = {p: (strong_max[p] + 1) * strong_max[p] > p - 1
                       for p in PRIMES}

    # ------------------------------------------------------------------
    # 5. Equivalence strong Sidon <=> differences distinct (exhaustive)
    # ------------------------------------------------------------------
    eq_ranges = [(7, 7), (11, 11), (19, 6), (23, 6)]
    for p, ms in eq_ranges:
        checked, mism = equivalence_check(p, ms)
        label = ("all subsets" if ms >= p else "all subsets of size <= %d" % ms)
        check("strong Sidon <=> ordered differences distinct: %s of F_%d"
              % (label, p),
              mism == 0,
              "%d subsets checked, %d mismatches" % (checked, mism))

    # ------------------------------------------------------------------
    # 6. Inclusion-maximal reading: every inclusion-maximal strong Sidon set
    #    in F_19 has size 4
    # ------------------------------------------------------------------
    all_strong = strong_sidon_subsets(19)
    maximal = []
    for S in all_strong:
        Sset = set(S)
        is_max = True
        for x in range(19):
            if x in Sset:
                continue
            if is_strong_sidon(list(S) + [x], 19):
                is_max = False
                break
        if is_max:
            maximal.append(S)
    max_sizes = sorted({len(S) for S in maximal})
    check("every inclusion-maximal strong Sidon set in F_19 has size 4",
          max_sizes == [4],
          "%d strong Sidon subsets, %d inclusion-maximal, sizes %s"
          % (len(all_strong), len(maximal), max_sizes))

    # ------------------------------------------------------------------
    # 7. WEAK Sidon maxima
    # ------------------------------------------------------------------
    weak_max = {}
    weak_set = {}
    for p in PRIMES:
        k, S = max_weak_sidon(p)
        weak_max[p] = k
        weak_set[p] = S
        c_ok = (k * (k - 1) // 2 <= p)
        check("max weak Sidon size in F_%d is %d (witness %s), C(%d,2)=%d <= p=%d"
              % (p, k, S, k, k * (k - 1) // 2, p),
              is_weak_sidon(S, p) and len(set(S)) == k and c_ok,
              "witness pair sums are distinct: %s" % sorted(weak_sums(S, p)))

    check("weak maxima match the independently known values",
          weak_max == EXPECTED_WEAK,
          "computed %s, expected %s" % (weak_max, EXPECTED_WEAK))

    detail_w = []
    agree_w = True
    for p in small:
        kf, _ = max_weak_sidon(p, wlog_zero=False)
        agree_w = agree_w and (kf == weak_max[p])
        detail_w.append("p=%d: full=%d wlog0=%d" % (p, kf, weak_max[p]))
    check("weak WLOG-0 search == unrestricted full search (p <= 23)",
          agree_w, "; ".join(detail_w))

    check("the weak reading also refutes the exact formula: max weak at p=19 "
          "is 6 vs ceil(sqrt 19)=5, and at p=11 is 5 vs ceil(sqrt 11)=4",
          weak_max[19] == 6 and weak_max[11] == 5,
          "p=19 weak max %d (e.g. %s); p=11 weak max %d (e.g. %s)"
          % (weak_max[19], weak_set[19], weak_max[11], weak_set[11]))

    weak19 = weak_set[19]
    check("difference-distinctness characterizes STRONG Sidon but fails for the "
          "WEAK maximum set %s in F_19" % (weak19,),
          not diff_distinct(weak19, 19),
          "that set has %d ordered differences but F_19 has only 18 nonzero "
          "elements, so they cannot be distinct; this confirms the "
          "difference-count bound is a strong-Sidon-only tool"
          % (weak_max[19] * (weak_max[19] - 1)))

    # ------------------------------------------------------------------
    # 8. Bruck-Ryser-Chowla cross-check at p = 43
    # ------------------------------------------------------------------
    check("p=43: a size-7 strong Sidon set would be a perfect (43,7,1) "
          "difference set (7*6 = 42 = 43-1)",
          7 * 6 == 43 - 1,
          "all 42 nonzero residues would be the pairwise differences, i.e. a "
          "projective plane of order 6")
    check("Bruck-Ryser-Chowla excludes projective planes of order 6 = 2 mod 4 "
          "(6 is not a sum of two squares)",
          6 % 4 == 2 and not is_sum_of_two_squares(6),
          "6 mod 4 = 2; 6 is not a^2+b^2 for integers (0,1,2,4,5 are the "
          "representable values <= 6)")
    check("consistency: computed max strong size at p=43 is 6, not 7",
          strong_max[43] == 6 and 6 * 5 <= 43 - 1,
          "6*5=30 <= 42, and no size-7 set exists by Bruck-Ryser-Chowla")

    # ------------------------------------------------------------------
    # 9. Comparison with ceil(sqrt p); the exact p = 3 mod 4 formula
    # ------------------------------------------------------------------
    rows = []
    for p in PRIMES:
        c = ceil_sqrt(p)
        rows.append((p, p % 4, c, strong_max[p], weak_max[p], c == strong_max[p]))

    holds = [p for p in PRIMES if p % 4 == 3 and strong_max[p] == ceil_sqrt(p)]
    fails = [p for p in PRIMES if p % 4 == 3 and strong_max[p] != ceil_sqrt(p)]
    check("the exact clause 'max = ceil(sqrt p) for p = 3 mod 4' fails at %s "
          "(and happens to hold at %s)" % (fails, holds),
          set(fails) == {11, 19, 43, 47, 59} and set(holds) == {7, 23, 31},
          "holds at %s, fails at %s -- a plausible but false exact formula, "
          "not a typo" % (holds, fails))

    # ==================================================================
    # Report
    # ==================================================================
    line = "=" * 78
    print(line)
    print("Disproof of conjecture 00000001067 -- reproduction")
    print(line)
    print()
    print("Reading: a B_2 set with unique 2-fold sums is a STRONG Sidon set")
    print("         (all a+b with a <= b distinct, repetitions allowed).")
    print("Claim:   max size = ceil(sqrt p), exactly (O(1) = 0), for p = 3 mod 4.")
    print("Verdict: FALSE.  p = 19 = 3 mod 4 has max strong Sidon size 4,")
    print("         but ceil(sqrt 19) = 5.")
    print()
    print("[1] Witness {0,1,3,7} in F_19 is strong Sidon; pairwise sums:")
    print("      %s   (all distinct)" % ws)
    print("    Difference bound forbids size 5: 5*4 = 20 > 18 = 19-1.")
    print("    Exhaustive: all C(19,5) = 11628 five-subsets contain a repeat.")
    print()
    print("[2] Strong / weak Sidon maxima vs ceil(sqrt p)")
    print("      %3s  %4s  %6s  %7s  %5s  %s"
          % ("p", "p%4", "ceil", "strong", "weak", "strong == ceil"))
    for p, m4, c, k, w, e in rows:
        print("      %3d  %4d  %6d  %7d  %5d  %s"
              % (p, m4, c, k, w, "yes" if e else "NO"))
    print()
    print("[3] Difference bound k(k-1) <= p-1 on the computed maxima")
    for p in PRIMES:
        k = strong_max[p]
        if count_rules_out[p]:
            note = "k+1=%d RULED OUT by counting (%d > %d)" % (
                k + 1, (k + 1) * k, p - 1)
        else:
            note = ("k+1=%d allowed by counting (%d <= %d); the exhaustive "
                    "search rules it out" % (k + 1, (k + 1) * k, p - 1))
        print("      p=%2d  k=%d  k(k-1)=%2d  p-1=%2d   %s"
              % (p, k, k * (k - 1), p - 1, note))
    print()
    print("[4] Weak Sidon maxima (unique sums of DISTINCT elements only)")
    for p in PRIMES:
        print("      p=%2d  max weak = %d   (example %s)"
              % (p, weak_max[p], weak_set[p]))
    print("    The weak reading also refutes the exact formula: 6 != 5 at p=19")
    print("    and 5 != 4 at p=11.  Note the difference bound is strictly a")
    print("    strong-Sidon fact: the p=19 weak maximum set has %d ordered"
          % (weak_max[19] * (weak_max[19] - 1)))
    print("    differences but F_19 has only 18 nonzero elements.")
    print()
    print("[5] Inclusion-maximal reading")
    print("    Every inclusion-maximal strong Sidon set in F_19 has size %s"
          % max_sizes)
    print("    (%d of them out of %d strong Sidon subsets), so 'maximal' as"
          % (len(maximal), len(all_strong)))
    print("    inclusion-maximal does not rescue the O(1) = 0 clause.")
    print()
    print("[6] p = 43 cross-check (Bruck-Ryser-Chowla)")
    print("    A size-7 strong Sidon set at p=43 would satisfy 7*6 = 42 = p-1,")
    print("    i.e. be a perfect (43,7,1) difference set = projective plane of")
    print("    order 6.  BRC excludes order 6 (6 = 2 mod 4 and 6 is not a sum of")
    print("    two squares), consistent with the computed maximum 6.")
    print()
    print("[7] Checks")
    for name, ok, detail in checks:
        print("    [%s] %s" % ("ok  " if ok else "FAIL", name))
        print("          %s" % detail)
    print()
    print(line)
    if not failed:
        print("PASS: all checks verified; conjecture 00000001067 is FALSE.")
        print("  p = 19 (= 3 mod 4): max strong Sidon size 4, not ceil(sqrt 19)")
        print("  = 5.  The exact 'O(1) = 0' clause for p = 3 mod 4 fails")
        print("  already at p = 11, and also at 19, 43, 47, 59.")
        print(line)
        return 0
    print("FAIL: %d check(s) did not verify: %s" % (len(failed), failed))
    print(line)
    return 1


if __name__ == "__main__":
    sys.exit(main())
