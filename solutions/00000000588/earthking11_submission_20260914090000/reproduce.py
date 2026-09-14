#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000000588.

    Definition: the type t(S) is the number of maximal Apery elements of S
                (equivalently, of pseudo-Frobenius numbers of S).
    Conjecture: t(<n, n+1, ..., 2n-1>) = ceil(n/2).

The conjecture is FALSE.  For the interval semigroup S = <n, ..., 2n-1> one has

        S = {0} U [n, infinity),

because n, n+1, ..., 2n-1 are generators and every m >= 2n splits as
m = n + (m - n) with m - n >= n (induction on m).  Hence, with respect to the
multiplicity n,

        Ap(S, n) = { s in S : s - n not in S } = {0} U {n+1, n+2, ..., 2n-1},

whose nonzero elements are pairwise incomparable under the Apery order
x <=_S y  <=>  y - x in S (their differences lie in {1, ..., n-2}, all gaps),
while 0 <_S x for every nonzero x in Ap(S,n).  So

        t = n - 1,

which equals ceil(n/2) only for n = 2 and n = 3.  The smallest counterexample is

        n = 4:  S = <4,5,6,7>,  Ap(S,4) = {0,5,6,7},  t = 3 != 2 = ceil(4/2).

Standard library only, Python 3.8+.  Exits non-zero if any check fails.
"""

import math


# ----------------------------------------------------------------------
# Exact membership test for S = <gens>, by unbounded-coin DP up to a bound
# ----------------------------------------------------------------------

def membership(gens, bound):
    """reachable[x] is True iff x is a nonnegative integer combination of gens.

    Exact dynamic programming (unbounded coin change) for 0 <= x <= bound:
    a value x is representable iff x == 0 or x - g is representable for some
    generator g <= x.  No floating point, no heuristics.
    """
    reachable = [False] * (bound + 1)
    reachable[0] = True
    for x in range(1, bound + 1):
        for g in gens:
            if g <= x and reachable[x - g]:
                reachable[x] = True
                break
    return reachable


def apery_set(gens, mod, reachable, bound):
    """Ap(S, mod) computed exactly within [0, bound].

    Ap(S, mod) = { s in S : s - mod not in S } (with s - mod < 0, as for
    s = 0, counted as "not in S").  The bound is chosen large enough that the
    whole Apery set lies inside it; see `main` for the certificate that the
    largest element is at most Frobenius + mod.
    """
    ap = []
    for s in range(0, bound + 1):
        if not reachable[s]:
            continue
        if s < mod:
            ap.append(s)          # s - mod < 0, hence not in S
        elif not reachable[s - mod]:
            ap.append(s)
    return ap


def maximal_elements(ap, reachable):
    """Maximal elements of `ap` under x <=_S y  <=>  (x < y and y - x in S)."""
    out = []
    for x in ap:
        maximal = True
        for y in ap:
            if x < y and reachable[y - x]:
                maximal = False
                break
        if maximal:
            out.append(x)
    return out


def pseudo_frobenius(gens, reachable, bound):
    """PF(S) = { x not in S : x + s in S for every nonzero s in S }.

    It suffices to test x + g in S for every generator g: if x + g is in S for
    all generators g, then x + (any element of S) is in S by induction.
    """
    pf = []
    for x in range(0, bound + 1):
        if reachable[x]:
            continue
        if all(reachable[x + g] for g in gens):
            pf.append(x)
    return pf


def main():
    checks = []          # (name, ok, detail)
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    print("=" * 78)
    print("Disproof of conjecture 00000000588 -- reproduction")
    print("=" * 78)
    print()
    print("Definition: t(S) = number of maximal Apery elements of S.")
    print("Conjecture: t(<n, n+1, ..., 2n-1>) = ceil(n/2).")
    print("Claimed value: FALSE; smallest counterexample n = 4 (t = 3, ceil = 2).")

    # ------------------------------------------------------------------
    # 1. The explicit counterexample n = 4, step by step
    # ------------------------------------------------------------------
    n = 4
    gens4 = list(range(n, 2 * n))
    bound4 = 4 * n + 16
    R4 = membership(gens4, bound4)
    ap4 = apery_set(gens4, n, R4, bound4)
    mx4 = maximal_elements(ap4, R4)
    pf4 = pseudo_frobenius(gens4, R4, 2 * n)

    check("n = 4: Ap(S,4) = {0,5,6,7}",
          ap4 == [0, 5, 6, 7], "computed Ap = %s" % ap4)
    check("n = 4: 1,2,3 are gaps (5-4, 6-4, 7-4 not in S)",
          not R4[1] and not R4[2] and not R4[3],
          "inS(1)=%s, inS(2)=%s, inS(3)=%s" % (R4[1], R4[2], R4[3]))
    check("n = 4: 5,6,7 are pairwise incomparable (differences 1,2 not in S)",
          not R4[1] and not R4[2],
          "6-5=1 and 7-6=1 and 7-5=2; inS(1)=%s, inS(2)=%s" % (R4[1], R4[2]))
    check("n = 4: 0 is not maximal (0 <_S 5 since 5-0 = 5 in S)",
          R4[5] and 0 not in mx4, "maximal elements = %s" % mx4)
    check("n = 4: maximal Apery elements = {5,6,7}, so t = 3",
          mx4 == [5, 6, 7], "t = %d" % len(mx4))
    check("n = 4: t = 3 != 2 = ceil(4/2)",
          len(mx4) == 3 and len(mx4) != -(-4 // 2),
          "t = %d, ceil(4/2) = %d" % (len(mx4), -(-4 // 2)))

    # PF and the standard bijection maximal Ap element  <->  PF number (x |-> x - n)
    check("n = 4: PF(S) = {1,2,3} and {maximal Apery} - 4 = PF(S)",
          pf4 == [1, 2, 3] and sorted(x - n for x in mx4) == pf4,
          "PF = %s, {5,6,7}-4 = %s, |PF| = %d"
          % (pf4, sorted(x - n for x in mx4), len(pf4)))

    # ------------------------------------------------------------------
    # 2. The true closed form t = n - 1 for n = 2 .. 12 (table n = 2 .. 9)
    # ------------------------------------------------------------------
    table = []
    bad_ap = []
    bad_t = []
    bad_formula = []
    for nn in range(2, 13):
        gens = list(range(nn, 2 * nn))
        bound = 6 * nn + 24                    # >= 2nn and >= Frobenius + 2nn
        R = membership(gens, bound)
        ap = apery_set(gens, nn, R, bound)
        expect_ap = [0] + list(range(nn + 1, 2 * nn))
        if ap != expect_ap:
            bad_ap.append((nn, ap, expect_ap))
        mx = maximal_elements(ap, R)
        t = len(mx)
        ceil_half = -(-nn // 2)
        table.append((nn, ap, mx, t, ceil_half, t == ceil_half))
        if t != nn - 1:
            bad_t.append((nn, t, nn - 1))
        if (t == ceil_half) != (nn in (2, 3)):
            bad_formula.append((nn, t, ceil_half))

    check("n = 2..12: Ap(S,n) = {0} U {n+1,...,2n-1} for every n",
          not bad_ap,
          "all match" if not bad_ap else "mismatches: %s" % bad_ap)
    check("n = 2..12: t = n - 1 for every n",
          not bad_t,
          "all match" if not bad_t else "failures: %s" % bad_t)
    check("n = 2..12: t = ceil(n/2) exactly for n in {2,3}, and t != ceil(n/2) "
          "for n >= 4",
          not bad_formula,
          "all match" if not bad_formula else "failures: %s" % bad_formula)
    check("the conjecture t(<n,...,2n-1>) = ceil(n/2) is FALSE (n = 4 is a "
          "counterexample)",
          table[2][3] == 3 and table[2][3] != table[2][4],
          "n=4: t=%d, ceil=%d" % (table[2][3], table[2][4]))

    # ------------------------------------------------------------------
    # 3. Robustness: other moduli for n = 4, and other roundings
    # ------------------------------------------------------------------
    mod_bound = 80
    R4big = membership(gens4, mod_bound)
    moduli = [4, 5, 6, 7, 9, 13]
    mod_results = []
    for m in moduli:
        apm = apery_set(gens4, m, R4big, mod_bound)
        mxm = maximal_elements(apm, R4big)
        mod_results.append((m, apm, mxm, len(mxm)))
    check("n = 4: the type is independent of the Apery modulus; over moduli "
          "4,5,6,7,9,13 there are always 3 maximal elements",
          all(c == 3 for (_, _, _, c) in mod_results),
          "; ".join("m=%d: Ap=%s -> %d maximal" % (m, apm, c)
                    for (m, apm, mxm, c) in mod_results))
    check("n = 4: PF(S) = {1,2,3} has the same size 3 as t (maximal Apery "
          "elements correspond to PF numbers via x |-> x - 4)",
          len(pf4) == 3 and pf4 == [1, 2, 3],
          "PF = %s, |PF| = %d, t = %d" % (pf4, len(pf4), len(mx4)))

    alt = {
        "ceil(n/2)": -(-n // 2),
        "floor(n/2)": n // 2,
        "round(n/2)": (n + 1) // 2,          # round-half-up
    }
    check("n = 4: no rounding of n/2 saves the claim (ceil, floor, round all "
          "give 2, but t = 3)",
          all(v == 2 for v in alt.values()) and len(mx4) == 3,
          "; ".join("%s=%d" % (k, v) for k, v in alt.items())
          + "; t=3")

    # ------------------------------------------------------------------
    # 4. Report
    # ------------------------------------------------------------------
    print()
    print("[1] Explicit counterexample n = 4:  S = <4,5,6,7>")
    print("    S = {0} U [4,inf): 4,5,6,7 are generators and m >= 8 = 4 + (m-4).")
    print("    Ap(S,4) = {0,5,6,7}, since 5-4=1, 6-4=2, 7-4=3 are not in S.")
    print("    Nonzero Ap elements 5,6,7 have differences 1,2 (gaps), so they")
    print("    are pairwise incomparable; 0 <_S 5, so 0 is not maximal.")
    print("    Hence t = 3, but ceil(4/2) = 2: the conjecture is FALSE.")
    print("    PF(S) = %s, and {5,6,7} - 4 = %s = PF(S)."
          % (pf4, sorted(x - n for x in mx4)))

    print()
    print("[2] True closed form t = n - 1 (table for n = 2..9; n = 10..12 also checked)")
    print("    %-3s %-26s %-16s %-4s %-10s %s"
          % ("n", "Ap(S,n)", "maximal elements", "t", "ceil(n/2)", "t = ceil(n/2)?"))
    for (n, ap, mx, t, ch, agrees) in table:
        print("    %-3d %-26s %-16s %-4d %-10d %s"
              % (n, str(ap)[:26], str(mx)[:16], t, ch, "yes" if agrees else "NO"))
    print("    The true value is t = n - 1; it agrees with ceil(n/2) only at")
    print("    n = 2 (1 = 1) and n = 3 (2 = 2), and differs for every n >= 4.")

    print()
    print("[3] Robustness")
    print("    type is modulus-independent (n = 4):")
    for (m, apm, mxm, c) in mod_results:
        print("      modulus %-2d: Ap = %-24s maximal = %-18s count = %d"
              % (m, str(apm)[:24], str(mxm)[:18], c))
    print("    PF(S) = %s (|PF| = t = 3), corresponding via x |-> x - n." % pf4)
    print("    roundings of 4/2: %s -> all 2, while t = 3."
          % ", ".join("%s=%d" % (k, v) for k, v in alt.items()))

    print()
    print("[4] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print("    [%s] %s" % (mark, name))
        print("           %s" % detail)

    print()
    print("=" * 78)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000000588 is FALSE.")
        print("  t(<4,5,6,7>) = 3 != 2 = ceil(4/2), and t = n - 1 in general.")
        print("=" * 78)
        return 0
    print("FAIL: at least one check did not verify.")
    print("=" * 78)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
