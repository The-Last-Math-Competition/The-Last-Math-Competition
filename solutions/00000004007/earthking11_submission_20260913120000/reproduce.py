#!/usr/bin/env python3
"""
Reproduction script for the refutation of conjecture 00000004007:

    The p-variation, defined as the p-th root of the supremum over partitions
    of the sum of the p-th powers of the increments, satisfies the optimal
    subadditivity inequality
        ||X+Y|| <= (||X||^q + ||Y||^q)^{1/q},
    where q is the conjugate exponent of p, and the inequality cannot be
    enlarged.

Verdict: FALSE.

Because ||.|| is the p-th root of a supremum, it is homogeneous of degree 1:
||a X|| = |a| ||X||.  Taking X = Y = any non-zero path gives

    LHS = ||X+Y|| = ||2X|| = 2 ||X||,
    RHS = (||X||^q + ||X||^q)^{1/q} = 2^{1/q} ||X||,

and q = p/(p-1) > 1 for every finite p > 1, so 2 > 2^{1/q} and the claimed
inequality fails.  For a two-point unit-step path (||X|| = 1) this script
computes ||X||, ||X+Y|| and the claimed RHS for p = 3/2, 2, 3, 4, 10, and
checks LHS > RHS in every case, using exact rational arithmetic (stdlib
only, `fractions`).  It also checks the raw-supremum reading (if one ignores
the stated root) and the limit case p = 1 (q = infinity), both of which fail
as well.

Exit status is 0 when every check passes.
"""

import sys
from fractions import Fraction
from itertools import combinations


# ---------------------------------------------------------------------------
# p-variation of a finite path
# ---------------------------------------------------------------------------

def partitions(n):
    """All partitions of {0, 1, ..., n} that contain 0 and n.

    Yields tuples of increasing indices starting at 0 and ending at n (for a
    path with n+1 sample points); this is exactly the set over which the
    supremum in the definition of p-variation is taken.
    """
    middle = list(range(1, n))
    for r in range(len(middle) + 1):
        for combo in combinations(middle, r):
            yield (0,) + combo + (n,)


def partition_sum_pow(values, p, part):
    """sum of |increments|^p along the partition `part`, as a float."""
    total = 0.0
    for i, j in zip(part, part[1:]):
        inc = abs(float(values[j]) - float(values[i]))
        total += inc ** float(p)
    return total


def p_variation(values, p):
    """p-variation = ( sup over partitions of sum |increments|^p )^{1/p}.

    Numeric (float) evaluation of the definition, used only as a sanity
    check.  For a two-point path (len(values) == 2) there is a single
    partition {0, 1}, so the supremum is |step|^p and the p-th root is
    exactly |step|, for every p > 0.
    """
    n = len(values) - 1
    best = max(partition_sum_pow(values, p, part) for part in partitions(n))
    return best ** (1.0 / float(p))


def variation_two_point_exact(step):
    """Exact p-variation of a two-point path with a single step `step`.

    sup over partitions of sum |inc|^p = |step|^p, whose p-th root is
    |step| exactly (any p > 0).  Independent of p.
    """
    return abs(Fraction(step))


# ---------------------------------------------------------------------------
# exact comparisons for 2 vs 2^{1/q}
# ---------------------------------------------------------------------------

def conjugate(p):
    """Conjugate exponent q = p/(p-1) as an exact Fraction."""
    return p / (p - 1)


def lhs_gt_rhs_exact(p):
    """Exact check that 2 > 2^{1/q}, where q = p/(p-1).

    Raise both sides to the positive rational q: the comparison is
    equivalent to 2^q > 2^1.  With q = a/b (lowest terms, a,b > 0), that is
    2^a > 2^b, equivalent to a > b (base 2 > 1).  This holds iff q > 1.
    """
    q = conjugate(p)
    a, b = q.numerator, q.denominator
    return a > b


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    checks = []

    def check(name, ok, detail=""):
        ok = bool(ok)
        checks.append((name, ok))
        print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))

    print("=" * 76)
    print("conjecture 00000004007 -- optimal subadditivity of p-variation")
    print("=" * 76)

    # --- sanity: the variation definition on a two-point unit step ---------
    values_X = (0, 1)      # X: one unit step;  ||X|| = 1
    values_XY = (0, 2)     # X+Y: one step of size 2;  ||X+Y|| = 2
    print("\nTwo-point unit-step path X = (0, 1), and X + Y with Y = X:")
    print("  ||X||   = 1   (one increment of size 1; p-th root of 1^p)")
    print("  ||X+Y|| = 2   (one increment of size 2; p-th root of 2^p)")
    print("  homogeneity: ||X+Y|| = ||2X|| = 2 ||X|| = 2")
    print()

    check("variation of X is exactly 1 (structural, any p > 0)",
          variation_two_point_exact(1) == Fraction(1))
    check("variation of X+Y is exactly 2 (structural, any p > 0)",
          variation_two_point_exact(2) == Fraction(2))

    # numeric evaluation of the partition-supremum definition, as a check
    for p in [Fraction(3, 2), Fraction(2), Fraction(3), Fraction(4), Fraction(10)]:
        vx = p_variation(values_X, p)
        vxy = p_variation(values_XY, p)
        check(f"numeric p-variation definition (sup over partitions) "
              f"gives ||X|| = 1, ||X+Y|| = 2 for p = {p}",
              abs(vx - 1.0) < 1e-12 and abs(vxy - 2.0) < 1e-12,
              f"got {vx:.10f}, {vxy:.10f}")

    # --- table over the requested p values ---------------------------------
    ps = [Fraction(3, 2), Fraction(2), Fraction(3), Fraction(4), Fraction(10)]
    print(f"\n{'p':>5} {'q = p/(p-1)':>12} {'||X||':>7} {'||X+Y||':>9} "
          f"{'claimed RHS':>13} {'LHS>RHS':>8}")
    print("-" * 76)
    for p in ps:
        q = conjugate(p)
        nx = variation_two_point_exact(1)
        nxy = variation_two_point_exact(2)
        # claimed RHS = (||X||^q + ||Y||^q)^{1/q} with ||X|| = ||Y|| = 1
        rhs_numeric = 2.0 ** (1.0 / float(q))
        lhs = float(nxy)
        ok = lhs_gt_rhs_exact(p) and lhs > rhs_numeric
        print(f"{str(p):>5} {str(q):>12} {float(nx):>7.4f} {lhs:>9.4f} "
              f"{rhs_numeric:>13.4f} {str(ok):>8}")
        check(f"p = {p}: LHS = 2 > RHS = 2^{{1/q}} = {rhs_numeric:.4f}",
              ok, f"q = {q}")

    # --- raw-supremum reading (root ignored) -------------------------------
    # If one reads ||.|| as the raw supremum sum |inc|^p (no p-th root), then
    # ||X|| = 1^p = 1 and ||X+Y|| = 2^p, while the claimed RHS is still
    # (1^q + 1^q)^{1/q} = 2^{1/q}.  The inequality fails a fortiori.
    print("\nRaw-supremum reading (ignore the stated p-th root):")
    raw_ok = True
    for p in ps:
        q = conjugate(p)
        raw_lhs = 2.0 ** float(p)          # ||X+Y||_raw = 2^p
        raw_rhs = 2.0 ** (1.0 / float(q))
        # exact: raise to p*q > 0: 2^{p^2 q} vs 2^{p}, i.e. p*q > 1
        exact = (p * q) > 1
        ok = exact and raw_lhs > raw_rhs
        raw_ok = raw_ok and ok
        print(f"  p = {str(p):>4}: raw LHS = 2^p = {raw_lhs:>10.4f}, "
              f"RHS = {raw_rhs:>7.4f}  -> {'LHS>RHS' if ok else 'FAIL'}")
    check("raw-supremum reading also fails for every p > 1", raw_ok,
          "e.g. p = 2: 4 vs 1.4142")

    # --- p = 1 limit (q = infinity) ----------------------------------------
    # q -> infinity gives RHS -> max(||X||,||Y||) = ||X|| = 1, while
    # LHS = ||2X|| = 2.  The inequality fails.
    print("\nLimit case p = 1 (q = infinity):")
    lhs_limit = 2.0          # ||2X|| = 2
    rhs_limit = 1.0          # max(||X||, ||Y||) = 1
    print(f"  LHS = ||X+Y|| = 2, RHS = max(||X||, ||Y||) = 1")
    check("p = 1 (q = infinity): LHS = 2 > RHS = 1", lhs_limit > rhs_limit)

    # --- conclusion --------------------------------------------------------
    print("-" * 76)
    print("Conclusion: the conjectured inequality is false already at X = Y != 0.")
    print("Homogeneity ||aX|| = |a| ||X|| forces 2 ||X|| <= 2^{1/q} ||X||, i.e.")
    print("2 <= 2^{1/q}, equivalently 2^q <= 2 -- false for every q > 1.")
    print("The failure is elementary (X = Y); this is precisely why the stated")
    print("inequality cannot be correct.")
    print("-" * 76)

    failed = [name for name, ok in checks if not ok]
    if failed:
        print(f"\nRESULT: FAIL ({len(failed)} check(s) failed)")
        for name in failed:
            print(f"  - {name}")
        return 1
    print(f"\nRESULT: PASS (all {len(checks)} checks passed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
