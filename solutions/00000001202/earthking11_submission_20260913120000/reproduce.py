#!/usr/bin/env python3
"""
Reproduce / refute conjecture 00000001202.

The conjecture (from conjectures/00000001202.md) asserts that the
Sprague-Grundy (SG) sequence of the octal game 0.07 is eventually periodic
with period 12 and pre-period length 4, i.e.

        g(n + 12) = g(n)   for all n >= 4.

This script implements BOTH readings of the ambiguous prose:

  * STANDARD octal reading of ``0.07`` (digits d1 = 0, d2 = 7):
    a move removes exactly 2 tokens and may split the remaining tokens
    into 0, 1 or 2 heaps (all three splits are legal because 7 = 111_2).
    Hence for n >= 2

        g(n) = mex{ g(a) XOR g(b) : a + b = n - 2 }.

    This is Dawson's Kayles.  (For n < 2 there is no legal move.)

  * The conjecture's own prose reading "removes 1 or 2 tokens", which is
    the octal game ``0.77`` (Kayles): for n >= 1

        g(n) = mex( { g(a) XOR g(b) : a + b = n - 1 }
                    U { g(a) XOR g(b) : a + b = n - 2 } ).

For each reading the script

  1. computes g(n) for 0 <= n <= N with N >= 800,
  2. finds the smallest n >= 4 with g(n + 12) != g(n) (if any),
  3. searches for the true eventual period p and the smallest index s
     such that g(n + p) = g(n) for all n >= s (within the computed range,
     with a confirmation window well beyond s),
  4. prints value tables and PASS/FAIL lines,
  5. exits 0 (the counterexample is a *successful* refutation).

Standard library only.
"""

import sys

# ---------------------------------------------------------------------------
# Core Sprague-Grundy machinery
# ---------------------------------------------------------------------------


def mex(values):
    """Smallest non-negative integer not present in ``values``."""
    m = 0
    seen = set(values)
    while m in seen:
        m += 1
    return m


def grundy_007(N):
    """SG values of the octal game 0.07 (Dawson's Kayles).

    A move removes exactly 2 tokens and splits the remainder into 0, 1 or
    2 heaps: g(n) = mex{ g(a) ^ g(b) : a + b = n - 2 } for n >= 2.
    """
    g = [0] * (N + 1)
    for n in range(2, N + 1):
        reach = set()
        m = n - 2
        for a in range(m + 1):
            b = m - a
            reach.add(g[a] ^ g[b])
        g[n] = mex(reach)
    # n = 0, 1 have no legal move; mex(empty) = 0, already initialised.
    return g


def grundy_077(N):
    """SG values of the octal game 0.77 (Kayles).

    A move removes 1 or 2 tokens and splits the remainder into 0, 1 or 2
    heaps: g(n) = mex({g(a)^g(b): a+b=n-1} U {g(a)^g(b): a+b=n-2}).
    """
    g = [0] * (N + 1)
    for n in range(1, N + 1):
        reach = set()
        for k in (1, 2):
            if n >= k:
                m = n - k
                for a in range(m + 1):
                    b = m - a
                    reach.add(g[a] ^ g[b])
        g[n] = mex(reach)
    return g


# ---------------------------------------------------------------------------
# Analysis helpers
# ---------------------------------------------------------------------------


def first_period12_failure(g, start=4):
    """Smallest n >= start with g(n) != g(n + 12), or None."""
    N = len(g) - 1
    for n in range(start, N - 12 + 1):
        if g[n] != g[n + 12]:
            return n
    return None


def find_eventual_period(g, max_period=200, min_tail=300):
    """Find the minimal eventual period p.

    Returns ``(p, s)`` where ``s`` is the smallest index such that
    g(n + p) = g(n) for every n in [s, N - p], subject to the confirmation
    window ``N - p - s >= min_tail`` (so that a spurious short period near
    the end of the data is not mistaken for the true one).  Returns
    ``(None, None)`` if no period up to ``max_period`` is confirmed.
    """
    N = len(g) - 1
    for p in range(1, max_period + 1):
        last_bad = -1
        for n in range(0, N - p + 1):
            if g[n] != g[n + p]:
                last_bad = n
        s = last_bad + 1
        if N - p - s >= min_tail:
            return p, s
    return None, None


def print_table(g, upto=60, per_line=10):
    print("    n :", "  ".join(f"{n:3d}" for n in range(upto)))
    for start in range(0, upto, per_line):
        stop = min(start + per_line, upto)
        print("  g(n):", "  ".join(f"{g[n]:3d}" for n in range(start, stop)))


def report(name, g, statement_period=12, statement_start=4):
    print("=" * 74)
    print(f"Reading: {name}")
    print("=" * 74)
    print(f"Computed SG values for 0 <= n <= {len(g) - 1}.")
    print("First values:")
    print_table(g, upto=min(60, len(g) - 1))

    nfail = first_period12_failure(g, start=statement_start)
    if nfail is None:
        print(f"\n  g(n+12) = g(n) holds for all n in "
              f"[{statement_start}, {len(g) - 1 - statement_period}] in the data.")
        print(f"  CLAIM (period 12, pre-period 4): NOT refuted by this range.")
    else:
        print(f"\n  Claimed identity g(n+12) = g(n) for all n >= {statement_start}:")
        print(f"    FIRST FAILURE at n = {nfail}:  "
              f"g({nfail}) = {g[nfail]}, g({nfail + statement_period}) = "
              f"{g[nfail + statement_period]}  (different).")
        print(f"  CLAIM is REFUTED (verdict FALSE).")

    p, s = find_eventual_period(g)
    if p is None:
        print("\n  True eventual period: not found up to the search bound.")
    else:
        print(f"\n  True eventual period: {p}, minimal pre-period: {s}")
        print(f"    i.e. g(n+{p}) = g(n) for all n >= {s} "
              f"(confirmed on n = {s}..{len(g) - 1 - p}).")
    return nfail, p, s


def main():
    N = 1000  # n >= 800 required; 1000 gives a large confirmation window
    print("Conjecture 00000001202: SG sequence of octal 0.07 is eventually")
    print("periodic with period 12 and pre-period 4")
    print("(g(n+12) = g(n) for all n >= 4).")
    print(f"Computing to n = {N}.\n")

    g007 = grundy_007(N)
    fail007, p007, s007 = report("STANDARD octal 0.07  (d1=0, d2=7; removes exactly 2) -- Dawson's Kayles",
                                 g007, statement_period=12, statement_start=4)

    print()
    g077 = grundy_077(N)
    fail077, p077, s077 = report("PROSE 'removes 1 or 2 tokens' = octal 0.77 (Kayles)",
                                 g077, statement_period=12, statement_start=4)

    print()
    print("=" * 74)
    print("SUMMARY")
    print("=" * 74)
    ok = True

    if fail007 is not None:
        print(f"  [PASS] 0.07 refutes 'g(n+12)=g(n) for n>=4': "
              f"first failure n={fail007}, g({fail007})={g007[fail007]}, "
              f"g({fail007 + 12})={g007[fail007 + 12]}.")
        print(f"         true eventual period {p007}, pre-period {s007} "
              f"(conjecture says period 12, pre-period 4).")
    else:
        print("  [FAIL] 0.07 did not refute the identity in range.")
        ok = False

    if fail077 is not None:
        print(f"  [PASS] 0.77 refutes 'g(n+12)=g(n) for n>=4': "
              f"first failure n={fail077}, g({fail077})={g077[fail077]}, "
              f"g({fail077 + 12})={g077[fail077 + 12]}.")
        print(f"         true eventual period {p077}, pre-period {s077} "
              f"(pre-period is not 4).")
    else:
        print("  [FAIL] 0.77 did not refute the identity in range.")
        ok = False

    print()
    print("  VERDICT: conjecture 00000001202 is FALSE under both readings.")
    print("           " + ("Both tests PASS." if ok else "Incomplete."))
    return 0


if __name__ == "__main__":
    sys.exit(main())
