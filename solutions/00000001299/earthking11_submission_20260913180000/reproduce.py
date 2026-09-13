#!/usr/bin/env python3
"""Reproduction script for conjecture 00000001299 (Ducci cycles).

Conjecture (exact wording): "For n a power of two the sequence reaches zero in
finitely many steps, while for non-powers of two nontrivial cycles exist; and
the minimal cycle length is an odd factor of n."

This script refutes the *last* clause.  The integer Ducci map is

    T(x)_i = |x_i - x_{i+1}|     (indices cyclic, length n).

For n = 5 the seed (0,0,0,1,1) lies on a cycle of minimal length 15.  The
number 15 is odd but 15 does not divide 5, so the minimal cycle length is not an
odd factor of n.  The first clause (nontrivial cycles exist for non-powers of
two) is the classical zero criterion and is NOT disputed here.

What is computed:

* the explicit 15-cycle of the seed (0,0,0,1,1) for n = 5, with a check that
  all 15 states are distinct and that the 15th returns to the seed;
* exhaustive period sets for n = 5 over [0..9]^5 and for n = 10 over [0..3]^10;
* period sets on random larger seeds for n = 5 and n = 10;
* divisibility checks 15 | 5 and 15 | 10 (both false).

Only the Python standard library is used.  The script prints PASS/FAIL and
exits 0 in both cases.

An honest remark, included because it matters for the written argument: an
earlier attempted proof ("the mod-2 reduction has periods {1,15}, hence integer
cycle lengths must be divisible by 15") is NOT rigorous.  Many seeds whose
integer period is 15 (16 of 300 random n = 5 seeds in one sample) have a mod-2
reduction of period 1; the count is random-sample dependent, but the phenomenon
is robust.  The refutation below therefore rests on direct verification only.
"""

import random
import sys
from itertools import product


def T(x):
    """One step of the Ducci map on the tuple x (cyclic absolute differences)."""
    n = len(x)
    return tuple(abs(x[i] - x[(i + 1) % n]) for i in range(n))


def period(seed, max_iter=100000):
    """Return (preperiod, period) of the orbit of `seed` under T."""
    seen = {}
    x = seed
    k = 0
    while x not in seen:
        seen[x] = k
        x = T(x)
        k += 1
        if k > max_iter:
            raise RuntimeError("iteration limit exceeded")
    mu = seen[x]
    return mu, k - mu


def periods_of(seeds):
    out = set()
    for seed in seeds:
        _, p = period(seed)
        out.add(p)
    return out


def print_cycle(seed):
    print("Explicit cycle for n = 5, seed %s:" % (seed,))
    x = seed
    states = []
    for _ in range(15):
        states.append(x)
        x = T(x)
    for i, st in enumerate(states):
        print("  T^%-2d = %s" % (i, st))
    distinct = len(set(states)) == 15
    closes = T(states[-1]) == seed
    print("  all 15 states distinct: %s" % distinct)
    print("  T(T^14) == seed:        %s   (T^15 = identity on the seed)" % closes)
    return distinct and closes


def main():
    ok = True
    seed5 = (0, 0, 0, 1, 1)

    print("=" * 68)
    ok &= print_cycle(seed5)

    print()
    print("=" * 68)
    print("Period sets (a period of 1 is the trivial fixed point).")

    # Exhaustive n = 5 over [0..9]^5.
    print("\nExhaustive n = 5 over [0..9]^5 (10^5 seeds) ...")
    p5 = periods_of(product(range(10), repeat=5))
    print("  period set: %s" % sorted(p5))
    print("  minimal non-trivial period: %s" % min(p for p in p5 if p > 1))

    # Random larger seeds for n = 5.
    random.seed(20260913)
    seeds5 = [tuple(random.randint(0, 10**6) for _ in range(5)) for _ in range(2000)]
    p5r = periods_of(seeds5)
    print("  random n = 5, 2000 seeds with values up to 10^6:")
    print("    period set: %s" % sorted(p5r))

    # Exhaustive n = 10 over [0..3]^10.
    print("\nExhaustive n = 10 over [0..3]^10 (4^10 = 1048576 seeds) ...")
    p10 = periods_of(product(range(4), repeat=10))
    print("  period set: %s" % sorted(p10))
    print("  minimal non-trivial period: %s" % min(p for p in p10 if p > 1))

    # Random larger seeds for n = 10.
    seeds10 = [tuple(random.randint(0, 10**6) for _ in range(10)) for _ in range(300)]
    p10r = periods_of(seeds10)
    print("  random n = 10, 300 seeds with values up to 10^6:")
    print("    period set: %s" % sorted(p10r))

    print()
    print("=" * 68)
    print("Divisibility checks:")
    d5 = (5 % 15 == 0)
    d10 = (10 % 15 == 0)
    print("  15 divides 5:  %s" % d5)
    print("  15 divides 10: %s" % d10)

    # --- verdict ---------------------------------------------------------
    p5_nontrivial = sorted(p for p in p5 if p > 1)
    p10_nontrivial = sorted(p for p in p10 if p > 1)
    checks = {
        "seed (0,0,0,1,1) lies on a 15-cycle (n = 5)":
            period(seed5)[1] == 15,
        "exhaustive n=5 minimal non-trivial period is 15":
            p5_nontrivial and p5_nontrivial[0] == 15,
        "exhaustive n=10 minimal non-trivial period is 15":
            p10_nontrivial and p10_nontrivial[0] == 15,
        "15 is odd": 15 % 2 == 1,
        "15 does not divide 5": not d5,
        "15 does not divide 10": not d10,
    }

    print()
    print("=" * 68)
    for desc, val in checks.items():
        print("  [%s] %s" % ("ok" if val else "XX", desc))
        ok &= bool(val)

    print()
    if ok and not d5 and not d10:
        print("PASS: conjecture 00000001299 is REFUTED for n = 5: the seed")
        print("      (0,0,0,1,1) has minimal non-trivial cycle length 15, which")
        print("      is odd but does not divide 5.  (For n = 10 the minimal")
        print("      non-trivial period is also 15, and 15 does not divide 10.)")
    else:
        print("FAIL: unexpected result; see checks above.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
