#!/usr/bin/env python3
"""
Reproduces the refutation of conjecture 00000000416.

The conjecture asserts, for the evacuation operator on the standard Young
tableaux of two-row shape (n,n):

    (a) the number of orbits is 2^(n-1)
    (b) every orbit length divides 2n
    (c) the number of orbits of length exactly 2 is F_(n-1)

At n = 2, (a) says there are 2 orbits and (c) says 1 of them has length 2.
That requires at least 2 + 1 = 3 tableaux. The shape (2,2) has exactly 2.

This script:
  1. enumerates the standard Young tableaux of shape (n,n) for small n;
  2. checks the count against the Catalan number C_n;
  3. prints C_n against the totals the conjecture would require;
  4. prints the two tableaux of shape (2,2) explicitly.

Standard library only. Run with:  python3 reproduce.py
"""
from itertools import permutations
from math import comb


def standard_tableaux(shape):
    """All standard Young tableaux of the given (straight) shape, as row lists."""
    cells = [(i, j) for i, r in enumerate(shape) for j in range(r)]
    n = len(cells)
    out = []
    for perm in permutations(range(1, n + 1)):
        t = dict(zip(cells, perm))
        ok = True
        for (i, j) in cells:
            if j + 1 < shape[i] and t[(i, j)] > t[(i, j + 1)]:
                ok = False
                break
            if i + 1 < len(shape) and j < shape[i + 1] and t[(i, j)] > t[(i + 1, j)]:
                ok = False
                break
        if ok:
            out.append([[t[(i, j)] for j in range(shape[i])] for i in range(len(shape))])
    return out


def catalan(n):
    return comb(2 * n, n) // (n + 1)


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def main():
    print("=" * 72)
    print("00000000416 - orbits of evacuation on standard Young tableaux")
    print("             of two-row shape (n, n)")
    print("=" * 72)

    print()
    print("1. The standard Young tableaux of shape (2,2)")
    print("-" * 72)
    t22 = standard_tableaux((2, 2))
    for t in t22:
        print("   ", t)
    print(f"   count = {len(t22)}")
    assert len(t22) == 2, "shape (2,2) must carry exactly two tableaux"
    print("   -> C_2 = 2, confirmed by enumeration.")

    print()
    print("2. What the conjecture requires at n = 2")
    print("-" * 72)
    orbits = 2 ** (2 - 1)
    length_two = fib(2 - 1)
    need = 2 * length_two + 1 * (orbits - length_two)
    print(f"   orbits claimed by (a):                 {orbits}")
    print(f"   orbits of length 2 claimed by (c):     {length_two}")
    print(f"   tableaux required: 1*2 + 1*1        >= {need}")
    print(f"   tableaux actually available:            {len(t22)}")
    print()
    if need > len(t22):
        print(f"   CONTRADICTION: need at least {need}, only {len(t22)} exist.")
        print("   The conjecture is false.")
    else:
        print("   no contradiction - check the argument")

    print()
    print("3. Same comparison for other n (using |T_n| = Catalan(n))")
    print("-" * 72)
    print("   'required' is only a LOWER bound (an orbit longer than 2 would use")
    print("   more tableaux), so 'bound ok' does not mean the claim holds - see 4.")
    print()
    print(f"   {'n':>3}  {'actual C_n':>10}  {'orbits 2^(n-1)':>14}  "
          f"{'len-2 F_(n-1)':>13}  {'required':>9}   verdict")
    for n in range(1, 8):
        cn = catalan(n)
        orb = 2 ** (n - 1)
        f2 = fib(n - 1)
        # lower bound: one orbit of length 2 (2 tableaux) + at least one each
        lo = orb + f2
        verdict = "bound ok" if lo <= cn else f"CONTRADICTION (>= {lo} > {cn})"
        print(f"   {n:>3}  {cn:>10}  {orb:>14}  {f2:>13}  {lo:>9}   {verdict}")
    print()
    print("   Only n = 2 is refuted by this bound alone. That is enough: the")
    print("   conjecture makes an unrestricted claim, and it fails at n = 2.")

    print()
    print("4. Independent second failure at n = 4")
    print("-" * 72)
    print("   If e is an involution, every orbit has length 1 or 2, so (a) and (c)")
    print("   force   |T_n| = 2^(n-1) + F_(n-1).")
    for n in (1, 2, 3, 4, 5):
        cn = catalan(n)
        forced = 2 ** (n - 1) + fib(n - 1)
        flag = "ok" if cn == forced else f"MISMATCH"
        print(f"      n = {n}:  C_n = {cn:>4}   forced = {forced:>4}   {flag}")
    print()
    print("   n = 2 fails without any assumption on e (pure counting).")
    print("   n = 4 fails once one uses that e is an involution.")


if __name__ == "__main__":
    main()
