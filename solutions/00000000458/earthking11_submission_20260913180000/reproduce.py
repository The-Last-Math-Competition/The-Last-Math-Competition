#!/usr/bin/env python3
"""Reproduction script for conjecture 00000000458.

Conjecture (file conjectures/00000000458.md):

    "The absolute value of the Moebius number of the Tamari lattice T_n
     is (n-2)(-1)^n."

Verdict: FALSE.

The Tamari lattice T_n is the set of binary trees with n internal nodes
(equivalently, full binary trees with n+1 leaves), ordered by the
right-rotation order: t <= t' iff t' is obtained from t by a sequence of
right rotations, where a right rotation turns ((A,B),C) into (A,(B,C)) at
any node.

This script enumerates T_n for n = 1..8 and checks:

  * |T_n| = Catalan(n) = C(2n,n)/(n+1)  (1, 2, 5, 14, 42, 132, 429, 1430);
  * the number of cover relations equals (n-1) * Catalan(n) / 2;
  * unique minimum (left comb) and unique maximum (right comb);
  * the lattice property (every pair has a least upper bound and a greatest
    lower bound) for n <= 6;
  * the Moebius number mu(0_hat, 1_hat) = (-1)^(n-1), so |mu| = 1;

and prints the table of |mu(T_n)| against the claimed (n-2)(-1)^n.

Standard library only.  Exits 0 when the conjecture is refuted.
"""

import sys
from math import comb
from functools import lru_cache

LEAF = None


def node(l, r):
    return (l, r)


def size(t):
    if t is LEAF:
        return 0
    return 1 + size(t[0]) + size(t[1])


def trees(n):
    """All binary trees with exactly n internal nodes (Catalan(n) of them)."""
    if n == 0:
        return [LEAF]
    out = []
    for i in range(n):
        for l in trees(i):
            for r in trees(n - 1 - i):
                out.append((l, r))
    return out


def rotations(t):
    """All trees obtained from t by one right rotation at any node."""
    out = []
    if t is LEAF:
        return out
    l, r = t
    if l is not LEAF:
        a, b = l
        out.append((a, (b, r)))          # rotate at the root
    for l2 in rotations(l):
        out.append((l2, r))              # rotate inside the left subtree
    for r2 in rotations(r):
        out.append((l, r2))              # rotate inside the right subtree
    return out


def catalan(n):
    return comb(2 * n, n) // (n + 1)


def le_closure(ts, idx):
    """Reflexive-transitive closure of the right-rotation relation.

    Returns `le` with le[i][j] True iff ts[i] <= ts[j] in the Tamari order.
    """
    N = len(ts)
    le = [[False] * N for _ in range(N)]
    for i in range(N):
        le[i][i] = True
    for t in ts:
        for t2 in rotations(t):
            le[idx[t]][idx[t2]] = True
    # Floyd-Warshall transitive closure
    for k in range(N):
        rk = le[k]
        for i in range(N):
            if le[i][k]:
                ri = le[i]
                for j in range(N):
                    if rk[j]:
                        ri[j] = True
    return le


def mobius_bottom_top(N, le):
    """mu(bottom, top) by mu(x,x)=1, mu(x,z) = -sum_{x<=y<z} mu(x,y)."""
    bottom = next(i for i in range(N) if all(le[i][j] for j in range(N)))
    top = next(j for j in range(N) if all(le[i][j] for i in range(N)))
    below = [[j for j in range(N) if le[i][j]] for i in range(N)]

    @lru_cache(maxsize=None)
    def mu(x, z):
        if x == z:
            return 1
        return -sum(mu(x, y)
                    for y in below[x]
                    if y != z and le[y][z])

    return bottom, top, mu(bottom, top)


def is_lattice(N, le):
    """Every pair has a unique least upper bound and greatest lower bound."""
    for a in range(N):
        for b in range(N):
            ubs = [u for u in range(N) if le[a][u] and le[b][u]]
            glbs = [u for u in range(N) if le[u][a] and le[u][b]]
            if not ubs or not glbs:
                return False
            lubs = [u for u in ubs if all(le[u][w] for w in ubs)]
            glbs2 = [g for g in glbs if all(le[w][g] for w in glbs)]
            if len(lubs) != 1 or len(glbs2) != 1:
                return False
    return True


def main():
    print("Tamari lattice T_n: binary trees with n internal nodes,")
    print("right-rotation order.  Catalan(n) = C(2n,n)/(n+1).")
    print()
    header = ("n", "|T_n|", "Cat(n)", "covers", "(n-1)Cat/2", "min/max",
              "mu", "|mu|", "claim (n-2)(-1)^n")
    widths = (3, 7, 7, 7, 11, 8, 4, 5, 18)
    fmt = "  ".join("{:<%d}" % w for w in widths)
    print(fmt.format(*header))
    print("-" * (sum(widths) + 2 * len(widths)))

    all_ok = True
    claims_match = 0

    for n in range(1, 9):
        ts = trees(n)
        idx = {t: i for i, t in enumerate(ts)}
        N = len(ts)
        le = le_closure(ts, idx)

        covers = len({(idx[t], idx[t2]) for t in ts for t2 in rotations(t)})
        expected_covers = (n - 1) * catalan(n) // 2
        mins = [i for i in range(N) if all(le[i][j] for j in range(N))]
        maxs = [j for j in range(N) if all(le[i][j] for i in range(N))]
        bottom, top, mu = mobius_bottom_top(N, le)

        cat_ok = (N == catalan(n))
        cov_ok = (covers == expected_covers)
        ext_ok = (len(mins) == 1 and len(maxs) == 1)
        lat_ok = is_lattice(N, le) if n <= 6 else True
        mu_ok = (mu == (-1) ** (n - 1))
        all_ok = all_ok and cat_ok and cov_ok and ext_ok and lat_ok and mu_ok

        claim = (n - 2) * (-1) ** n
        if abs(mu) == claim:
            claims_match += 1

        print(fmt.format(
            str(n), str(N), str(catalan(n)), str(covers), str(expected_covers),
            "yes" if ext_ok else "NO", str(mu), str(abs(mu)), str(claim)))

    print()
    print("Enumeration checks:")
    print("  |T_n| = Catalan(n) for n = 1..8          : %s"
          % ("OK" if all_ok else "FAILED"))
    print("  cover counts = (n-1)Catalan(n)/2          : checked above")
    print("  unique minimum and maximum                : checked above")
    print("  lattice property for n <= 6               : checked above")
    print("  mu(0_hat,1_hat) = (-1)^(n-1), |mu| = 1    : checked above")

    print()
    print("Sign contradiction (independent of enumeration):")
    for n in (3, 5, 7):
        claim = (n - 2) * (-1) ** n
        print("  n = %d: (n-2)(-1)^n = %d is negative,"
              " but an absolute value is >= 0." % (n, claim))

    # The conjecture holds only if |mu| = (n-2)(-1)^n for all n in range.
    refuted = (not all_ok) or (claims_match < 8)

    print()
    if refuted and all_ok:
        print("PASS: conjecture 00000000458 is REFUTED.")
        print("      |mu(T_n)| = 1 for all n = 1..8, while (n-2)(-1)^n is")
        print("      1, 0, -1, 2, -3, 4, -5, 6: it agrees only at n = 1")
        print("      and is negative for odd n > 2, so it cannot be an")
        print("      absolute value.")
        return 0
    if not all_ok:
        print("FAIL: enumeration self-check failed.")
        return 1
    print("FAIL: conjecture not refuted in range 1..8.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
