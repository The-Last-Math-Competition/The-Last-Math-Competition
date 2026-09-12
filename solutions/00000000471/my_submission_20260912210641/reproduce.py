#!/usr/bin/env python3
"""
Reproduces the refutation of conjecture 00000000471.

The conjecture concerns K_n^{(3)}, the complete 3-uniform hypergraph on n
vertices (its edge set is all C(n,3) triples).  A *hypertree* is a minimally
connected subhypergraph of that edge set, and t(K_n^{(3)}) counts them.  The
conjectured closed form is

    t(K_n^{(3)}) = n^{C(n-1,2) - 1} * prod_{i=1}^{n-1} (i^2 - i + 1),

asserted to cover all known values for n <= 6.

Two independent refutations are checked here.

(1) TRIVIAL BOUND.  A hypertree is a subhypergraph, i.e. a subset of the
    C(n,3) edges, so t(K_n^{(3)}) <= 2^{C(n,3)}.  The conjectured formula
    already exceeds this bound at n = 3 (it gives 3 against at most 2), and it
    exceeds it by a factor of more than 55,000 at n = 6.  This argument uses
    nothing about connectedness or minimality, so it is immune to any
    disagreement about how those words are read.

(2) EXACT ENUMERATION.  At n = 3 the edge set of K_3^{(3)} has exactly one
    member, so the only connected subhypergraph is that single edge, and it is
    minimal.  Hence t(K_3^{(3)}) = 1, while the formula gives 3.  Exhaustive
    enumeration at n = 4 and n = 5 gives 6 and 25 respectively, against 336 and
    853125 from the formula.

Standard library only.  Run with:  python3 reproduce.py
"""
from itertools import combinations
from math import comb, log10


def hyperedges(n, r=3):
    """All r-subsets of {0, ..., n-1}, i.e. the edge set of K_n^{(r)}."""
    return list(combinations(range(n), r))


def is_connected(n, subset):
    """A subhypergraph is connected if its edges cover every vertex and the
    graph obtained by replacing each edge with a clique is connected."""
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry

    covered = set()
    for e in subset:
        covered.update(e)
        for v in e[1:]:
            union(e[0], v)
    if len(covered) != n:
        return False
    return len({find(v) for v in range(n)}) == 1


def is_minimally_connected(n, subset):
    """Connected, and removing any single edge destroys connectedness."""
    if not is_connected(n, subset):
        return False
    for i in range(len(subset)):
        smaller = subset[:i] + subset[i + 1:]
        if is_connected(n, smaller):
            return False
    return True


def count_hypertrees(n, r=3):
    """Exhaustive count over all 2^{C(n,r)} subhypergraphs."""
    edges = hyperedges(n, r)
    total = 0
    for k in range(len(edges) + 1):
        for subset in combinations(edges, k):
            if is_minimally_connected(n, subset):
                total += 1
    return total


def f(i):
    return i * i - i + 1


def formula(n):
    """The conjectured closed form."""
    exponent = comb(n - 1, 2) - 1
    prod = 1
    for i in range(1, n):
        prod *= f(i)
    return (n ** exponent) * prod


def main():
    print("=" * 74)
    print("00000000471 - the number of hypertrees of K_n^{(3)}")
    print("=" * 74)

    print()
    print("0. The conjectured formula, expanded")
    print("-" * 74)
    print(f"   {'n':>3}  {'C(n-1,2)-1':>11}  {'n^exp':>14}  "
          f"{'prod f(i)':>12}  {'formula':>16}")
    for n in range(3, 7):
        exp = comb(n - 1, 2) - 1
        pr = 1
        for i in range(1, n):
            pr *= f(i)
        print(f"   {n:>3}  {exp:>11}  {n ** exp:>14}  {pr:>12}  {formula(n):>16}")

    print()
    print("1. REFUTATION (1) - the trivial bound t <= 2^{C(n,3)}")
    print("-" * 74)
    print("   A hypertree is a subhypergraph, i.e. a subset of the C(n,3) edges.")
    print("   So the number of them cannot exceed the number of subsets.")
    print()
    print(f"   {'n':>3}  {'C(n,3)':>7}  {'2^C(n,3)':>14}  {'formula':>16}  "
          f"{'formula / bound':>17}  verdict")
    print()
    bound_fails = []
    for n in range(3, 7):
        m = comb(n, 3)
        b = 2 ** m
        v = formula(n)
        ok = v <= b
        if not ok:
            bound_fails.append(n)
        ratio = v / b
        print(f"   {n:>3}  {m:>7}  {b:>14}  {v:>16}  {ratio:>16.1f}x  "
              f"{'ok' if ok else 'IMPOSSIBLE'}")
    print()
    print(f"   The formula is impossible for n in {bound_fails} - the whole range")
    print("   the conjecture claims to cover.  This needs no enumeration and no")
    print("   reading of 'connected' or 'minimal'.")

    print()
    print("   How far does the bound refutation reach?  (log10, so that the")
    print("   numbers stay readable)")
    print()
    print(f"   {'n':>3}  {'log10 bound':>12}  {'log10 formula':>14}  verdict")
    for n in range(3, 21):
        b = comb(n, 3) * log10(2)
        fm = (comb(n - 1, 2) - 1) * log10(n) + sum(log10(f(i)) for i in range(1, n))
        print(f"   {n:>3}  {b:>12.1f}  {fm:>14.1f}  "
              f"{'bound violated' if fm > b else '-'}")
    print()
    print("   The bound is violated for 3 <= n <= 13 and holds from n = 14 on.")
    print("   One counterexample is enough, and the conjecture claims n <= 6 --")
    print("   all six of which are inside the violated range.")

    print()
    print("2. REFUTATION (2) - exact enumeration by brute force")
    print("-" * 74)
    print(f"   {'n':>3}  {'edges':>6}  {'subhypergraphs':>15}  "
          f"{'hypertrees':>11}  {'formula':>16}  verdict")
    print()
    for n in (3, 4, 5):
        edges = hyperedges(n)
        t = count_hypertrees(n)
        v = formula(n)
        print(f"   {n:>3}  {len(edges):>6}  {2 ** len(edges):>15}  {t:>11}  "
              f"{v:>16}  {'ok' if t == v else 'MISMATCH'}")
    print()
    print("   (n = 6 has 2^20 = 1048576 subhypergraphs; refutation (1) already")
    print("    settles it, so we do not enumerate it.)")

    print()
    print("3. The case n = 3 in full")
    print("-" * 74)
    e3 = hyperedges(3)
    print(f"   edge set of K_3^{{(3)}}: {e3}   (C(3,3) = {len(e3)} edge)")
    subs = [s for k in range(len(e3) + 1)
            for s in combinations(e3, k)]
    for s in subs:
        print(f"      subhypergraph {str(s):<16} connected={is_connected(3, s)!s:<5} "
              f"minimal={is_minimally_connected(3, s)}")
    t3 = count_hypertrees(3)
    print(f"   t(K_3^{{(3)}}) = {t3}")
    print(f"   formula(3)     = {formula(3)}")
    assert t3 == 1, "n = 3 must have exactly one hypertree"
    assert formula(3) == 3, "formula must give 3 at n = 3"
    print(f"   {t3} != {formula(3)}  ->  the conjecture is FALSE at n = 3.")

    print()
    print("4. The case n = 4 in full")
    print("-" * 74)
    t4 = count_hypertrees(4)
    print(f"   t(K_4^{{(3)}}) = {t4}    (all minimally connected subhypergraphs:")
    edges4 = hyperedges(4)
    for k in range(len(edges4) + 1):
        for s in combinations(edges4, k):
            if is_minimally_connected(4, s):
                print("      ", [tuple(x + 1 for x in e) for e in s])
    print(f"   formula(4)     = {formula(4)}")
    assert t4 == 6, "n = 4 must have exactly six hypertrees"

    print()
    print("5. The case n = 5")
    print("-" * 74)
    t5 = count_hypertrees(5)
    print(f"   t(K_5^{{(3)}}) = {t5}")
    print(f"   formula(5)     = {formula(5)}")
    assert t5 == 25, "n = 5 must have exactly 25 hypertrees"

    print()
    print("=" * 74)
    print("CONCLUSION: conjecture 00000000471 is FALSE.")
    print("  - it fails the trivial counting bound at every n in 3..6;")
    print("  - it fails by exact enumeration at n = 3 (1 vs 3), n = 4 (6 vs 336)")
    print("    and n = 5 (25 vs 853125).")
    print("=" * 74)


if __name__ == "__main__":
    main()
