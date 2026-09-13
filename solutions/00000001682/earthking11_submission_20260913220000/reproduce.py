#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001682.

    Conjecture (as filed):
        "The pancyclicity threshold of generalized Petersen graphs G(n, 2) has
         a complete classification for n >= 11 (G(n,2) pancyclic)."
        中文: 广义 Petersen 图 G(n, 2) 的满圈泛环性(pancyclic)阈值为 n >= 11 的
              完全分类(G(n,2) 泛环)。

The conjecture is FALSE.  This script verifies, by exhaustive brute force:

  * G(11, 2) is triangle-free.  Its vertex set has 2*11 = 22 elements, so
    pancyclicity would require a cycle of length 3; there is none.  Hence
    G(11, 2) is NOT pancyclic, refuting the claim that G(n, 2) is pancyclic
    for all n >= 11.

  * In fact G(n, 2) is not pancyclic for any n = 5, ..., 16; the script prints
    the exact list of cycle lengths 3, ..., 2n that are missing, and checks
    that every one of these graphs misses at least one length.

Definitions (standard generalized Petersen graph GP(n, k)):
    vertices u_0..u_{n-1} and v_0..v_{n-1};
    outer edges u_i u_{i+1},  spokes u_i v_i,  inner edges v_i v_{i+k},
    all indices modulo n.
A graph is pancyclic iff it has a cycle of every length 3, 4, ..., |V| = 2n.

Cycle existence for length L is decided exactly by two independent methods:
  * for small L (at most SUBSET_LIMIT vertex subsets): exhaustive enumeration
    of all C(2n, L) vertex sets, testing each induced subgraph for a
    Hamiltonian cycle with a DFS (a cycle of length L is a Hamiltonian cycle of
    its own vertex set);
  * for larger L: a DFS cycle search over the graph, canonicalising on the
    smallest vertex of the cycle and pruning with a degree/cover condition.
Both methods are exhaustive; they are cross-checked against each other for the
small lengths.

Standard library only.  Python 3.8+.  Exits non-zero if any check fails.
"""

import itertools
import math
import sys

sys.setrecursionlimit(1000000)

# Use exhaustive subset enumeration when C(2n, L) is at most this bound.
SUBSET_LIMIT = 200000


# ----------------------------------------------------------------------
# Graph construction
# ----------------------------------------------------------------------

def gp(n, k=2):
    """Adjacency lists of GP(n, k); u_i = 2i, v_i = 2i + 1."""
    N = 2 * n
    adj = [set() for _ in range(N)]

    def u(i):
        return 2 * i

    def v(i):
        return 2 * i + 1

    def add(a, b):
        adj[a].add(b)
        adj[b].add(a)

    for i in range(n):
        add(u(i), u((i + 1) % n))      # outer edge u_i -- u_{i+1}
        add(u(i), v(i))                # spoke      u_i -- v_i
        add(v(i), v((i + k) % n))      # inner edge v_i -- v_{i+k}
    return [sorted(s) for s in adj], N


# ----------------------------------------------------------------------
# Triangles
# ----------------------------------------------------------------------

def count_triangles(adj, N):
    """Number of (unordered) triangles: all C(N, 3) triples are tested."""
    cnt = 0
    for a, b, c in itertools.combinations(range(N), 3):
        if b in adj[a] and c in adj[a] and c in adj[b]:
            cnt += 1
    return cnt


# ----------------------------------------------------------------------
# Cycle existence, method 1: exhaustive over vertex subsets
# ----------------------------------------------------------------------

def has_hamiltonian_cycle(adj, S):
    """Does the subgraph induced on the vertex set S have a Hamiltonian cycle?

    Exact DFS from the smallest vertex of S; used for |S| small.
    """
    S = set(S)
    if len(S) < 3:
        return False
    start = min(S)
    target = len(S)

    def rec(cur, visited):
        if len(visited) == target:
            return start in adj[cur]
        for w in adj[cur]:
            if w in S and w not in visited:
                visited.add(w)
                if rec(w, visited):
                    return True
                visited.discard(w)
        return False

    return rec(start, {start})


def has_cycle_subset(adj, N, L):
    """Exhaustively test every C(N, L) vertex subset for an L-cycle."""
    for S in itertools.combinations(range(N), L):
        if has_hamiltonian_cycle(adj, S):
            return True
    return False


# ----------------------------------------------------------------------
# Cycle existence, method 2: DFS cycle search
# ----------------------------------------------------------------------

def has_cycle_search(adj, N, L):
    """DFS search for a simple cycle with exactly L vertices.

    Each cycle is generated once, from its smallest vertex s; the walk only
    visits vertices > s.  When the remaining allowed vertices must all be used
    (the Hamiltonian-path stage) a necessary degree/cover condition prunes the
    search.  The search is exhaustive (no valid cycle is pruned).
    """
    if L < 3 or L > N:
        return False
    for s in range(0, N - L + 1):
        allowed = [x for x in range(s + 1, N)]

        def rec(cur, path, visited):
            length = len(path)
            if length == L:
                return s in adj[cur]
            rem = [x for x in allowed if x not in visited]
            if length + len(rem) < L:
                return False
            if length + len(rem) == L:
                # every remaining vertex must lie on the path
                for x in rem:
                    if len([y for y in adj[x]
                            if y in rem or y == cur or y == s]) < 2:
                        return False
                if not any(y in rem for y in adj[s]):
                    return False
                if not any(y in rem for y in adj[cur]):
                    return False
            for w in adj[cur]:
                if w <= s or w in visited:
                    continue
                visited.add(w)
                path.append(w)
                if rec(w, path, visited):
                    return True
                path.pop()
                visited.discard(w)
            return False

        if rec(s, [s], {s}):
            return True
    return False


def has_cycle(adj, N, L):
    """Exact decision of L-cycle existence, by the cheaper of the two methods."""
    if L > N or L < 3:
        return False
    if math.comb(N, L) <= SUBSET_LIMIT:
        return has_cycle_subset(adj, N, L)
    return has_cycle_search(adj, N, L)


# ----------------------------------------------------------------------
# The independently computed expectation (for verification)
# ----------------------------------------------------------------------

EXPECTED_MISSING = {
    5: [3, 4, 7, 10],
    6: [4],
    7: [3, 4],
    8: [3, 6],
    9: [3, 4, 6],
    10: [3, 4, 6, 7, 19],
    11: [3, 4, 6, 7, 22],
    12: [3, 4, 7],
    13: [3, 4, 6, 7],
    14: [3, 4, 6],
    15: [3, 4, 6, 7],
    16: [3, 4, 6, 7, 31],
}


def main():
    checks = []

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))

    # ------------------------------------------------------------------
    # 1. The witness G(11, 2)
    # ------------------------------------------------------------------
    adj11, N11 = gp(11, 2)
    assert N11 == 22
    tri11 = count_triangles(adj11, N11)

    check("G(11,2) has 22 vertices",
          N11 == 22, f"|V| = {N11} = 2*11")
    check("G(11,2) is triangle-free (all C(22,3) = 1540 triples tested)",
          tri11 == 0,
          f"C(22,3) = {math.comb(22, 3)} triples, triangles found = {tri11}")
    # The assertion demanded verbatim by the problem statement.
    assert tri11 == 0, "G(11,2) must be triangle-free"
    assert math.comb(22, 3) == 1540

    missing11 = [L for L in range(3, N11 + 1) if not has_cycle(adj11, N11, L)]
    check("G(11,2) missing lengths are exactly {3,4,6,7,22}",
          missing11 == [3, 4, 6, 7, 22],
          f"missing = {missing11}")
    check("G(11,2) is NOT pancyclic (lengths 3..22 not all present)",
          len(missing11) > 0,
          f"{len(missing11)} lengths missing: {missing11}; "
          f"in particular length 3 (a triangle) is absent")
    check("G(11,2) is not a 3-cycle: no triangle => no cycle of length 3",
          not has_cycle(adj11, N11, 3),
          "has_cycle(G(11,2), 3) = False")

    # ------------------------------------------------------------------
    # 2. All n = 5, ..., 16
    # ------------------------------------------------------------------
    table = {}
    tri_counts = {}
    for n in range(5, 17):
        adj, N = gp(n, 2)
        tri_counts[n] = count_triangles(adj, N)
        missing = [L for L in range(3, N + 1) if not has_cycle(adj, N, L)]
        table[n] = missing

    check("computed missing-length table matches independent expectation",
          all(table[n] == EXPECTED_MISSING[n] for n in range(5, 17)),
          "table reproduced exactly")

    check("G(5,2) (Petersen) misses exactly {3,4,7,10}",
          table[5] == [3, 4, 7, 10],
          f"missing = {table[5]}")

    positive = [n for n in range(5, 17) if tri_counts[n] > 0]
    check("among n = 5..16, a triangle occurs only for n = 6",
          positive == [6],
          f"n with triangles: {positive}; counts = "
          f"{ {n: tri_counts[n] for n in range(5, 17)} }; "
          "indeed G(n,2) has a triangle iff n | 6")

    non_pancyclic = [n for n in range(5, 17) if table[n]]
    check("G(n,2) is NOT pancyclic for every n = 5..16",
          non_pancyclic == list(range(5, 17)),
          f"non-pancyclic n = {non_pancyclic}")

    check("the conjecture's threshold claim fails at n = 11",
          table[11] != [] and 11 >= 11,
          "n = 11 >= 11 but G(11,2) is not pancyclic, so the claim "
          "'G(n,2) pancyclic for n >= 11' is false")

    # ------------------------------------------------------------------
    # 3. Cross-check the two cycle-existence methods on small lengths
    # ------------------------------------------------------------------
    cross_ok = True
    cross_detail = []
    for n in range(5, 17):
        adj, N = gp(n, 2)
        for L in range(3, 6):
            if L > N:
                continue
            a = has_cycle_subset(adj, N, L)
            b = has_cycle_search(adj, N, L)
            if a != b:
                cross_ok = False
                cross_detail.append((n, L, a, b))
    check("subset enumeration and DFS cycle search agree for L = 3,4,5, all n",
          cross_ok,
          "all agree" if cross_ok else f"mismatches: {cross_detail}")

    # ------------------------------------------------------------------
    # 4. Report
    # ------------------------------------------------------------------
    line = "=" * 78
    print(line)
    print("Disproof of conjecture 00000001682 -- reproduction")
    print(line)

    print("\n[1] Witness G(11, 2)")
    print(f"    vertices          : {N11}")
    print(f"    triangles         : {tri11}  "
          f"(all C(22,3) = {math.comb(22, 3)} triples tested)")
    print(f"    missing lengths   : {missing11}")
    print("    => G(11,2) is triangle-free, hence not pancyclic "
          "(a pancyclic 22-vertex graph needs a 3-cycle).")
    print("    => the claim 'G(n,2) is pancyclic for all n >= 11' is FALSE.")

    print("\n[2] Missing cycle lengths of G(n, 2), n = 5..16")
    print(f"    {'n':>3}  {'|V|=2n':>6}  {'triangles':>9}  missing lengths")
    print("    " + "-" * 62)
    for n in range(5, 17):
        N = 2 * n
        print(f"    {n:>3}  {N:>6}  {tri_counts[n]:>9}  {table[n]}")

    print("\n[3] Checks")
    all_ok = True
    for name, ok, detail in checks:
        all_ok = all_ok and ok
        print(f"    [{'ok  ' if ok else 'FAIL'}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok:
        print("PASS: all checks verified; conjecture 00000001682 is FALSE.")
        print("  G(11,2) is triangle-free and has no 3-cycle, so it is not")
        print("  pancyclic; moreover no G(n,2) with 5 <= n <= 16 is pancyclic.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
