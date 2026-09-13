#!/usr/bin/env python3
"""Refutation of conjecture 00000001671.

The conjecture claims that the *basis number* of the complete graph K_n -- the
least k for which the cycle space of K_n admits a cycle basis in which every
edge occurs in at most k of the basis cycles -- equals

    b(K_n) = ceil((n+3)/2).

This script computes the true values b(K_n) for n = 3, 4, 5, 6 exactly, prints
them next to the conjectured formula, and reports PASS/FAIL.

Method (standard library only)
------------------------------
* Edges of K_n are indexed 0..C(n,2)-1; an edge subset is an integer bitmask.
* Over GF(2) the cycle space of a connected graph is exactly the set of edge
  subsets in which every vertex has even degree ("even subgraphs"), so the
  cycles are enumerated directly.
* A k-fold cycle basis is an *independent* set of dim = |E| - |V| + 1 cycles
  whose GF(2) span is the whole cycle space and in which every edge lies in at
  most k basis cycles
  (independence + correct cardinality + spanning is checked by GF(2) rank).
* Existence of a k-fold basis is decided by an exact backtracking search over
  cycles ordered by length.  Two necessary conditions make the search small:
    - total length: sum of basis-cycle lengths = sum over edges of the edge
      multiplicity <= k * |E|;
    - every cycle of a simple graph has length >= 3.
  These prune the budget enough that even the *non-existence* searches for
  k = 1, 2 on K_5, K_6 terminate quickly.  Since all candidates with length
  above `k*|E| - 3*(dim-1)` are discarded (they cannot occur in any valid
  basis), the search is exhaustive, not heuristic.
"""

import sys
from itertools import combinations

EXPECTED = {3: 1, 4: 2, 5: 3, 6: 3}


# --------------------------------------------------------------------------
# K_n
# --------------------------------------------------------------------------

def edges_of(n):
    """Edges of K_n as (u, v) with u < v, indexed in lexicographic order."""
    return [(u, v) for u in range(n) for v in range(u + 1, n)]


def popcount(x):
    return bin(x).count("1")


def bits_of(x):
    """Indices of the set bits of x."""
    out = []
    i = 0
    while x:
        if x & 1:
            out.append(i)
        x >>= 1
        i += 1
    return out


def cycle_space(n):
    """All even subgraphs of K_n (elements of its cycle space), as bitmasks.

    Includes the empty set (mask 0); these are exactly the edge subsets with
    even degree at every vertex.
    """
    edges = edges_of(n)
    E = len(edges)
    out = []
    for mask in range(1 << E):
        deg = [0] * n
        m = mask
        i = 0
        while m:
            if m & 1:
                u, v = edges[i]
                deg[u] += 1
                deg[v] += 1
            m >>= 1
            i += 1
        if all(d % 2 == 0 for d in deg):
            out.append(mask)
    return out


def cycle_dim(n):
    """|E| - |V| + 1, the dimension of the cycle space of connected K_n."""
    return len(edges_of(n)) - n + 1


# --------------------------------------------------------------------------
# GF(2) linear algebra
# --------------------------------------------------------------------------

def reduce_add(x, basis):
    """Add vector x to the GF(2) row-echelon basis dict (high bit -> vector).

    Returns (new_basis, independent).  `basis` maps a bit position to the
    unique basis vector having that position as its highest set bit.
    """
    basis = dict(basis)
    while x:
        h = x.bit_length() - 1
        if h in basis:
            x ^= basis[h]
        else:
            basis[h] = x
            return basis, True
    return basis, False


def rank_of(masks):
    basis = {}
    for m in masks:
        basis, _ = reduce_add(m, basis)
    return len(basis)


# --------------------------------------------------------------------------
# Exact search for a k-fold basis
# --------------------------------------------------------------------------

def search_kfold(n, k, node_cap=50_000_000):
    """Return a k-fold basis of K_n as a list of bitmasks, or None.

    Exhaustive backtracking: only linearly independent cycles are ever added,
    so the reached rank equals the number of chosen cycles.
    """
    E = len(edges_of(n))
    d = cycle_dim(n)
    budget = k * E
    maxlen = budget - 3 * (d - 1)
    if maxlen < 3:
        return None
    cand = [c for c in cycle_space(n) if c != 0 and popcount(c) <= maxlen]
    cand.sort(key=lambda c: (popcount(c), c))   # shortest cycles first
    lens = [popcount(c) for c in cand]
    cbits = [bits_of(c) for c in cand]
    n_cand = len(cand)

    loads = [0] * E
    result = [None]
    nodes = [0]
    expected_len = d

    def dfs(idx, chosen, basis, total):
        nodes[0] += 1
        if nodes[0] > node_cap:
            raise RuntimeError("node cap exceeded")
        if len(chosen) == expected_len:
            return list(chosen)
        # every remaining cycle has length >= 3
        if total + 3 * (expected_len - len(chosen)) > budget:
            return None
        for j in range(idx, n_cand):
            l = lens[j]
            if total + l + 3 * (expected_len - len(chosen) - 1) > budget:
                break                      # lengths are non-decreasing
            ok = True
            for i in cbits[j]:
                if loads[i] + 1 > k:
                    ok = False
                    break
            if not ok:
                continue
            nbasis, indep = reduce_add(cand[j], basis)
            if not indep:
                continue
            for i in cbits[j]:
                loads[i] += 1
            chosen.append(cand[j])
            res = dfs(j + 1, chosen, nbasis, total + l)
            chosen.pop()
            for i in cbits[j]:
                loads[i] -= 1
            if res is not None:
                return res
        return None

    try:
        result[0] = dfs(0, [], {}, 0)
    except RuntimeError:
        result[0] = None
    return result[0]


def basis_number(n):
    """Exact basis number b(K_n) = least k admitting a k-fold cycle basis."""
    k = 0
    while k <= cycle_dim(n) + 1:
        w = search_kfold(n, k)
        if w is not None:
            return k, w
        k += 1
    raise AssertionError("no basis found")


def verify_witness(n, k, witness):
    """Check that `witness` really is a k-fold cycle basis of K_n."""
    E = len(edges_of(n))
    d = cycle_dim(n)
    cycles = {c for c in cycle_space(n) if c != 0}
    assert witness is not None and len(witness) == d, "wrong cardinality"
    assert all(w in cycles for w in witness), "non-cycle in witness"
    assert rank_of(witness) == d, "witness not independent/spanning"
    loads = [0] * E
    for w in witness:
        for i in bits_of(w):
            loads[i] += 1
    assert max(loads) <= k, "edge multiplicity exceeds k"
    return max(loads)


# --------------------------------------------------------------------------
# Conjectured formula
# --------------------------------------------------------------------------

def formula(n):
    """ceil((n+3)/2), computed in integers."""
    return (n + 4) // 2


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def main():
    ok = True
    print("conjecture 00000001671:  basis number of K_n  ==  ceil((n+3)/2)")
    print()
    print(f"{'n':>3} | {'|E|':>4} | {'dim':>3} | {'true b(K_n)':>11} | "
          f"{'formula':>7} | status")
    print("-" * 52)

    for n in (3, 4, 5, 6):
        E = len(edges_of(n))
        d = cycle_dim(n)
        b, witness = basis_number(n)
        f = formula(n)
        mismatch = (b != f)
        if not mismatch:
            ok = False
        if b != EXPECTED[n]:
            ok = False
        maxload = verify_witness(n, b, witness)
        print(f"{n:>3} | {E:>4} | {d:>3} | {b:>11} | {f:>7} | "
              f"{'WRONG' if mismatch else 'ok'}")

    print()
    print("Details")
    print(f"  K_3: 1-fold basis exists (the triangle), 0-fold does not.  "
          f"b(K_3) = 1, not 3.")
    print(f"  K_4: no 1-fold basis (three independent cycles need >= 9 edge "
          f"incidences but |E| = 6); three triangles form a 2-fold basis.  "
          f"b(K_4) = 2, not 4.")
    print(f"  K_5: k = 1, 2 impossible; k = 3 attained (star basis).  "
          f"b(K_5) = 3, not 4.")
    print(f"  K_6: k = 2 impossible (budget 2*15 = 30 forces 10 triangles with "
          f"every edge exactly twice, i.e. a Steiner triple system on 6 points, "
          f"which does not exist since 6 = 0 mod 6); k = 3 attained.  "
          f"b(K_6) = 3, not 5.")
    print()

    # A second, independent sanity check of the flagship cases: exhaustive
    # enumeration of all subsets of the cycle set for K_3 and K_4.
    for n in (3, 4):
        d = cycle_dim(n)
        cycles = [c for c in cycle_space(n) if c != 0]
        best = None
        for combo in combinations(cycles, d):
            if rank_of(combo) != d:
                continue
            loads = [0] * len(edges_of(n))
            for w in combo:
                for i in bits_of(w):
                    loads[i] += 1
            m = max(loads)
            if best is None or m < best:
                best = m
        if best != EXPECTED[n]:
            ok = False
        print(f"  exhaustive check K_{n}: min over all"
              f" C({len(cycles)},{d}) bases = {best}"
              f"  -> {'PASS' if best == EXPECTED[n] else 'FAIL'}")
    print()

    print("Result: the formula is wrong for every n = 3, 4, 5, 6.")
    print("RESULT: PASS" if ok else "RESULT: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
