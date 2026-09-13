#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000008234.

    Definition: swap_graph is the exchange graph of envy-free-up-to-one-good
    (EF1) allocations of m indivisible goods to n agents: vertices are the EF1
    allocations, edges are single-good transfers.
    Conjecture: under arbitrary monotone valuations swap_graph is connected
    with diameter at most m(n-1); [further conjuncts about EF1+Pareto, EFX, ...].

This script disproves the FIRST conjunct, hence the conjunction, by exhaustive
enumeration of the smallest instances with unit additive valuations
    v_i(g_j) = 1   for all agents i and goods j,
which are monotone.

Two independent ingredients are checked:

  * (n, m) = (2, 2).  There are 2^2 = 4 allocations.  EF1 (computed literally
    from the definition: for every ordered pair of agents, some good can be
    removed from the envied bundle to eliminate the envy) holds exactly for the
    two diagonal allocations, which differ in BOTH coordinates (Hamming
    distance 2).  Any single-good transfer leaves a (2, 0) or (0, 2) split,
    which is not EF1.  Hence swap_graph has ZERO edges: it is disconnected, its
    diameter is infinite, and the claimed bound m(n-1) = 2 fails.

  * (n, m) = (3, 3).  Same phenomenon with 3 agents: the 6 EF1 allocations
    (one good each) are pairwise at Hamming distance >= 2, so swap_graph again
    has zero edges and is disconnected.  The n = 2 case is therefore not a
    degenerate artifact.

Strengthening (the general n | m family).  For unit valuations, EF1 is
equivalent to (max bundle size - min bundle size) <= 1.  If n divides m, every
EF1 allocation is exactly balanced (each agent holds m/n goods), and any
single-good transfer creates a gap of 2, so swap_graph has NO edges at all.
The script verifies disconnection for (n, m) = (2,2), (2,4), (2,6), (3,3),
(4,4).

Standard library only.  Python 3.8+.  Runs in seconds.
"""

from itertools import product


# ---------------------------------------------------------------------------
# unit additive valuations, EF1, and the swap graph
# ---------------------------------------------------------------------------

def bundle_sizes(alloc, n, m):
    """Sizes of the n bundles; alloc[g] is the owner of good g.

    Under unit additive valuations the value of a bundle is its cardinality.
    """
    sizes = [0] * n
    for g in range(m):
        sizes[alloc[g]] += 1
    return sizes


def is_ef1(alloc, n, m):
    """EF1, transcribed literally from the definition.

    For every ordered pair (i, j) of agents, either i does not envy j
    (value_i(A_i) >= value_i(A_j)), or there is a good g in j's bundle with
    value_i(A_j \\ {g}) <= value_i(A_i).  Under unit valuations
    value_i(A_j \\ {g}) = sizes[j] - 1.
    """
    sizes = bundle_sizes(alloc, n, m)
    for i in range(n):
        for j in range(n):
            if sizes[i] < sizes[j]:                       # i envies j
                removable = any(
                    alloc[g] == j and sizes[j] - 1 <= sizes[i]
                    for g in range(m)
                )
                if not removable:
                    return False
    return True


def ef1_gap_characterisation(alloc, n, m):
    """For unit valuations: EF1  <=>  max size - min size <= 1."""
    sizes = bundle_sizes(alloc, n, m)
    return max(sizes) - min(sizes) <= 1


def hamming(a, b):
    """Number of goods whose owner differs; a single-good transfer is distance 1."""
    return sum(1 for x, y in zip(a, b) if x != y)


def all_allocations(n, m):
    """All n^m allocations, as tuples (owner of good 0, ..., owner of good m-1)."""
    return list(product(range(n), repeat=m))


def analyse(n, m):
    """Return (ef1_allocations, edges, components) for the (n, m) instance.

    edges: pairs of EF1 allocations at Hamming distance 1.
    components: number of connected components of swap_graph.
    """
    allocs = all_allocations(n, m)
    ef1s = [a for a in allocs if is_ef1(a, n, m)]
    edges = [
        (x, y)
        for x in ef1s
        for y in ef1s
        if hamming(x, y) == 1
    ]

    # connected components of swap_graph (BFS over the EF1 vertices)
    adj = {x: [y for y in ef1s if hamming(x, y) == 1] for x in ef1s}
    seen = set()
    components = 0
    for x in ef1s:
        if x in seen:
            continue
        components += 1
        stack = [x]
        seen.add(x)
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
    return ef1s, edges, components


# ---------------------------------------------------------------------------

def show(alloc):
    """Render an allocation as the list of bundle contents, e.g. [[0],[1]]."""
    n = max(alloc) + 1
    bundles = [[] for _ in range(n)]
    for g, owner in enumerate(alloc):
        bundles[owner].append(g)
    return "[" + ", ".join("{" + ",".join(str(g) for g in b) + "}" for b in bundles) + "]"


def main():
    checks = []
    line = "=" * 74

    # ------------------------------------------------------------------ 2 x 2
    n, m = 2, 2
    allocs22 = all_allocations(n, m)
    ef1s22, edges22, comps22 = analyse(n, m)

    print(line)
    print("Disproof of conjecture 00000008234 -- reproduction")
    print(line)
    print(f"\n[1] Exhaustive EF1 table for n = {n} agents, m = {m} goods,")
    print("    unit additive valuations v_i(g_j) = 1")
    print("    allocation (goods -> owner)  bundles            sizes  EF1")
    for a in allocs22:
        sizes = bundle_sizes(a, n, m)
        print(f"    {str(a):28s} {show(a):16s} {str(sizes):8s} {'yes' if is_ef1(a, n, m) else 'NO'}")

    # consistency: literal EF1 == size-gap characterisation on every allocation
    gap_ok = all(
        is_ef1(a, n, m) == ef1_gap_characterisation(a, n, m) for a in allocs22
    )
    checks.append((
        "2x2: literal EF1 == (max size - min size <= 1) on all 4 allocations",
        gap_ok,
        "checked the definition against the unit-valuation characterisation",
    ))
    checks.append((
        "2x2: exactly 2 EF1 allocations (the two diagonals)",
        len(ef1s22) == 2,
        f"EF1 allocations: {[show(a) for a in ef1s22]}",
    ))
    checks.append((
        "2x2: zero edges in swap_graph",
        len(edges22) == 0,
        f"{len(edges22)} edges among {len(ef1s22)} EF1 vertices",
    ))
    checks.append((
        "2x2: swap_graph is disconnected (>= 2 components)",
        comps22 >= 2,
        f"{comps22} connected components",
    ))
    checks.append((
        "2x2: the two EF1 allocations differ in BOTH coordinates (distance 2)",
        len(ef1s22) == 2 and hamming(ef1s22[0], ef1s22[1]) == 2,
        f"Hamming distance {hamming(ef1s22[0], ef1s22[1])}",
    ))
    checks.append((
        "2x2: the claimed diameter bound m(n-1) = 2 fails (infinite diameter)",
        2 * (n - 1) == 2 and len(edges22) == 0 and comps22 >= 2,
        "a disconnected graph has no finite diameter",
    ))

    # ------------------------------------------------------------------ 3 x 3
    n3, m3 = 3, 3
    ef1s33, edges33, comps33 = analyse(n3, m3)
    checks.append((
        "3x3: exactly 6 EF1 allocations (one good per agent)",
        len(ef1s33) == 6,
        f"{len(ef1s33)} EF1 allocations among 3^3 = 27 assignments",
    ))
    checks.append((
        "3x3: zero edges in swap_graph",
        len(edges33) == 0,
        f"{len(edges33)} edges among {len(ef1s33)} EF1 vertices",
    ))
    checks.append((
        "3x3: swap_graph is disconnected",
        comps33 >= 2,
        f"{comps33} connected components",
    ))

    # ------------------------------------------------- general n | m family
    family = [(2, 2), (2, 4), (2, 6), (3, 3), (4, 4)]
    table = []
    for (nn, mm) in family:
        effs, eds, cps = analyse(nn, mm)
        table.append((nn, mm, len(effs), len(eds), cps))
    table_ok = all(
        mm % nn == 0                      # n divides m
        and nef >= 2                      # at least two EF1 vertices
        and ned == 0                      # no edges
        and cps >= 2                      # disconnected
        for (nn, mm, nef, ned, cps) in table
    )
    checks.append((
        "n | m family: every listed instance has >=2 EF1 allocations, 0 edges, disconnected",
        table_ok,
        "unit valuations: EF1 allocations are exactly the balanced ones",
    ))

    print("\n[2] The n | m strengthening (unit valuations)")
    print("    For unit valuations, EF1 <=> max bundle size - min bundle size <= 1.")
    print("    If n divides m, every EF1 allocation is balanced (each agent m/n goods),")
    print("    and any single-good transfer creates a gap of 2, so there are no edges.")
    print("    n  m  #EF1  #edges  #components")
    for (nn, mm, nef, ned, cps) in table:
        print(f"    {nn}  {mm}  {nef:4d}  {ned:5d}  {cps:4d}")

    # ------------------------------------------------ hard assertions demanded
    assert len(ef1s22) == 2, "expected exactly two EF1 allocations at (2,2)"
    assert hamming(ef1s22[0], ef1s22[1]) == 2, "expected the diagonals at distance 2"
    assert len(edges22) == 0, "expected zero edges at (2,2)"
    assert comps22 >= 2, "expected swap_graph to be disconnected at (2,2)"
    assert len(edges33) == 0 and comps33 >= 2, "expected zero edges / disconnection at (3,3)"

    # ------------------------------------------------------------------ report
    print("\n[3] Checks")
    all_ok = True
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")
        all_ok = all_ok and ok

    print("\n" + line)
    if all_ok:
        print("PASS: the swap graph has no edges and is disconnected for every")
        print("      instance checked; the first conjunct of conjecture 00000008234")
        print("      is FALSE, hence the conjecture is FALSE as stated.")
        print("      Smallest counterexample: n = 2 agents, m = 2 goods, unit")
        print("      (monotone) valuations; claimed diameter bound m(n-1) = 2 fails.")
        print(line)
        return 0
    print("FAIL: at least one claimed contradiction did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
