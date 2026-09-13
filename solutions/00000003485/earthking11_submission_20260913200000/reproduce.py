#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000003485.

    Definition: A kernel of a digraph is an independent out-stable set.
    Conjecture: Digraphs with bounded out-degree and girth at least five have
    kernels; the critical configuration of the condition is the directed odd
    cycle with a one-point source, and the bound is a tightening of
    Richardson's theorem.

A kernel of a digraph D = (V, A) is a set S subset of V such that

    (i)  S is independent: no arc joins two members of S in either direction,
         i.e. for all u, v in S, neither (u, v) nor (v, u) lies in A;
    (ii) S is out-stable (absorbing): every vertex outside S has an arc INTO S,
         i.e. for every v not in S there is s in S with (v, s) in A.

This script disproves the conjecture with the smallest possible witness, the
directed 5-cycle C_5 (vertices 0..4, arcs i -> i+1 mod 5):

  * its out-degree is 1 everywhere, so it certainly has bounded out-degree;
  * its directed girth is 5, and so is its underlying undirected girth;
  * it has NO kernel: a brute force over all 2^5 = 32 subsets finds none.

The same brute force is run on the directed odd cycles C_3, C_5, C_7, C_9, and
on the strongly connected blow-ups of C_5 in which each vertex is replaced by
an independent part of equal size m (out-degree m, girth still 5); all are
kernel-free. Standard library only. Python 3.8+.
"""

from collections import deque
from itertools import product

# ---------------------------------------------------------------------------
# generic digraph helpers
# ---------------------------------------------------------------------------


def cycle_digraph(n):
    """Directed n-cycle: vertices 0..n-1, arc i -> (i + 1) mod n."""
    verts = list(range(n))
    arcs = {(i, (i + 1) % n) for i in range(n)}
    return verts, arcs


def blowup_cycle(n, m):
    """Strongly connected blow-up of the directed n-cycle.

    Each vertex i of the cycle is replaced by an independent part
    {(i, k) : 0 <= k < m} of size m, and every vertex of part i has an arc to
    every vertex of part i + 1 (mod n). The result has out-degree m, directed
    girth n, and is strongly connected.
    """
    verts = [(i, k) for i in range(n) for k in range(m)]
    arcs = {
        ((i, k), ((i + 1) % n, l))
        for i in range(n)
        for k in range(m)
        for l in range(m)
    }
    return verts, arcs


def out_degree(verts, arcs, v):
    return sum(1 for w in verts if (v, w) in arcs)


def is_independent(S, arcs):
    """No arc in either direction between two members of S."""
    for u in S:
        for v in S:
            if (u, v) in arcs or (v, u) in arcs:
                return False
    return True


def is_out_stable(S, verts, arcs):
    """Every vertex outside S has an arc into S."""
    for v in verts:
        if v in S:
            continue
        if not any((v, s) in arcs for s in S):
            return False
    return True


def count_kernels(verts, arcs):
    """Exhaustive brute force over all 2^|V| subsets."""
    kernels = 0
    for bits in product((0, 1), repeat=len(verts)):
        S = {v for v, b in zip(verts, bits) if b}
        if is_independent(S, arcs) and is_out_stable(S, verts, arcs):
            kernels += 1
    return kernels


def directed_girth(verts, arcs):
    """Length of the shortest directed cycle, or None if acyclic.

    Computed as the least k >= 1 for which some vertex is reachable from itself
    by a directed walk of length exactly k.
    """
    reach = {v: {v} for v in verts}
    for k in range(1, len(verts) + 2):
        nxt = {v: set() for v in verts}
        for v in verts:
            for u in reach[v]:
                for (a, b) in arcs:
                    if a == u:
                        nxt[v].add(b)
        reach = nxt
        if any(v in reach[v] for v in verts):
            return k
    return None


def undirected_girth(verts, arcs):
    """Length of the shortest cycle in the underlying undirected graph."""
    adj = {v: set() for v in verts}
    for (a, b) in arcs:
        adj[a].add(b)
        adj[b].add(a)
    best = None
    for src in verts:
        dist = {src: 0}
        parent = {src: None}
        queue = deque([src])
        while queue:
            u = queue.popleft()
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1
                    parent[w] = u
                    queue.append(w)
                elif parent[u] != w:
                    cycle = dist[u] + dist[w] + 1
                    if best is None or cycle < best:
                        best = cycle
    return best


# ---------------------------------------------------------------------------
# the checks
# ---------------------------------------------------------------------------


def main():
    checks = []
    line = "=" * 72

    def check(name, ok, detail):
        checks.append((name, ok, detail))

    # --- C_5: out-degree and girth (the conjecture's hypotheses) -----------
    v5, a5 = cycle_digraph(5)
    degs5 = [out_degree(v5, a5, v) for v in v5]
    dg5 = directed_girth(v5, a5)
    ug5 = undirected_girth(v5, a5)
    check(
        "C_5 has out-degree 1 at every vertex (bounded out-degree)",
        all(d == 1 for d in degs5),
        f"out-degrees = {degs5}",
    )
    check(
        "C_5 has directed girth 5 (>= 5)",
        dg5 == 5,
        f"shortest directed cycle has length {dg5}",
    )
    check(
        "C_5 has underlying undirected girth 5 (>= 5)",
        ug5 == 5,
        f"shortest undirected cycle has length {ug5}",
    )

    # --- C_5: zero kernels among the 32 subsets ---------------------------
    k5 = count_kernels(v5, a5)
    check(
        "C_5 has no kernel (0 kernels among 2^5 = 32 subsets)",
        k5 == 0,
        f"brute force over the 32 subsets found {k5} kernels",
    )

    # --- the odd-cycle family ---------------------------------------------
    print(line)
    print("Disproof of conjecture 00000003485 -- reproduction")
    print(line)
    print("\n[1] Directed odd cycles C_n: brute force over all 2^n subsets")
    family = {3: 0, 5: 0, 7: 0, 9: 0}
    for n in (3, 5, 7, 9):
        verts, arcs = cycle_digraph(n)
        k = count_kernels(verts, arcs)
        family[n] = k
        degs = sorted({out_degree(verts, arcs, v) for v in verts})
        print(
            f"    n = {n}: subsets = 2^{n} = {2 ** n}, "
            f"kernels = {k}, out-degrees = {degs}"
        )
        check(
            f"C_{n} has no kernel (0 kernels among {2 ** n} subsets)",
            k == 0,
            f"brute force found {k} kernels",
        )
    check(
        "odd-cycle family: C_3, C_5, C_7, C_9 are all kernel-free",
        all(v == 0 for v in family.values()),
        f"kernel counts = {family}",
    )

    # --- blow-ups of C_5: kernel-free with out-degree m, girth 5 -----------
    print("\n[2] Blow-ups of C_5 (each vertex replaced by an independent part")
    print("    of size m; arcs between consecutive parts). Out-degree = m,")
    print("    girth 5, still no kernel:")
    for m in (1, 2, 3):
        verts, arcs = blowup_cycle(5, m)
        k = count_kernels(verts, arcs)
        degs = sorted({out_degree(verts, arcs, v) for v in verts})
        dg = directed_girth(verts, arcs)
        print(
            f"    m = {m}: vertices = {len(verts)}, out-degrees = {degs}, "
            f"directed girth = {dg}, kernels = {k} (of {2 ** len(verts)} subsets)"
        )
        check(
            f"blow-up of C_5 with part size {m} has no kernel",
            k == 0,
            f"out-degree {m}, girth {dg}, {k} kernels",
        )
        check(
            f"blow-up of C_5 with part size {m} has girth 5 and out-degree {m}",
            dg == 5 and degs == [m],
            f"out-degrees = {degs}, directed girth = {dg}",
        )

    # --- what this means for the conjecture --------------------------------
    print("\n[3] Checks")
    all_ok = True
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")
        all_ok = all_ok and ok

    # --- hard assertions: exit non-zero on failure ------------------------
    assert k5 == 0, "C_5 must have no kernel"
    assert family == {3: 0, 5: 0, 7: 0, 9: 0}, "every odd cycle must be kernel-free"
    assert dg5 == 5 and ug5 == 5 and all(d == 1 for d in degs5), (
        "C_5 must have out-degree 1 and girth 5"
    )

    print("\n" + line)
    if all_ok:
        print("PASS: the directed 5-cycle has bounded out-degree and girth 5,")
        print("      yet no kernel; every directed odd cycle and every blow-up of C_5")
        print("      is likewise kernel-free.")
        print("Conjecture 00000003485 is FALSE as stated.")
        print(line)
        return 0
    print("FAIL: at least one claimed fact did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
