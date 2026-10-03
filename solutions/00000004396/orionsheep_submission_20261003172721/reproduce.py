#!/usr/bin/env python3
"""
Numerical refutation of TLMC conjecture 00000004396.

Conjecture (verbatim): "All Mobius ladders are Sidorenko, and every odd
subdivision of a tree is Sidorenko, and the union of the two families gives
infinitely many new nontrivial members."

Definition (Sidorenko graph): a graph G for which the reflection/Sidorenko
bound always holds, i.e. for every finite host graph H,

    hom(G, H) * |V(H)|^{|E(G)|} >= hom(K2, H)^{|E(G)|} * |V(H)|^{|V(G)|}

equivalently, in homomorphism-density form t(G,W) >= t(K2,W)^{|E(G)|}
for every graphon W.  A classical, easily checked necessary condition:
every Sidorenko graph is BIPARTITE (take H = K2: if G is non-bipartite then
hom(G,K2)=0 while the right-hand side is strictly positive).

We show the first conjunct is already false by exhibiting a Mobius ladder
that is non-bipartite: the Mobius ladder M_n on 2n vertices is bipartite
iff n is odd, so M_2 (= K4) and M_4 are non-bipartite, hence not Sidorenko.
"""
from itertools import product


def mobius_edges(n):
    """Mobius ladder M_n: vertices Z_{2n}; rim edges (i, i+1) and
    spokes (i, i+n)."""
    m = 2 * n
    E = set()
    for i in range(m):
        E.add((min(i, (i + 1) % m), max(i, (i + 1) % m)))
        E.add((min(i, (i + n) % m), max(i, (i + n) % m)))
    return E


def is_bipartite(nv, E):
    color = {}
    for s in range(nv):
        if s in color:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for a, b in E:
                v = -1
                if a == u:
                    v = b
                elif b == u:
                    v = a
                if v < 0:
                    continue
                if v in color:
                    if color[v] == color[u]:
                        return False
                else:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return True


def hom_count(E_G, nG, E_H, nH):
    """Number of graph homomorphisms G -> H (brute force)."""
    adjH = [[False] * nH for _ in range(nH)]
    for a, b in E_H:
        adjH[a][b] = adjH[b][a] = True
    cnt = 0
    for f in product(range(nH), repeat=nG):
        ok = True
        for a, b in E_G:
            if not adjH[f[a]][f[b]]:
                ok = False
                break
        cnt += ok
    return cnt


def sidorenko_holds_for_host(E_G, nG, E_H, nH):
    """Check hom(G,H) * nH^{eG} >= hom(K2,H)^{eG} * nH^{nG}."""
    eG = len(E_G)
    lhs = hom_count(E_G, nG, E_H, nH) * nH ** eG
    rhs = hom_count([(0, 1)], 2, E_H, nH) ** eG * nH ** nG
    return lhs >= rhs, lhs, rhs


K2 = ({(0, 1)}, 2)

print("== Bipartiteness of Mobius ladders M_n ==")
nonbip = []
for n in range(2, 9):
    E = mobius_edges(n)
    b = is_bipartite(2 * n, E)
    print(f"  M_{n}: |V|={2*n}, |E|={len(E)}, bipartite={b}")
    if not b:
        nonbip.append(n)

print("\n== Direct Sidorenko check vs host H = K2 ==")
for n in nonbip:
    E = mobius_edges(n)
    ok, lhs, rhs = sidorenko_holds_for_host(E, 2 * n, *K2)
    print(f"  M_{n}: hom(M_{n},K2)*2^{len(E)} = {lhs} "
          f"vs  hom(K2,K2)^{len(E)}*2^{2*n} = {rhs}  ->  inequality holds: {ok}")
    assert not ok, f"M_{n} unexpectedly satisfied the bound"
    print(f"    => M_{n} is NOT Sidorenko (fails already against H = K2).")

print("\n== Sanity: odd-n Mobius ladders are bipartite (consistent with known"
      " result that M_3=K_{3,3}, M_5, ... are Sidorenko) ==")
for n in [3, 5, 7]:
    E = mobius_edges(n)
    assert is_bipartite(2 * n, E)

print("\nVERDICT: REFUTED — Mobius ladders M_n with n even are non-bipartite,")
print("hence not Sidorenko; 'all Mobius ladders are Sidorenko' is FALSE.")
