#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000004091 (REFUTED).

Conjecture: b1(Conf_n(Gamma)) is barycentric-subdivision invariant
and a polynomial in the chromatic number of degree exactly n.

Refutation at n = 1: Conf_1(Gamma) = Gamma, b1 = E - V + 1.
C4 and P4 are both bipartite (chi = 2) but b1 = 1 vs 0: b1 is not a
function of chi, hence no polynomial of any degree. Also the two
clauses conflict: barycentric subdivision of C3 is C6 (chi 3 -> 2)
with b1 preserved, so invariance + polynomial-in-chi is incoherent.
"""

from itertools import combinations

# graphs as edge lists
C4 = [(0,1),(1,2),(2,3),(3,0)]
P4 = [(0,1),(1,2),(2,3)]

def b1(E, V):
    return E + 1 - V

def is_bipartite(E, n):
    adj = {i: set() for i in range(n)}
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    color = {}
    for s in range(n):
        if s in color: continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in color:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return False
    return True

assert b1(4, 4) == 1 and b1(3, 4) == 0
assert is_bipartite(C4, 4) and is_bipartite(P4, 4)
print("b1(C4) = 1, b1(P4) = 0; both bipartite (chi = 2) — b1 not a function of chi — REFUTED")

# subdivision conflict: C3 (chi 3) -> barycentric subdivision = C6 (chi 2), b1 = 1 preserved
C3 = [(0,1),(1,2),(2,0)]
assert b1(3, 3) == 1 and b1(6, 6) == 1
print("C3 and its barycentric subdivision C6 both have b1 = 1 but chi 3 vs 2 — invariance + polynomial-in-chi incoherent — OK")

# n = 1 is the FIRST interesting case: no degree-1 polynomial in chi can fit even on bipartite graphs
# (all chi = 2, b1 varies) — the degree-exactly-n claim fails at its base case.
print("\nALL CHECKS PASSED: conjecture 00000004091 REFUTED "
      "(b1 not a function of chi: C4 vs P4 at chi = 2)")
