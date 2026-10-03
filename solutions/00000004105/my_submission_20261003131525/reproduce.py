#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000004105 (REFUTED).

Conjecture: motion-group growth is polynomial iff the graph is a
tree; among non-trees the smallest growth is the star-graph motion
group's, strictly super-polynomial yet sub-exponential.

Refutation: the star K_{1,3} IS a tree (V = 4, E = 3 = V - 1,
connected, acyclic), so clause 1 gives polynomial growth for the
star's motion group while clause 3 demands strictly super-polynomial
growth for the same group: direct self-contradiction.
"""

from collections import deque

# ---------- gate 1: the star graph is a tree ----------
star = {0: [1, 2, 3], 1: [0], 2: [0], 3: [0]}
V, E = 4, 3
assert E == V - 1
# connected
seen, q = {0}, deque([0])
while q:
    u = q.popleft()
    for v in star[u]:
        if v not in seen:
            seen.add(v); q.append(v)
assert len(seen) == V
# acyclic: E = V - 1 + connected implies acyclic
print(f"star K_1,3: V = {V}, E = {E} = V - 1, connected, acyclic — a TREE — OK")

# ---------- gate 2: the two clauses conflict on the same object ----------
# clause 1: tree => polynomial growth  (applies to the star)
# clause 3: star => strictly super-polynomial growth (applies to the star)
# A growth function g with g <= p (some polynomial p) cannot satisfy
# g > q for every polynomial q, since q = p is a polynomial.
def super_polynomial(growth_fn):
    # strictly exceeds every polynomial (check a few degrees at large n)
    return all(growth_fn(10**6) > d * (10**6)**d for d in (1, 2, 3))

def polynomial_bounded(growth_fn):
    # bounded by some polynomial (e.g. degree 5)
    return growth_fn(10**6) <= 10 * (10**6)**5

# whatever the star's motion-group growth g is, it cannot satisfy both:
identity = lambda n: n
assert polynomial_bounded(identity) and not super_polynomial(identity)
crazy = lambda n: 2 ** n
assert super_polynomial(crazy) and not polynomial_bounded(crazy)
print("no growth function is both polynomially bounded and strictly super-polynomial — clauses 1 and 3 are exclusive")

# the star is in BOTH clauses' scopes: contradiction stands regardless of its true growth
print("star = tree => clause 1 scope; star = star => clause 3 scope: the conjecture refutes itself — REFUTED")

print("\nALL CHECKS PASSED: conjecture 00000004105 REFUTED "
      "(internally contradictory at K_{1,3})")
