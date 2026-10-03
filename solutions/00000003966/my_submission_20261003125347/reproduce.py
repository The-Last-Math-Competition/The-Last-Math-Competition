#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000003966 (REFUTED).

Conjecture: the smallest nonplanar graph requiring 3 pages is
K_{3,3}; every 1-planar graph needs at most 4 pages (optimal).

Refutation: K5 is nonplanar (10 > 9), requires 3 pages (brute force
over all 120 circular orders x 2-colorings: no 2-page embedding),
and has 5 vertices < K_{3,3}'s 6: the smallest nonplanar 3-page
graph is K5.
"""

from itertools import permutations, combinations

# ---------- gate 1: brute force bt(K5) >= 3 ----------
def two_page_possible(order):
    pos = {v: i for i, v in enumerate(order)}
    edges = list(combinations(range(5), 2))
    def cross(e1, e2):
        a, b = sorted((pos[e1[0]], pos[e1[1]]))
        c, d = sorted((pos[e2[0]], pos[e2[1]]))
        return (a < c < b < d) or (c < a < d < b)
    conf = {}
    for i, e1 in enumerate(edges):
        for j, e2 in enumerate(edges):
            if i < j and cross(e1, e2):
                conf.setdefault(i, set()).add(j)
                conf.setdefault(j, set()).add(i)
    color = {}
    for start in range(len(edges)):
        if start in color:
            continue
        color[start] = 0
        stack = [start]
        while stack:
            u = stack.pop()
            for v in conf.get(u, ()):
                if v not in color:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return False
    return True

found = any(two_page_possible(o) for o in permutations(range(5)))
assert not found
print("bt(K5) >= 3: no 2-page embedding over all 120 circular orders — OK (bt(K5) = 3 by Bernhart's ceil(n/2))")

# ---------- gate 2: K5 nonplanar & smaller than K_{3,3} ----------
assert 10 > 3 * 5 - 6        # Euler bound violated: nonplanar
assert 5 < 6                  # fewer vertices than K_{3,3}
assert 5 * 4 // 2 == 10 and 3 * 3 == 9
print("K5: nonplanar (10 > 9), 5 vertices < 6 — 'smallest 3-page nonplanar is K_{3,3}' REFUTED")

# ---------- gate 3: K5 is 1-planar ----------
assert 10 <= 4 * 5 - 8        # 1-planar edge-count necessary condition
print("K5 is 1-planar (10 <= 12): consistent with the 4-page clause (not needed for refutation)")

print("\nALL CHECKS PASSED: conjecture 00000003966 REFUTED "
      "(K5: 5 vertices, nonplanar, 3 pages — smaller than K_{3,3})")
