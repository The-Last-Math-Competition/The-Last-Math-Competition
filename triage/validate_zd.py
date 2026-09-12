#!/usr/bin/env python3
"""Validate the twin reduction in zerodivisor.py against brute force.

Builds Gamma(Z_n) explicitly and computes omega / chi directly, then compares
with the quotient-graph computation. If these disagree the reduction is wrong
and every downstream result is void.
"""
from itertools import combinations
from math import gcd

from zerodivisor import analyse, build_quotient


def brute_graph(n):
    verts = [x for x in range(1, n) if gcd(x, n) > 1]
    idx = {v: i for i, v in enumerate(verts)}
    m = len(verts)
    adj = [[False] * m for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            if (verts[i] * verts[j]) % n == 0:
                adj[i][j] = adj[j][i] = True
    return verts, adj


def brute_omega(adj):
    m = len(adj)
    best = [0]

    def expand(cand, size):
        if size > best[0]:
            best[0] = size
        if size + len(cand) <= best[0]:
            return
        for i, v in enumerate(cand):
            expand([u for u in cand[i + 1:] if adj[v][u]], size + 1)

    expand(list(range(m)), 0)
    return best[0]


def brute_chi(adj):
    m = len(adj)
    if m == 0:
        return 0
    order = sorted(range(m), key=lambda i: -sum(adj[i]))
    colours = [-1] * m

    def rec(pos, k, max_used):
        if pos == m:
            return True
        v = order[pos]
        blocked = {colours[u] for u in range(m) if adj[v][u] and colours[u] >= 0}
        for c in range(min(max_used + 2, k)):
            if c in blocked:
                continue
            colours[v] = c
            if rec(pos + 1, k, max(max_used, c)):
                return True
            colours[v] = -1
        return False

    k = brute_omega(adj)
    while not rec(0, k, -1):
        k += 1
    return k


print(f"{'n':>5} {'|V|':>5} {'omega_bf':>9} {'chi_bf':>7} {'omega_q':>8} {'chi_q':>6}  match")
bad = 0
for n in range(4, 121):
    verts, adj = brute_graph(n)
    if not verts:
        continue
    o_bf, c_bf = brute_omega(adj), brute_chi(adj)
    o_q, c_q, _ = analyse(n)
    ok = (o_bf == o_q and c_bf == c_q)
    if not ok:
        bad += 1
        print(f"{n:>5} {len(verts):>5} {o_bf:>9} {c_bf:>7} {o_q:>8} {str(c_q):>6}  MISMATCH")
print(f"\nvalidated n in [4,120]; mismatches: {bad}")
