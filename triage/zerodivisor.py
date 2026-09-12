#!/usr/bin/env python3
"""
Target C: 00000002222
  "No counterexample exists to chromatic number = clique number for the
   zero-divisor graph Gamma(R) with R = Z_n for n <= 1000."

Gamma(Z_n): vertices are the nonzero zero-divisors of Z_n; x ~ y iff n | xy.
The conjecture asserts chi = omega for every n <= 1000.

Exact computation is made feasible by a twin reduction.

Let n = prod p_i^{a_i}. For x in Z_n, x != 0, let v(x) = (v_{p_1}(x), ...).
Then
    x ~ y   <=>   v_i(x) + v_i(y) >= a_i   for every i
so adjacency depends only on v(x). Hence:

  * vertices sharing a valuation vector are TWINS (identical neighbourhoods);
  * such a class is a clique iff 2*v_i >= a_i for all i, else an independent set;
  * |class(v)| = prod_i c_i(v_i), with c_i(a_i) = 1 and
    c_i(v) = phi(p_i^{a_i - v}) for v < a_i.

So Gamma(Z_n) is a blow-up of a small quotient graph G. The quotient keeps the
valuation vectors other than v = 0 (the units, which are not vertices) and
v = a (which forces x = 0 mod n), so it has exactly

    prod(a_i + 1) - 2

vertices -- at most 30 for n <= 1000, attained at n = 840 = 2^3*3*5*7. With
per-class weights

    w(v) = |class(v)|   if the class is a clique
         = 1            otherwise

and
    omega(Gamma) = max over cliques C of G of sum_{v in C} w(v)
    chi(Gamma)   = weighted chromatic number of G with weights w.

Both are computed exactly below.
"""
import sys
from functools import lru_cache
from itertools import combinations
from math import gcd

sys.setrecursionlimit(10000)


def factorize(n):
    f = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            a = 0
            while n % d == 0:
                n //= d
                a += 1
            f.append((d, a))
        d += 1
    if n > 1:
        f.append((n, 1))
    return f


def euler_phi(m):
    result = m
    p = 2
    mm = m
    while p * p <= mm:
        if mm % p == 0:
            while mm % p == 0:
                mm //= p
            result -= result // p
        p += 1
    if mm > 1:
        result -= result // mm
    return result


def build_quotient(n):
    """Return (vectors, weights, adj) for the quotient graph of Gamma(Z_n)."""
    fac = factorize(n)
    k = len(fac)
    if k == 0:
        return [], [], []
    ranges = [range(a + 1) for _, a in fac]
    vecs = []
    for combo in __import__("itertools").product(*ranges):
        if all(c == 0 for c in combo):
            continue                                  # units
        if all(c == a for c, (_, a) in zip(combo, fac)):
            continue                                  # zero
        vecs.append(combo)

    weights = []
    for v in vecs:
        size = 1
        for vi, (p, a) in zip(v, fac):
            size *= 1 if vi == a else euler_phi(p ** (a - vi))
        is_clique = all(2 * vi >= a for vi, (_, a) in zip(v, fac))
        weights.append(size if is_clique else 1)

    m = len(vecs)
    adj = [[False] * m for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            if all(u + w >= a for u, w, (_, a) in zip(vecs[i], vecs[j], fac)):
                adj[i][j] = adj[j][i] = True
    return vecs, weights, adj


def max_weight_clique(weights, adj):
    """Exact maximum weight clique by branch and bound."""
    m = len(weights)
    order = sorted(range(m), key=lambda i: -weights[i])
    best = [0]

    def expand(cand, total):
        if total > best[0]:
            best[0] = total
        # optimistic bound
        if total + sum(weights[i] for i in cand) <= best[0]:
            return
        for idx, v in enumerate(cand):
            expand([u for u in cand[idx + 1:] if adj[v][u]], total + weights[v])

    expand(order, 0)
    return best[0]


def weighted_chromatic(weights, adj, k):
    """Is there a colouring with k colours? Exact backtracking.

    Each vertex v needs weights[v] distinct colours, all disjoint from the
    colours of its neighbours. Returns a colouring or None."""
    m = len(weights)
    order = sorted(range(m), key=lambda i: -weights[i])
    colours = [None] * m
    used_by = [set() for _ in range(m)]      # colours blocked on each vertex

    def rec(pos, max_used):
        if pos == len(order):
            return True
        v = order[pos]
        w = weights[v]
        blocked = set()
        for u in range(m):
            if adj[v][u] and colours[u] is not None:
                blocked |= colours[u]
        # a vertex may need several colours at once, so allow up to w brand-new
        # ones beyond the highest colour used so far (this was the bug that made
        # chi come out too large for single-vertex quotients such as n = 9)
        avail = [c for c in range(min(k, max_used + 1 + w)) if c not in blocked]
        if len(avail) < w:
            return False
        for chosen in combinations(avail, w):
            colours[v] = set(chosen)
            new_max = max(max_used, max(chosen))
            if new_max < k and rec(pos + 1, new_max):
                return True
            colours[v] = None
        return False

    return rec(0, -1)


def analyse(n):
    vecs, weights, adj = build_quotient(n)
    if not vecs:
        return 0, 0, 0
    omega = max_weight_clique(weights, adj)
    chi = omega
    while chi <= len(vecs) + max(weights) and not weighted_chromatic(weights, adj, chi):
        chi += 1
        if chi > omega + 5:
            return omega, None, len(vecs)
    return omega, chi, len(vecs)


if __name__ == "__main__":
    bad = []
    maxq = 0
    worst = None
    checked = 0
    skipped = 0
    lo = None
    hi = None
    for n in range(4, 1001):
        omega, chi, q = analyse(n)
        if not q:
            # no zero divisors at all: n is prime (or 1), so Gamma(Z_n) is
            # empty and the conjecture is vacuous here. Do not count it.
            skipped += 1
            continue
        maxq = max(maxq, q)
        if chi is None:
            bad.append((n, omega, "unknown"))
            continue
        checked += 1
        if chi != omega:
            bad.append((n, omega, chi))
        if worst is None or q > worst[2]:
            worst = (n, omega, q)
        if lo is None or omega < lo[1]:
            lo = (n, omega)
        if hi is None or omega > hi[1]:
            hi = (n, omega)
    print(f"composite n in [4, 1000] analysed: {checked} "
          f"(skipped {skipped} primes, which have no zero divisors)")
    print(f"omega range: {lo[1]} (n = {lo[0]}) .. {hi[1]} (n = {hi[0]})")
    print(f"largest quotient graph: {maxq} vertices "
          f"(n = {worst[0]}, omega = {worst[1]})")
    print(f"counterexamples (chi != omega): {len(bad)}")
    for n, omega, chi in bad[:30]:
        print(f"   n={n}: omega={omega}, chi={chi}")
