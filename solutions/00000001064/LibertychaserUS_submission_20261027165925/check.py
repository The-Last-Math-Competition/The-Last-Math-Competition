#!/usr/bin/env python3
"""Conjecture 00000001064: for every odd prime p, the minimum size of a Kakeya set
S in (Z/p)^2 equals p(p+1)/2 + (p-1)/2.

Definitions (taken directly from the claim):
  * A Kakeya set is S subset of (Z/p)^2 such that for every nonzero (u,v) in (Z/p)^2
    there exist a,b in Z/p with L(a,b;u,v) = {(a+t*u, b+t*v) : t in Z/p} contained in S.
  * kak(p) = min |S| over all Kakeya sets S.
  * claimed(p) = p(p+1)//2 + (p-1)//2.

Methods:
  A. Definition-level brute force over all 2^(p^2) subsets (p=3 only; 2^9 = 512).
  B. Exhaustive over line choices (independent of B&B): S is Kakeya iff it contains a
     full line of every direction class, so kak(p) = min over one-line-per-direction
     choices of |union|. Enumerated completely for p = 3, 5, 7 (p^(p+1) choices).
  C. Exact branch and bound on the same reduction, for p = 3, 5, 7, 11 (and 13 if
     fast enough). Pruning uses valid lower bounds on the final union:
       - |U| + max_i m_i, where m_i = min over lines of direction i of |L \\ U|;
       - |U| + sum_i m_i - C(k,2) (Bonferroni: two distinct lines meet in <= 1 point).
     Translation symmetry: fix the line chosen for the first direction.
     The min is found by increasing k from p(p+1)/2 (the Bonferroni root bound) until a
     Kakeya set of size k exists. Each witness is re-verified against the definition.
"""
import itertools
import math
import sys
import time


def popcount(x):
    return x.bit_count()


def setup(p):
    pts = [(x, y) for x in range(p) for y in range(p)]
    bit = {pt: i for i, pt in enumerate(pts)}
    vecs = [(u, v) for u in range(p) for v in range(p) if (u, v) != (0, 0)]
    # line masks for each nonzero vector, directly from the definition
    lines_of = {}
    for (u, v) in vecs:
        ms = set()
        for a in range(p):
            for b in range(p):
                m = 0
                for t in range(p):
                    m |= 1 << bit[((a + t * u) % p, (b + t * v) % p)]
                ms.add(m)
        lines_of[(u, v)] = sorted(ms)
        assert len(ms) == p, "a direction must have exactly p lines"
    # direction classes: vectors that are nonzero scalar multiples
    def canon(u, v):
        return min(((lam * u) % p, (lam * v) % p) for lam in range(1, p))
    classes = {}
    for (u, v) in vecs:
        classes.setdefault(canon(u, v), []).append((u, v))
    # check: scalar multiples have identical line families (so classes are the right notion)
    for c, members in classes.items():
        base = lines_of[c]
        for w in members:
            assert lines_of[w] == base, "scalar multiples must give same line family"
    assert len(classes) == p + 1
    dirs = [lines_of[c] for c in sorted(classes)]
    return pts, bit, vecs, lines_of, dirs


def is_kakeya(S, p, vecs, lines_of):
    """Definition-level test on a set S given as an int bitmask."""
    for w in vecs:
        if not any((L & ~S) == 0 for L in lines_of[w]):
            return False
    return True


def method_A_bruteforce_p3(p=3):
    pts, bit, vecs, lines_of, dirs = setup(p)
    n = p * p
    best = None
    minimizers = []
    for S in range(1 << n):
        if is_kakeya(S, p, vecs, lines_of):
            k = popcount(S)
            if best is None or k < best:
                best, minimizers = k, [S]
            elif k == best:
                minimizers.append(S)
    return best, len(minimizers)


def method_B_exhaustive(p):
    pts, bit, vecs, lines_of, dirs = setup(p)
    best = None
    count = 0
    for choice in itertools.product(*dirs):
        U = 0
        for L in choice:
            U |= L
        k = popcount(U)
        if best is None or k < best:
            best, count = k, 1
        elif k == best:
            count += 1
    return best, count


def method_C_feasible(p, dirs, k, vecs, lines_of, node_budget=None):
    """Is there a Kakeya set of size <= k? Returns (witness_mask or None, nodes, complete)."""
    D = len(dirs)
    nodes = [0]
    aborted = [False]

    def lb(U, rem):
        ms = [min(popcount(L & ~U) for L in dirs[d]) for d in rem]
        r = len(ms)
        if r == 0:
            return 0
        bon = sum(ms) - r * (r - 1) // 2
        return max(max(ms), bon)

    def dfs(U, depth):
        nodes[0] += 1
        if node_budget is not None and nodes[0] > node_budget:
            aborted[0] = True
            return None
        cu = popcount(U)
        if cu > k:
            return None
        if depth == D:
            return U
        rem = list(range(depth, D))
        if cu + lb(U, rem) > k:
            return None
        if depth == 0:
            cands = [dirs[0][0]]  # translation symmetry
        else:
            cands = sorted(dirs[depth], key=lambda L: popcount(L & ~U))
        for L in cands:
            res = dfs(U | L, depth + 1)
            if res is not None:
                return res
            if aborted[0]:
                return None
        return None

    w = dfs(0, 0)
    return w, nodes[0], not aborted[0]


def method_C_min(p, node_budget=None):
    pts, bit, vecs, lines_of, dirs = setup(p)
    start = p * (p + 1) // 2
    log = []
    for k in range(start, p * p + 1):
        t0 = time.time()
        w, nodes, complete = method_C_feasible(p, dirs, k, vecs, lines_of, node_budget)
        log.append((k, w is not None, nodes, complete, round(time.time() - t0, 2)))
        if w is not None:
            size = popcount(w)
            ok = is_kakeya(w, p, vecs, lines_of) and size <= k
            return {"min": size, "witness_ok": ok, "witness_mask": w, "log": log,
                    "complete": all(l[3] for l in log)}
        if not complete:
            return {"min": None, "log": log, "complete": False}
    return {"min": None, "log": log, "complete": True}


def claimed(p):
    return p * (p + 1) // 2 + (p - 1) // 2


def main():
    report = {}
    print("== A. definition-level brute force, p=3 (all 2^9 subsets)")
    bestA, nminA = method_A_bruteforce_p3(3)
    print(f"   min |S| = {bestA}, number of minimizers = {nminA}, claimed = {claimed(3)}")
    report["A_p3"] = bestA

    print("== B. exhaustive line-choice enumeration (independent of B&B)")
    for p in (3, 5, 7):
        t0 = time.time()
        best, cnt = method_B_exhaustive(p)
        print(f"   p={p}: min = {best} (number of optimal line-choices = {cnt}); "
              f"claimed = {claimed(p)}; {round(time.time()-t0,1)} s")
        report[f"B_p{p}"] = best

    print("== C. branch and bound (exact, with lower-bound pruning)")
    ps = [int(a) for a in sys.argv[1:]] or [3, 5, 7, 11]
    for p in ps:
        t0 = time.time()
        res = method_C_min(p)
        if res["min"] is None:
            print(f"   p={p}: NOT resolved (budget/complete={res['complete']}); "
                  f"log={res['log']}")
        else:
            print(f"   p={p}: min = {res['min']}, witness verified against definition = "
                  f"{res['witness_ok']}, claimed = {claimed(p)}, "
                  f"match = {res['min'] == claimed(p)}; "
                  f"decision log (k, feasible, nodes, complete, s) = {res['log']}; "
                  f"{round(time.time()-t0,1)} s")
        report[f"C_p{p}"] = res["min"]
    print("== summary", report)


if __name__ == "__main__":
    main()
