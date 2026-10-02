#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002491."""
import sys
from itertools import combinations
from functools import lru_cache

def partitions(n):
    def rec(seq):
        if not seq:
            yield []
            return
        first, rest = seq[0], seq[1:]
        for p in rec(rest):
            yield [[first]] + p
            for i, block in enumerate(p):
                yield p[:i] + [[first] + block] + p[i+1:]
    return sorted(rec(list(range(n))), key=lambda p: sorted(map(len, p)))

def refine(p, q):
    # p <= q in partition lattice order (p refines q)
    for b in p:
        if not any(set(b) <= set(c) for c in q):
            return False
    return True

@lru_cache(maxsize=None)
def mu(i, j, lattice):
    lat = lattices[int(lattice)]
    if i == j:
        return 1
    if not refine(lat[i], lat[j]):
        return 0
    return -sum(mu(i, k, lattice) for k in range(len(lat))
                if k != j and refine(lat[i], lat[k]) and refine(lat[k], lat[j]))

lattices = [partitions(4)]

def main():
    lat = partitions(4)
    print(f"|Pi_4| = {len(lat)}")
    target = [[0, 1], [2, 3]]
    ti = lat.index(target)
    sizes = sorted(len(b) for b in target)
    print(f"sigma = {target}, block sizes = {sizes} (repeated)")
    v = mu(0, ti, 0)
    print(f"mu(0_hat, sigma) = {v}")
    assert v == 1 and len(sizes) == 2 and sizes[0] == sizes[1]
    # list all repeated-size partitions and their mu values
    for i, p in enumerate(lat):
        s = sorted(len(b) for b in p)
        if len(s) > 1 and len(set(s)) < len(s):
            m = mu(0, i, 0)
            print(f"  repeated sizes {s}: mu = {m}")
            assert m != 0, "vanishing claim would hold here"
    print("ALL CHECKS PASS — repeated-size partitions have NONZERO Mobius values")
    return 0

if __name__ == "__main__":
    sys.exit(main())
