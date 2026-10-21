#!/usr/bin/env python3
"""Independent finite diagnostics, not a substitute for the universal Lean proof."""
from itertools import combinations, product
import json

def monomials(d):
    return [(i,j,k) for i in range(d+1) for j in range(d+1-i)
            for k in range(d+1-i-j)] if d >= 0 else []

def rank(vectors):
    pivots = {}
    for v in vectors:
        while v:
            p = v.bit_length() - 1
            if p in pivots:
                v ^= pivots[p]
            else:
                pivots[p] = v
                break
    return len(pivots)

def matrix_columns(d):
    source = monomials(d)
    target = {m:i for i,m in enumerate(monomials(d+2))}
    generators = [(1,1,0),(1,0,1),(0,1,1)]
    alpha = [1 << target[tuple(a+b for a,b in zip(m,g))]
             for g in generators for m in source]
    index = {(c,m):c*len(source)+i for c in range(3)
             for i,m in enumerate(source)}
    syzygy = []
    for components in [[(0,(0,0,1)),(1,(0,1,0))],
                       [(0,(0,0,1)),(2,(1,0,0))]]:
        for m in monomials(d-1):
            col = 0
            for c,g in components:
                col ^= 1 << index[c, tuple(a+b for a,b in zip(m,g))]
            syzygy.append(col)
    for col in syzygy:
        image = 0
        for i,v in enumerate(alpha):
            if (col >> i) & 1:
                image ^= v
        assert image == 0
    assert rank(syzygy) == len(syzygy)
    assert len(alpha)-rank(alpha) == len(syzygy)
    return {"coefficient_degree_bound":d, "source_dimension":len(alpha),
            "augmentation_rank":rank(alpha),
            "kernel_dimension":len(alpha)-rank(alpha),
            "syzygy_domain_dimension":len(syzygy)}

def matching_number(edges):
    maximum = 0
    for r in range(len(edges)+1):
        for es in combinations(edges,r):
            flat = [v for e in es for v in e]
            if len(set(flat)) == len(flat):
                maximum = max(maximum,r)
    return maximum

def bipartite(n,edges):
    return any(all(c[a]!=c[b] for a,b in edges)
               for c in product([0,1],repeat=n))

def main():
    k2=[(0,1)]
    k3=[(0,1),(0,2),(1,2)]
    assert matching_number(k2)==matching_number(k3)==1
    assert bipartite(2,k2) and not bipartite(3,k3)
    assert [(0,1),(1,2),(0,2)] == [k3[0],k3[2],k3[1]]
    checks=[matrix_columns(d) for d in range(9)]
    quotient_betti=[(0,0,1),(1,2,3),(2,3,2)]
    ideal_betti=[(0,2,1)]
    assert max(j-i for i,j,_ in quotient_betti)==1
    assert max(j-i for i,j,_ in ideal_betti)==2
    print(json.dumps({"status":"PASS", "scope":"Independent finite diagnostics only",
          "K2":{"matching_number":1,"bipartite":True,"edges":k2,
                "ideal_regularity_from_proposed_resolution":2},
          "K3":{"matching_number":1,"bipartite":False,"triangle":[0,1,2,0],
                "edges":k3,"quotient_regularity_from_proposed_resolution":1},
          "F2_polynomial_resolution_checks":checks},indent=2))

if __name__=="__main__":
    main()
