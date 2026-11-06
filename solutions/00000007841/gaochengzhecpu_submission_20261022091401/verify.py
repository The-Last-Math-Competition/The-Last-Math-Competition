"""Independent exact enumeration of genuine random contractions on small graphs.

Original edges retain their identities, including parallel edges after a merge.
Only loops are removed. Each remaining original edge is sampled uniformly.
The success event is ANY minimum cut, not one prescribed cut. No Lean oracle.
"""
from fractions import Fraction
from functools import cache
from itertools import combinations
import json

def exact_success(n,edges):
    edges=tuple(edges)
    assert n>=3 and all(0<=u<v<n for u,v in edges) and len(set(edges))==len(edges)
    def cut_size(mask):
        return sum(bool(mask&(1<<u))!=bool(mask&(1<<v)) for u,v in edges)
    full=(1<<n)-1
    minimum=min(cut_size(mask) for mask in range(1,full) if mask&1)
    assert minimum>0,'connected input required'
    @cache
    def run(blocks):
        block_of={v:i for i,b in enumerate(blocks) for v in range(n) if b&(1<<v)}
        alive=[(block_of[u],block_of[v]) for u,v in edges if block_of[u]!=block_of[v]]
        if len(blocks)==2:
            return Fraction(len(alive)==minimum)
        total=Fraction(0)
        for i,j in alive:
            merged=blocks[i]|blocks[j]
            next_blocks=tuple(sorted([b for k,b in enumerate(blocks) if k not in {i,j}]+[merged]))
            total+=run(next_blocks)
        return total/len(alive)
    prob=run(tuple(1<<v for v in range(n)))
    return {'n':n,'edges':len(edges),'min_cut':minimum,'success':str(prob),'states':run.cache_info().currsize}

rows=[]
for n in range(3,10):
    cycle=sorted({tuple(sorted((i,(i+1)%n))) for i in range(n)})
    row=exact_success(n,cycle); assert row['success']=='1'; rows.append({'family':'cycle',**row})
for n in range(3,8):
    row=exact_success(n,combinations(range(n),2))
    assert Fraction(row['success'])>=Fraction(2,n*(n-1))
    rows.append({'family':'complete',**row})
print(json.dumps(rows,indent=2))
