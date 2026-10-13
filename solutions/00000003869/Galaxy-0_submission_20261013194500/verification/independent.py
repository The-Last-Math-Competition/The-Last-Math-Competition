#!/usr/bin/env python3
"""Independent finite regressions; never used as a Lean proof oracle."""
from itertools import combinations
import random

def matchings(points):
    if not points:
        yield ()
        return
    a = min(points)
    for b in sorted(points - {a}):
        for rest in matchings(points - {a, b}):
            yield ((a,b),) + rest

def inv(m):
    p = sum((list(e) for e in m), [])
    return sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1,len(p)))
def cross(m):
    return sum(a<c<b<d for (a,b),(c,d) in combinations(m,2))
def nest(m):
    return sum(a<c<d<b for (a,b),(c,d) in combinations(m,2))
def product(xs):
    r=1
    for x in xs:r*=x
    return r

def recursive_pf(A, points):
    if not points:return 1
    a,*tail=points
    return sum((-1)**j * A[a][b] * recursive_pf(A,tail[:j]+tail[j+1:])
               for j,b in enumerate(tail))

def verify():
    expected=1
    total=0
    for n in range(7):
        if n:expected*=2*n-1
        M=list(matchings(set(range(2*n))))
        assert len(M)==expected and len(set(M))==expected
        for m in M:
            assert sorted(sum((list(e) for e in m),[]))==list(range(2*n))
            assert inv(m)==cross(m)+2*nest(m)
            assert (-1)**inv(m)==(-1)**cross(m)
        print(f'n={n}: all {len(M)} perfect matchings passed')
        total+=len(M)
    rng=random.Random(3869)
    count=0
    for n in range(6):
        for trial in range(10):
            A=[[0]*(2*n) for _ in range(2*n)]
            for i,j in combinations(range(2*n),2):
                A[i][j]=rng.randint(-9,9);A[j][i]=-A[i][j]
            value=sum((-1)**cross(m)*product(A[a][b] for a,b in m)
                      for m in matchings(set(range(2*n))))
            assert value==recursive_pf(A,list(range(2*n)))
            count+=1
    print(f'PASS: {total} matching identities; {count} recursive Pfaffian matrix checks')

if __name__=='__main__':verify()
