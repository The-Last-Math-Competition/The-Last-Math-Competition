#!/usr/bin/env python3
"""Independent exact-rational audit. No floating point or third-party dependencies."""
from fractions import Fraction as Q
from itertools import combinations
P=((0,0,0),(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1))
W=tuple(Q(i,100) for i in range(5))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(t,a): return tuple(t*x for x in a)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def cross(a,b): return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def power(i,x): return dot(sub(x,P[i]),sub(x,P[i]))-W[i]
for i,j in combinations(range(5),2):
    x=scale((3-W[j])/6,P[j]) if i==0 else add(add(P[i],P[j]),scale((W[j]-W[i])/16,sub(P[i],P[j])))
    n=sub(P[i],P[j]); a,b,c=n
    u,v=((-b,a,0),(-c,0,a)) if a else (((b,-a,0),(0,-c,b)) if b else ((1,0,0),(0,1,0)))
    y=add(x,scale(Q(1,1000),u)); z=add(x,scale(Q(1,1000),v))
    assert cross(sub(y,x),sub(z,x)) != (0,0,0)
    for t in (x,y,z):
        assert power(i,t)==power(j,t)
        assert all(power(i,t)<power(k,t) for k in range(5) if k not in (i,j))
    gap=min(power(k,x)-power(i,x) for k in range(5) if k not in(i,j))
    print(f'facet {i}{j}: base={x}, strict gap={gap}; three points verified')
for i,j,k,l in combinations(range(5),4):
    d=dot(sub(P[j],P[i]),cross(sub(P[k],P[i]),sub(P[l],P[i])))
    assert d!=0
    print(f'affine determinant {i}{j}{k}{l}: {d}')
assert sum(dot(P[i],P[i])-W[i] for i in range(1,5)) == Q(119,10)
assert add(add(P[1],P[2]),add(P[3],P[4])) == (0,0,0)
assert all(power(i,P[i])<power(k,P[i]) for i in range(5) for k in range(5) if i!=k)
print('All exact geometric audits passed.')
