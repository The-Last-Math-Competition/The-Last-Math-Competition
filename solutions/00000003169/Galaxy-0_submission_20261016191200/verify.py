#!/usr/bin/env python3
"""Independent exact check. Python standard library only; no numerical roots."""
from fractions import Fraction as Q
from collections import defaultdict
f={(0,0):1,(1,0):1,(0,1):1}
g={(0,0):4,(1,0):1,(0,1):2,(3,0):1,(2,1):3,(1,2):3,(0,3):1}
def add(a,b):
 c=defaultdict(int,a)
 for p,v in b.items(): c[p]+=v
 return {p:v for p,v in c.items() if v}
def neg(a): return {p:-v for p,v in a.items()}
def mul(a,b):
 c=defaultdict(int)
 for (i,j),v in a.items():
  for (k,l),w in b.items(): c[i+k,j+l]+=v*w
 return {p:v for p,v in c.items() if v}
h={(2,0):1,(1,1):2,(0,2):1,(1,0):-1,(0,1):-1,(0,0):2}
x1={(1,0):1,(0,0):-1}; y2={(0,1):1,(0,0):2}
assert add(g,neg(mul(h,f)))==y2
assert add(mul(add(h,{(0,0):1}),f),neg(g))==x1
assert add(x1,y2)==f
assert add(mul(h,x1),mul(add(h,{(0,0):1}),y2))==g
assert sum(v*1**i*(-2)**j for (i,j),v in f.items())==0
assert sum(v*1**i*(-2)**j for (i,j),v in g.items())==0
def derivative(p,axis):
 return {(i-(axis==0),j-(axis==1)):v*(i if axis==0 else j) for (i,j),v in p.items() if (i if axis==0 else j)>0}
assert add(mul(derivative(f,0),derivative(g,1)),neg(mul(derivative(f,1),derivative(g,0))))=={(0,0):1}
def hull(points):
 ps=sorted(set(points))
 def cross(o,a,b):return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
 low=[]
 for p in ps:
  while len(low)>1 and cross(low[-2],low[-1],p)<=0:low.pop()
  low.append(p)
 up=[]
 for p in ps[::-1]:
  while len(up)>1 and cross(up[-2],up[-1],p)<=0:up.pop()
  up.append(p)
 return low[:-1]+up[:-1]
def area(p):return Q(abs(sum(a[0]*b[1]-a[1]*b[0] for a,b in zip(p,p[1:]+p[:1]))),2)
P=hull(f);T=hull(g);S=hull([(a+c,b+d) for a,b in P for c,d in T])
assert P==[(0,0),(1,0),(0,1)]
assert T==[(0,0),(3,0),(0,3)]
assert S==[(0,0),(4,0),(0,4)]
A=area(S)-area(P)-area(T)
assert A==3 and A/2==Q(3,2)
assert 1!=A and 1!=A/2
print('PASS: exact four ideal identities; unique root (1,-2); Jacobian polynomial 1.')
print('PASS: actual support convex hulls:',P,T,'; Minkowski hull:',S)
print('PASS: areas',area(P),area(T),area(S),'; BKK mixed area',A,'; classical mixed area',A/2)
