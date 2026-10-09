#!/usr/bin/env python3
"""Independent exact determinant and isomorphism check; no external packages."""
from itertools import permutations
from collections import defaultdict

def adj(g,i,j):
 if i==j:return 0
 i,j=sorted((i,j));return (g>>(j*(j-1)//2+i))&1

def mul(p,q):
 out=[0]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):out[i+j]+=a*b
 return out

def cp(n,g):
 out=[0]*(n+1)
 for p in permutations(range(n)):
  sign=(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
  term=[sign]
  for i in range(n):term=mul(term,[-adj(g,i,p[i]),int(i==p[i])])
  out=[a+b for a,b in zip(out,term)]
 return tuple(out)

def iso(n,g,h):return any(all(adj(g,i,j)==adj(h,p[i],p[j]) for i in range(n) for j in range(n)) for p in permutations(range(n)))

def main():
 for n in range(5):
  buckets=defaultdict(list)
  for g in range(1<<(n*(n-1)//2)):buckets[cp(n,g)].append(g)
  for group in buckets.values():
   for g in group:
    for h in group:assert iso(n,g,h),(n,g,h)
  print(f'n={n}: {sum(map(len,buckets.values()))} labeled graphs; {len(buckets)} distinct characteristic polynomials; all equal-spectrum pairs isomorphic')
 assert cp(5,75)==cp(5,45)==(0,0,0,-4,0,1)
 assert not iso(5,75,45)
 print('5-vertex witnesses: masks 75 and 45; polynomial X^5-4X^3; nonisomorphic; minimum proved.')
if __name__=='__main__':main()
