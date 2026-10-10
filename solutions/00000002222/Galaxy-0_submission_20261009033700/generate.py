#!/usr/bin/env python3
"""Deterministically generate finite certificates. Lean checks all output."""
from math import gcd,prod
from pathlib import Path

def factors(n):
 out=[];p=2
 while p*p<=n:
  if n%p==0:
   a=0
   while n%p==0:n//=p;a+=1
   out.append((p,a))
  p+=1
 if n>1:out.append((n,1))
 return out

def certificate(n):
 fs=factors(n)
 if n==1 or (len(fs)==1 and fs[0][1]==1):return [],[]
 d=prod(p**((a+1)//2) for p,a in fs)
 core=list(range(d,n,d)) if d else []
 groups={('core',x):[x] for x in core};clique=core[:]
 for p,a in fs:
  if a%2:
   groups[('odd',p)]=[]
   clique.append(n//(p**((a+1)//2)))
 vertices=[x for x in range(1,n) if gcd(n,x)>1]
 for x in vertices:
  if x%d==0:continue
  p,a=next((p,a) for p,a in fs if x%(p**((a+1)//2))!=0)
  key=('odd',p) if a%2 else ('core',n//(p**(a//2)))
  groups[key].append(x)
 C=list(groups.values())
 assert sorted(sum(C,[]))==vertices
 assert len(clique)==len(C) and len(set(clique))==len(clique)
 assert all(x in vertices for x in clique)
 assert all(x*y%n==0 for i,x in enumerate(clique) for y in clique[i+1:])
 for c in C:
  if not c:continue
  a,*xs=c;ds=set(gcd(n,x) for x in xs)
  assert all(a*x%n!=0 for x in xs)
  assert all(d*e%n!=0 for d in ds for e in ds)
 return C,clique

def lean(x):return str(x).replace(' ','')

def write_chunk(nums,path):
 s=['import Basic','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace TLMC2222']
 for n in nums:
  C,K=certificate(n)
  s += [f'def C{n} : List (List Nat) := {lean(C)}',f'def K{n} : List Nat := {lean(K)}',f'theorem cert{n} : check {n} C{n} K{n} := by decide',f'theorem result{n} : EqualChromaticClique {n} := check_sound (by decide) cert{n}']
 nums=list(nums)
 lo,hi=nums[0],nums[-1]
 s += [f'theorem range{lo}_{hi} (n : Nat) (hl : {lo} ≤ n) (hh : n ≤ {hi}) : EqualChromaticClique n := by',
       '  have h : '+ ' ∨ '.join(f'n = {n}' for n in nums) + ' := by omega',
       '  rcases h with '+ ' | '.join('h'+str(n) for n in nums)]
 for n in nums: s += [f'  · subst n; exact result{n}']
 s+=['end TLMC2222']
 Path(path).write_text('\n'.join(s)+'\n')

if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--all',action='store_true');a=p.parse_args()
 if a.all:
  for i in range(20):write_chunk(range(i*50+1,i*50+51),f'Cert{i:02}.lean')
 else:write_chunk([1000],'Bench.lean')
 print('Generated; all Python arithmetic and partition assertions passed.')
