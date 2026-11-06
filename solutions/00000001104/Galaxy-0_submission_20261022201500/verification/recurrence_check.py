from itertools import permutations
from functools import cache
N=5
ps=list(permutations(range(N)))
@cache
def length(p):return sum(p[i]>p[j] for i in range(N) for j in range(i+1,N))
@cache
def leq(x,w):return all(all(a<=b for a,b in zip(sorted(x[:i]),sorted(w[:i]))) for i in range(1,N+1))
def sw(x,s):p=list(x);p[s],p[s+1]=p[s+1],p[s];return tuple(p)
def add(*vs):
 n=max(map(len,vs),default=0);out=[0]*n
 for v in vs:
  for i,a in enumerate(v):out[i]+=a
 while out and out[-1]==0:out.pop()
 return tuple(out)
def shift(p,k,c=1):return (0,)*k+tuple(c*x for x in p) if p else ()
@cache
def kl(x,w):
 if not leq(x,w):return ()
 if x==w:return (1,)
 s=next(i for i in range(N-1) if w[i]>w[i+1]);ws=sw(w,s);xs=sw(x,s);c=int(length(xs)<length(x))
 out=add(shift(kl(xs,ws),1-c),shift(kl(x,ws),c))
 for z in ps:
  d=length(ws)-length(z)
  if d>0 and d%2 and z[s]>z[s+1] and leq(x,z) and leq(z,ws):
   p=kl(z,ws);mu=p[(d-1)//2] if (d-1)//2<len(p) else 0
   if mu:out=add(out,shift(kl(x,z),(length(w)-length(z))//2,-mu))
 return out
w=(2,3,4,0,1)
x=tuple(range(5))
assert kl(x,w)==(1,2)
assert length(w)==6
s=2;v=sw(w,s)
assert kl(sw(x,s),v)==(1,)
assert kl(x,v)==(1,1)
print("P_e,34512 =",kl(x,w),"length =",length(w))
print("P_s3,34152 =",kl(sw(x,s),v),"P_e,34152 =",kl(x,v))
