from itertools import permutations
from functools import cache
N=5
W=list(permutations(range(1,N+1)))
def length(w):return sum(w[i]>w[j] for i in range(N) for j in range(i+1,N))
def le(x,w):return all(sum(x[i]>=b for i in range(a))<=sum(w[i]>=b for i in range(a)) for a in range(N+1) for b in range(1,N+1))
def swap(w,i):return w[:i]+(w[i+1],w[i])+w[i+2:]
def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,v in enumerate(a):c[i]+=v
 for i,v in enumerate(b):c[i]+=v
 while c and c[-1]==0:c.pop()
 return tuple(c)
def mul(a,b):
 c=[0]*max(0,(len(a)+len(b)-1))
 for i,u in enumerate(a):
  for j,v in enumerate(b):c[i+j]+=u*v
 while c and c[-1]==0:c.pop()
 return tuple(c)
@cache
def R(x,w):
 if not le(x,w):return ()
 if x==w:return (1,)
 i=max(i for i in range(N-1) if w[i]>w[i+1])
 xs,ws=swap(x,i),swap(w,i)
 if length(xs)<length(x):return R(xs,ws)
 return add(mul((-1,1),R(x,ws)),mul((0,1),R(xs,ws)))
@cache
def P(x,w):
 if not le(x,w):return ()
 if x==w:return (1,)
 s=()
 for z in W:
  if x!=z and le(x,z) and le(z,w):s=add(s,mul(R(x,z),P(z,w)))
 d=length(w)-length(x)
 p=tuple(-(s[i] if i<len(s) else 0) for i in range((d-1)//2+1))
 while p and p[-1]==0:p=p[:-1]
 lhs=add(tuple([0]*(d-len(p)+1)+list(reversed(p))),tuple(-v for v in p))
 assert lhs==s,(x,w,p,s,lhs)
 return p
w=(3,4,5,1,2);x=(1,2,3,4,5)
print('R inversion independent P:',P(x,w),'length',length(w))
print('interval pairs cache',P.cache_info())
