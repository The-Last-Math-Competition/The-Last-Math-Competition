from fractions import Fraction as F
from itertools import permutations, product, combinations
S=[(0,0,0),(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]
w=[F(i,100) for i in range(5)]
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def sc(t,a):return tuple(t*x for x in a)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def power(i,x):return dot(sub(x,S[i]),sub(x,S[i]))-w[i]
margins=[]; volumes=[]
for i,j in permutations(range(5),2):
 a=sc((3-w[j])/6,S[j]) if i==0 else sc((3-w[i])/6,S[i]) if j==0 else add(add(S[i],S[j]),sc((w[j]-w[i])/16,sub(S[i],S[j])))
 n=sub(S[i],S[j]);u=(-n[1],n[0],0) if n[0] else (n[1],-n[0],0) if n[1] else (1,0,0)
 v=(-n[2],0,n[0]) if n[0] else (0,-n[2],n[1]) if n[1] else (0,1,0)
 b=add(a,sc(F(1,1000),u));c=add(a,sc(F(1,1000),v))
 assert cross(sub(b,a),sub(c,a))!=(0,0,0)
 for x in (a,b,c):
  assert power(i,x)==power(j,x)
  for k in range(5):
   if k not in (i,j):
    m=power(k,x)-power(i,x); assert m>0;margins.append(m)
for i,j,k,l in combinations(range(5),4):
 d=dot(sub(S[j],S[i]),cross(sub(S[k],S[i]),sub(S[l],S[i])));assert d;volumes.append(d)
print('All 20 ordered-pair certificates verified; smallest strict margin:',min(margins))
print('Five increasing-order determinants:',volumes)
# Independent rotations generated from cycle permutations, not Lean table.
orders=[(0,)+p for p in permutations((1,2,3))]
darts=[(i,j) for i in range(5) for j in range(5) if i!=j]
faces={}
for rr in product(orders,repeat=5):
 successor={}
 for i in range(5):
  neigh=[j for j in range(5) if j!=i]
  cyc=[neigh[p] for p in rr[i]]
  for a,b in zip(cyc,cyc[1:]+cyc[:1]):successor[(a,i)]=(i,b)
 remaining=set(darts); count=0
 while remaining:
  d=next(iter(remaining));count+=1
  while d in remaining:remaining.remove(d);d=successor[d]
 faces[count]=faces.get(count,0)+1
assert sum(faces.values())==6**5 and 7 not in faces
print('Independently traversed 7776 rotation systems. Facial-cycle histogram:',faces)
