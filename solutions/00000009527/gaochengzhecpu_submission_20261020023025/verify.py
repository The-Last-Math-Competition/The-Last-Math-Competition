"""Exact, independent sanity checks of all displayed qubit Kraus formulas.
The submitted Lean project proves the arbitrary complex-matrix identities and
all-ensemble Holevo comparisons; this script is auxiliary, not a proof oracle.
"""
from fractions import Fraction as F

def add(A,B): return [[A[i][j]+B[i][j] for j in range(2)] for i in range(2)]
def mul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def adj(A): return [[A[j][i] for j in range(2)] for i in range(2)]
def scale(c,A): return [[c*x for x in row] for row in A]
def unit(a,b): return [[F(i==a and j==b) for j in range(2)] for i in range(2)]
Z=scale(0,unit(0,0)); I=add(unit(0,0),unit(1,1))
def summ(xs):
 out=Z
 for A in xs: out=add(out,A)
 return out
def kraus(K,A): return summ(mul(mul(k,A),adj(k)) for k in K)
Kz=[unit(0,0),unit(1,1)]
Kd=[scale(F(1,2),unit(a,b)) for a in range(2) for b in range(2) for _ in range(2)]
Kr=[[unit(a,b) for b in range(2)] for a in range(2)]
for K in [Kz,Kd,*Kr]: assert summ(mul(adj(k),k) for k in K)==I
for a in range(2):
 for b in range(2):
  A=unit(a,b); tr=A[0][0]+A[1][1]
  assert kraus(Kz,A)==[[A[0][0],F(0)],[F(0),A[1][1]]]
  assert kraus(Kd,A)==scale(tr/2,I)
  for t in range(2): assert kraus(Kr[t],A)==scale(tr,unit(t,t))
assert kraus(Kr[0],unit(0,0)) != kraus(Kr[1],unit(0,0))
print('PASS: exact Kraus normalization, all complex-linear basis identities, distinct reset maps')
