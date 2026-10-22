"""Independent exact rational certificate and graph enumeration for conjecture 8908."""
from fractions import Fraction as Q
from itertools import combinations
import json
n=5
b=[-9,32,8,8,32]
B=[[b[(j-i)%n] for j in range(n)] for i in range(n)]
G=[[sum(B[k][i]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
adj=lambda i,j:(i-j)%n in (1,4)
comp=lambda i,j:i!=j and not adj(i,j)
assert all(G[i][j]==(2257 if i==j else 0 if adj(i,j) else 1392) for i in range(n) for j in range(n))
X=[[Q(G[i][j],11285) for j in range(n)] for i in range(n)]
assert sum(X[i][i] for i in range(n))==1
assert all(X[i][j]==0 for i in range(n) for j in range(n) if adj(i,j))
objective=sum(map(sum,X))
assert objective==Q(5041,2257)>2
# Positive semidefiniteness is certified by X=B^T B/11285 exactly.
# In particular x^T X x = sum_k (sum_i B[k][i] x_i)^2/11285 for all real x.
def clique_num(a):
    return max(k for k in range(n+1) if any(all(a(i,j) for i,j in combinations(s,2)) for s in combinations(range(n),k)))
assert clique_num(comp)==2
assert clique_num(lambda i,j:i!=j and not adj(i,j))==2
assert all(not all(comp(i,j) for i,j in combinations(s,2)) for s in combinations(range(n),3))
print(json.dumps({'B':B,'Gram':G,'trace':str(sum(X[i][i] for i in range(n))),'objective':str(objective),'gap_above_two':str(objective-2),'complement_clique':clique_num(comp),'independence':clique_num(comp),'PSD_certificate':'Exact Gram factorization B^T B / 11285; no eigenvalue approximation'},indent=2))
