#!/usr/bin/env python3
"""Independent exact check of the standard subresultant construction."""
import itertools,json
from pathlib import Path

def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    while len(out)>1 and out[-1]==0:out.pop()
    return out

def add(a,b):
    out=[(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
    while len(out)>1 and out[-1]==0:out.pop()
    return out

def det(a):
    n=len(a); assert all(len(row)==n for row in a)
    answer=0
    for p in itertools.permutations(range(n)):
        term=(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        for i in range(n):term*=a[i][p[i]]
        answer+=term
    return answer

def sylvester_submatrix(f,g,i):
    n=len(f)-1;m=len(g)-1
    assert n>=m>i>=0
    width=n+m-i
    rows=[]
    for poly,count in [(f,m-i),(g,n-i)]:
        for shift in reversed(range(count)):
            shifted=[0]*shift+poly
            rows.append([(shifted[k] if k<len(shifted) else 0) for k in reversed(range(width))])
    assert len(rows)==n+m-2*i
    return rows

def coeff_minor(matrix,k,t):
    cols=list(range(k-1))+[k+t-1]
    return det([[matrix[r][c] for c in cols] for r in range(k)])

f=[0,-4,0,1];g=[-1,0,1]
assert f==mul(mul([2,1],[0,1]),[-2,1])
assert g==mul([1,1],[-1,1])
assert len(f)==4 and len(g)==3 and f[-1]==g[-1]==1
f_roots=[-2,0,2];g_roots=[-1,1]
interleaving=[f_roots[0],g_roots[0],f_roots[1],g_roots[1],f_roots[2]]
assert all(a<b for a,b in zip(interleaving,interleaving[1:]))
assert not set(f_roots)&set(g_roots)
# This Bezout identity independently excludes all common roots over characteristic zero.
assert add(mul([0,1],f),mul([3,0,-1],g))==[-3]
s=sylvester_submatrix(f,g,1)
assert s==[[1,0,-4,0],[1,0,-1,0],[0,1,0,-1]]
m30=coeff_minor(s,3,0);m31=coeff_minor(s,3,1)
assert (m30,m31)==(-3,0)
# Sres_i=sum_j M_(n+m-2i,i-j) x^j.
sres=[coeff_minor(s,3,1-j) for j in range(2)]
assert sres==[0,-3]
assert add(f,mul([0,-1],g))==sres
result={'f_coefficients_ascending':f,'g_coefficients_ascending':g,'sylvester_submatrix_index':1,'sylvester_submatrix':s,'minor_order':3,'M_3_0':m30,'M_3_1':m31,'subresultant_coefficients_ascending':sres,'strict_root_interleaving':interleaving,'bezout_constant':-3,'claim_M_3_1_zero_iff_M_3_0_zero':False}
print(json.dumps(result,indent=2))
Path(__file__).with_name('independent_check.json').write_text(json.dumps(result,indent=2)+'\n')
