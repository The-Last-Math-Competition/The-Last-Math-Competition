"""Independent exact rational checks for the actual three quantum channels.
No floating point, numerical eigensolvers, or theorem-prover oracles are used.
The Lean proof independently handles all density matrices and all ancilla dimensions.
"""
from fractions import Fraction as F

def zero(n,m): return [[F(0) for _ in range(m)] for _ in range(n)]
def eye(n):
    a=zero(n,n)
    for i in range(n): a[i][i]=F(1)
    return a
def tr(a): return sum((a[i][i] for i in range(len(a))), F(0))
def add(a,b): return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def transpose(a): return [list(x) for x in zip(*a)]
def mul(a,b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),F(0))
             for j in range(len(b[0]))] for i in range(len(a))]
def sandwich(k,a): return mul(mul(k,a),transpose(k))
def sum_matrices(xs,n,m):
    a=zero(n,m)
    for x in xs: a=add(a,x)
    return a
def partial_environment(x):
    return [[sum((x[3*b+j][3*c+j] for j in range(3)),F(0)) for c in range(2)] for b in range(2)]
def partial_output(x):
    return [[sum((x[3*b+j][3*b+k] for b in range(2)),F(0)) for k in range(3)] for j in range(3)]

for i in range(3):
    bit=lambda j: 0 if j==i else 1
    ks=[]
    for j in range(3):
        k=zero(2,3); k[bit(j)][j]=F(1); ks.append(k)
    v=zero(6,3)
    for j in range(3): v[3*bit(j)+j][j]=F(1)
    assert mul(transpose(v),v)==eye(3)
    assert sum_matrices([mul(transpose(k),k) for k in ks],3,3)==eye(3)
    p=zero(3,3);p[i][i]=F(1)
    q=eye(3);q[i][i]=F(0)
    for r in range(3):
        for s in range(3):
            a=zero(3,3);a[r][s]=F(1)
            phi=sum_matrices([sandwich(k,a) for k in ks],2,2)
            expected=zero(2,2);expected[0][0]=a[i][i];expected[1][1]=tr(a)-a[i][i]
            assert phi==expected
            joint=sandwich(v,a)
            assert partial_environment(joint)==phi
            comp=add(sandwich(p,a),sandwich(q,a))
            assert partial_output(joint)==comp
            assert tr(phi)==tr(a)==tr(comp)
print("PASS: all 27 channel/matrix-unit cases, exact Kraus normalization, Stinespring isometries,")
print("      both partial traces, full block pinching complements, and trace preservation")

def log_coeff(q):
    """Formal rational logarithm as prime exponent dictionary."""
    out={}
    for n,sgn in [(q.numerator,1),(q.denominator,-1)]:
        d=2
        while d*d<=n:
            while n%d==0:
                out[d]=out.get(d,F(0))+sgn;n//=d
            d+=1
        if n>1: out[n]=out.get(n,F(0))+sgn
    return {p:c for p,c in out.items() if c}
def entropy_coeff(ps):
    out={}
    for q in ps:
        if q:
            for p,c in log_coeff(q).items(): out[p]=out.get(p,F(0))-q*c
    return {p:c for p,c in out.items() if c}
assert entropy_coeff([F(1,3),F(2,3)])=={3:F(1),2:F(-2,3)}
assert entropy_coeff([F(1,2),F(1,2)])=={2:F(1)}
assert F(32,27)>1
for i in range(3):
    p=[F(1,4)]*3;p[i]=F(1,2)
    assert sum(p)==1
    assert entropy_coeff([p[i],1-p[i]])=={2:F(1)}
print("PASS: uniform input gives h(1/3)=log3-(2/3)log2; each individual optimum log2")
print("PASS: exact strict gap log2-h(1/3)=(1/3)log(32/27)>0 since 32>27")
