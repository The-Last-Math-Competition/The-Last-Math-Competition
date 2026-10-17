from fractions import Fraction as Q
from itertools import combinations, permutations, product
from math import comb

V = frozenset(range(4))
E = tuple(frozenset(e) for e in combinations(V, 2))

def subsets(s):
    s=tuple(s)
    return (frozenset(x) for k in range(len(s)+1) for x in combinations(s,k))

def cycles(k):
    answer=set()
    for perm in permutations(V,k):
        edges=frozenset(frozenset((perm[i],perm[(i+1)%k])) for i in range(k))
        answer.add((frozenset(perm),edges))
    return answer

T,S=cycles(3),cycles(4)
assert len(T)==4 and len(S)==3
for vs,es in T|S:
    assert len(vs)==len(es)
    for ws in subsets(vs):
        if not ws: continue
        available=frozenset(e for e in es if e<=ws)
        for fs in subsets(available):
            if (ws,fs)==(vs,es): continue
            assert len(fs)*len(vs)<len(es)*len(ws)

hosts=list(subsets(E))
assert len(hosts)==64
tri=lambda h:sum(e<=h for v,e in T)
sq=lambda h:sum(e<=h for v,e in S)

def expansion(count):
    coeff=[0]*7
    for h in hosts:
        m=len(h)
        for j in range(7-m):
            coeff[m+j]+=count(h)*(-1)**j*comb(6-m,j)
    return coeff
assert expansion(lambda _:1)==[1,0,0,0,0,0,0]
assert expansion(tri)==[0,0,0,4,0,0,0]
assert expansion(sq)==[0,0,0,0,3,0,0]
for p in [Q(1,4),Q(1,2),Q(1,3),Q(3,4)]:
    prob=lambda h:p**len(h)*(1-p)**(6-len(h))
    assert sum(map(prob,hosts))==1
    a=sum(tri(h)*prob(h) for h in hosts)
    b=sum(sq(h)*prob(h) for h in hosts)
    assert a==4*p**3 and b==3*p**4
    print(f'p={p}: E(C3)={a}, E(C4)={b}, ratio={a/b}')
print('6182 PASS: generated unordered cycles, strict balance of all copies, all 64 hosts, exact probability and expectation polynomials.')

M=range(6)
mult=min
for a,b,c in product(M,repeat=3):
    assert mult(mult(a,b),c)==mult(a,mult(b,c))
for a in M:
    assert mult(a,5)==a==mult(5,a)
    inverses=[b for b in M if mult(mult(a,b),a)==a and mult(mult(b,a),b)==b]
    assert inverses==[a]
units=[a for a in M if any(mult(a,b)==5==mult(b,a) for b in M)]
assert units==[5]
characters=[f for f in product((0,1),repeat=6) if f[5]==1 and all(f[min(i,j)]==f[i]*f[j] for i,j in product(M,repeat=2))]
thresholds=[tuple(int(i>=t) for i in M) for t in M]
assert set(characters)==set(thresholds) and len(characters)==6
assert {tuple(f[i] for i in units) for f in characters}=={(1,)}
assert len([f for f in characters if f[0]==0])==5
assert all(2**k not in (5,6) for k in range(10))
print('8207 PASS: monoid/inverses/units; all Boolean characters are precisely the six thresholds; one restriction value; zero-preserving subset has five. General representation classification requires the algebraic proof, not this enumeration.')

for n in range(4,30):
    for p in [Q(1,4),Q(1,2),Q(1,n),Q(2,n)]:
        a=comb(n,3)*p**3
        b=3*comb(n,4)*p**4
        assert a/b==Q(4,3*(n-3))/p
for n in [10,100,1000]:
    c=Q(2)
    ratio=Q(4*n,3*(n-3))/c
    assert ratio-Q(4,3)/c==Q(4,c*(n-3))
print("6182 PASS: all-n formula 4/[3(n-3)p], checked n=4,...,29; threshold-scale difference from 4/(3c) exactly 4/[c(n-3)].")
