#!/usr/bin/env python3
"""Independent finite checks. Python is corroboration, never a Lean proof oracle."""
from itertools import product
M = range(6)
meet = min
for a, b, c in product(M, repeat=3):
    assert meet(meet(a,b),c) == meet(a,meet(b,c))
for a in M:
    assert meet(a,5) == meet(5,a) == a
    assert [b for b in M if meet(meet(a,b),a)==a and meet(meet(b,a),b)==b] == [a]
assert [a for a in M if any(meet(a,b)==meet(b,a)==5 for b in M)] == [5]
print('Six-element min monoid: associativity, identity, unique inverses and unit group PASS')
expected = [tuple(int(t <= a) for a in M) for t in M]
for p in (2,3,5):
    chars = [x for x in product(range(p),repeat=6)
             if x[5] == 1 and all(x[min(a,b)] == x[a]*x[b]%p for a,b in product(M,repeat=2))]
    assert set(chars) == set(expected)
    assert len(chars) == 6
    assert len([x for x in chars if x[0]==0]) == 5
    assert {x[5] for x in chars} == {1}
    print(f'F_{p}: all scalar homomorphisms enumerated; ordinary fiber=6; contracted fiber=5 PASS')
# Exhaust all 2-dimensional representations over F_2, directly using matrix products.
matrices = list(product(range(2),repeat=4))
I = (1,0,0,1)
Z = (0,0,0,0)
def mul(A,B):
    a,b,c,d=A; e,f,g,h=B
    return ((a*e+b*g)%2,(a*f+b*h)%2,(c*e+d*g)%2,(c*f+d*h)%2)
def apply(A,v):
    a,b,c,d=A; x,y=v
    return ((a*x+b*y)%2,(c*x+d*y)%2)
idempotents=[A for A in matrices if mul(A,A)==A]
nonzero=[(1,0),(0,1),(1,1)]
count=0
for prefix in product(idempotents,repeat=5):
    rho=prefix+(I,)
    if not all(mul(rho[a],rho[b])==rho[min(a,b)] for a,b in product(M,repeat=2)):
        continue
    count+=1
    assert any(all(apply(A,v) in ((0,0),v) for A in rho) for v in nonzero)
print(f'F_2 dimension 2: all {count} actual matrix representations have an invariant proper line PASS')
assert all(2**k not in (5,6) for k in range(100))
print('Finite arithmetic regression PASS; Lean proves the all-k power obstruction.')
