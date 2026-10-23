"""Independent exhaustive arithmetic check, supplementary to the Lean proof."""
from itertools import product
V = list(product(range(2), repeat=2))
def product_(x,y):
    a,b=x; c,d=y
    return ((a*c+b*d)%2, (a*d+b*c)%2)
def action(x,v):
    a,b=x; u,w=v
    return ((a*u+b*w)%2,(a*w+b*u)%2)
D={v for v in V if v == v[::-1]}
idempotents=[a for a in V if product_(a,a)==a]
assert idempotents == [(0,0),(1,0)]
assert D == {(0,0),(1,1)}
assert all({action(a,v) for v in V} != D for a in idempotents)
assert {action((1,1),v) for v in V} == D
assert product_((1,1),(1,1)) == (0,0)
assert not any(all(action(a,v) in D for v in V) and all(action(a,v)==v for v in D) for a in V)
for a in V:
    for b in V:
        for v in V:
            assert action(product_(a,b),v)==action(a,action(b,v))
print('All 4 group-ring elements; all 4 cochains; 64 action-composition triples checked.')
print('Idempotents:',idempotents,'; fixed subspace:', sorted(D))
print('No group-ring idempotent has invariant image. Norm element has that image but squares to zero.')
