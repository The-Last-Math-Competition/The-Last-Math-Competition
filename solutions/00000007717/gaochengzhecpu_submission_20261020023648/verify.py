"""Exact independent structural and Rayleigh sanity check; no floating point."""
from collections import deque
from fractions import Fraction
V = [(i, j) for i in range(64) for j in range(4)]
def neighbors(v):
    i, j = v
    return {((i+1)%64,j), ((i-1)%64,j), (i,(j+1)%4), (i,(j-1)%4)}
assert len(V) == 256
assert all(len(neighbors(v)) == 4 and v not in neighbors(v) for v in V)
assert all(v in neighbors(w) for v in V for w in neighbors(v))
seen = {(0,0)}
queue = deque(seen)
while queue:
    for w in neighbors(queue.popleft()):
        if w not in seen:
            seen.add(w)
            queue.append(w)
assert len(seen) == 256
for i,j in V:
    cell = [(i,j), ((i+1)%64,j), ((i+1)%64,(j+1)%4), (i,(j+1)%4)]
    assert len(set(cell)) == 4
    assert all(cell[(k+1)%4] in neighbors(cell[k]) for k in range(4))
def f(v):
    return min(v[0], 64-v[0])-16
assert sum(map(f,V)) == 0
norm = sum(f(v)**2 for v in V)
energy_twice = sum((f(v)-f(w))**2 for v in V for w in neighbors(v))
assert energy_twice % 2 == 0
energy = energy_twice // 2
assert (energy,norm) == (256,21888)
assert Fraction(energy,norm) == Fraction(2,171) < Fraction(3,256)
print('PASS: actual square quotient: 256 vertices, degree 4, connected, four-edge cells; exact Rayleigh quotient 2/171 < 3/256.')
