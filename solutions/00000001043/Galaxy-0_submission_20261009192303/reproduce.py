#!/usr/bin/env python3
"""Independent exact arithmetic check; Lean is the authoritative formal proof."""
from itertools import product

P = 11

def inverse(x):
    return pow(x, P-2, P)

def witness(x):
    return {7:8, 8:7, 9:10, 10:9}.get(x, x)

def polynomial(x):
    return (x-pow(x-7,10,P)+pow(x-8,10,P)-pow(x-9,10,P)+pow(x-10,10,P)) % P

assert all(P % d for d in range(2, P))
assert sorted(witness(x) for x in range(P)) == list(range(P))
assert all(inverse(inverse(x)) == x for x in range(P))
assert all(polynomial(x) == witness(x) for x in range(P))
assert all(inverse(inverse(a)*x % P) == a*inverse(x) % P
           for a in range(1,P) for x in range(P))

for layers in (3,4):
    failures = [0] * P
    count = 0
    for parameters in product(range(P), repeat=layers):
        h = [witness(x) for x in range(P)]
        for b in parameters:
            h = [inverse((y-b) % P) for y in h]
        slope = (h[1]-h[0]) % P
        failed = next((x for x in range(P) if h[x] != (slope*x+h[0]) % P), None)
        assert failed is not None, (layers, parameters, h)
        failures[failed] += 1
        count += 1
    assert count == P**layers
    print(f'{layers} layers: {count} tuples, zero affine survivors; first-failure counts {failures}')
print('Every exact check passed. These auxiliary checks do not replace the complete Lean proof.')
