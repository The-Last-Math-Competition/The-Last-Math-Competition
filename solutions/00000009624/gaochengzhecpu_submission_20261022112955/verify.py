"""Independent exact finite checks for the bilateral three-symbol shift.
The Lean proof, not this finite script, establishes all n and genuine topological entropy.
"""
from itertools import product

def extend(word):
    return lambda k: word[k] if 0 <= k < len(word) else 0

def shift(x):
    return lambda k: x(k + 1)

def unshift(x):
    return lambda k: x(k - 1)

checked = 0
for n in range(9):
    words = list(product(range(3), repeat=n))
    traces = set()
    for word in words:
        x = extend(word)
        orbit = x
        observed = []
        for k in range(n):
            observed.append(orbit(0))
            orbit = shift(orbit)
        trace = tuple(observed)
        assert trace == word
        traces.add(trace)
        for k in range(-2, n + 2):
            assert shift(unshift(x))(k) == x(k)
            assert unshift(shift(x))(k) == x(k)
            block = tuple(x(k + offset) for offset in (-1, 0, 1))
            assert shift(x)(k) == block[2]
            assert unshift(x)(k) == block[0]
        checked += 1
    assert len(traces) == 3**n
    print(f"PASS n={n}: {len(traces)} distinct actual orbit traces, radius-one rules and inverses")

x = lambda k: 0
y = lambda k: 1 if k == 1 else 0
assert x(0) == y(0)
assert shift(x)(0) != shift(y)(0)
assert 3 > 2 > 0
print(f"PASS: {checked} exact word configurations; radius zero impossible; log3>log2 by strict monotonicity")
