#!/usr/bin/env python3
"""Independent chronological permutation enumeration; not a proof premise."""
import itertools, math, collections, json
checks = []
for n in range(9):
    counts = collections.Counter()
    for p in itertools.permutations(range(n)):
        b = tuple(all(p[j] < p[i] for j in range(i)) for i in range(n))
        counts[b] += 1
    for b in itertools.product([False, True], repeat=n):
        expected = math.prod(1 if flag else i for i, flag in enumerate(b))
        assert counts[b] == expected, (n,b,counts[b],expected)
    assert sum(counts.values()) == math.factorial(n)
    checks.append({'n':n,'actual_permutations':math.factorial(n),'patterns_checked':2**n})
print(json.dumps({'result':'PASS','checks':checks},indent=2))
