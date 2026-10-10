"""Supplementary exact arithmetic; the Lean proof is independent of this script."""
from collections import Counter
from math import gcd
import json

V = 21
D = {3, 6, 7, 12, 14}
differences = Counter((x - y) % V for x in D for y in D if x != y)
assert len(D) == 5 and differences == Counter({r: 1 for r in range(1, V)})
blocks = {frozenset((x + t) % V for x in D) for t in range(V)}
assert len(blocks) == V and all(len(b) == 5 for b in blocks)
assert all(sum(x in b and y in b for b in blocks) == 1
           for x in range(V) for y in range(V) if x != y)
units = [m for m in range(V) if gcd(m, V) == 1]
translations = {m: [t for t in range(V)
                    if {(m * x) % V for x in D} == {(x + t) % V for x in D}]
                for m in units}
multipliers = {m: ts for m, ts in translations.items() if ts}
assert set(multipliers) == {1, 2, 4, 8, 16, 11}
assert all(ts == [0] for ts in multipliers.values())
assert all(x % len(multipliers) != 0 for x in [V, len(D), 1, len(D) - 1, V * len(D)])
print(json.dumps({'difference_set': sorted(D), 'parameters': [V, len(D), 1],
                  'ordered_difference_counts': dict(sorted(differences.items())),
                  'block_count': len(blocks), 'pair_incidence': 1,
                  'multipliers_and_translations': multipliers,
                  'group_order': len(multipliers), 'all_checks': 'PASS'}, indent=2))
