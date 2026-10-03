"""Independent exact checks for the two root-agent counterexamples."""
from fractions import Fraction
from itertools import product
import json

coefficients = [0] * 9
for a, b, c, d in product(range(3), repeat=4):
    if a >= b and a >= c and b >= d and c >= d:
        coefficients[a+b+c+d] += 1
assert coefficients == [1,1,3,3,4,3,3,1,1]
assert coefficients[1] ** 2 < coefficients[0] * coefficients[2]

# Exact truncated formal series for MacMahon's product; no floating point.
series = [1] + [0] * 8
for i,j,k in product(range(1,3), repeat=3):
    numerator, denominator = i+j+k-1, i+j+k-2
    old = series[:]
    series = [old[n] - (old[n-numerator] if n >= numerator else 0) for n in range(9)]
    for n in range(denominator, 9):
        series[n] += series[n-denominator]
assert series == coefficients

ratio = Fraction(4,3) / Fraction(7,4)
assert ratio == Fraction(16,21) and ratio != Fraction(7,9)
assert 1/ratio != Fraction(7,9)
print(json.dumps({"425": {"coefficients": coefficients, "macmahon": series}, "996": {"ratio": str(ratio), "reverse": str(1/ratio)}}))
