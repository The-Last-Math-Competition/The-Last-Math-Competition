"""Supplementary exact logarithm-interval checks for integer linear forms.

All mathematical comparisons use Fraction intervals. Floating point appears
only when formatting output. The universal theorem and limits are proved
in Lean; finitely many examples are not used to justify an asymptotic claim.
"""
from fractions import Fraction as Q
import json

def log_unit(u, terms=160):
    assert 1 <= u <= 2
    t = (u - 1) / (u + 1)
    power = t
    lower = Q(0)
    for k in range(terms):
        lower += 2 * power / (2*k + 1)
        power *= t*t
    remainder = 2 * power / ((2*terms + 1) * (1 - t*t))
    return lower, lower + remainder

L2 = log_unit(Q(2))

def log_integer(n):
    assert n >= 1
    e = n.bit_length() - 1
    a, b = log_unit(Q(n, 2**e))
    return a + e*L2[0], b + e*L2[1]

L3 = log_integer(3)
assert 0 < L2[0] < L2[1] < L3[0] < L3[1]
xi = (L2[0] + L2[1]) / (L3[0] + L3[1])
p0, p1, q0, q1 = 0, 1, 1, 0
samples = []
for _ in range(16):
    digit = xi.numerator // xi.denominator
    p = digit*p1 + p0
    q = digit*q1 + q0
    p0, p1, q0, q1 = p1, p, q1, q
    frac = xi - digit
    assert frac > 0
    xi = 1 / frac
    if p == 0 or q == 0:
        continue
    a, b = q, p
    lower, upper = a*L2[0] - b*L3[1], a*L2[1] - b*L3[0]
    assert upper < 0 or lower > 0
    abs_lower = min(abs(lower), abs(upper))
    abs_upper = max(abs(lower), abs(upper))
    assert 0 < abs_lower <= abs_upper <= L3[0] / (a + 1)
    H = max(3, a, b)
    _, logH_upper = log_integer(H)
    scaled_upper = abs_upper * logH_upper**2
    samples.append({'a':a, 'b':b, 'actual_height':H,
                    'abs_form_upper_display':float(abs_upper),
                    'abs_form_times_log_height_squared_upper_display':float(scaled_upper)})
assert len(samples) >= 12
assert samples[-1]['actual_height'] > 10**7
assert scaled_upper < Q(1, 10000)
print(json.dumps({'result':'PASS', 'arithmetic':'exact Fraction intervals',
                  'certified_examples':samples,
                  'universal_limit_proof':'Lean, not finite numerical extrapolation'}))
