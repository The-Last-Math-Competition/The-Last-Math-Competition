#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000003901 (REFUTED).

Conjecture: for every ideal in an n-dimensional ring, the length of
I^{[p^e]}/I (Frobenius exponent quotient) has leading exponent n-1
in p^e, with explicit leading coefficient (Newton polyhedron boundary
measure)/(n-1)!.

Refutation at R = k[x,y] (n = 2), I = (x,y): the finite-length
Frobenius quotient m/(x^q, y^q) has length q^2 - 1 (monomials of the
q x q box minus the origin), verified q = 2..8: exponent 2 = n, not
n - 1 = 1; and the length exceeds C*q for every fixed C (at q = 2C+1
the excess is 2C^2 + 3C > 0): no finite leading coefficient at
exponent n-1.
"""

from fractions import Fraction as F

# ---------- gate 1: exact length of m/(x^q, y^q) ----------
def length(q):
    return sum(1 for i in range(q) for j in range(q) if i + j >= 1)

for q in range(2, 9):
    assert length(q) == q * q - 1, (q, length(q))
    print(f"q = {q}: len(m/(x^q, y^q)) = q^2 - 1 = {q*q - 1}")

# ---------- gate 2: leading exponent is 2 = n, not 1 ----------
# fit log(len)/log(q) -> 2
import math
for q in (8, 16, 32):
    est = math.log(q*q - 1) / math.log(q)
    print(f"q = {q}: log(len)/log(q) = {est:.4f} (approaching 2 = n)")
    assert est > 1.5

# ---------- gate 3: no constant at exponent n-1 = 1 ----------
for C in (1, 2, 3, 5, 10, 100):
    q = 2 * C + 1
    L = q * q - 1
    assert L > C * q
    excess = L - C * q
    assert excess == 2 * C * C + 3 * C
    print(f"C = {C}: at q = {q}, len = {L} > C*q = {C*q} (excess {excess} = 2C^2+3C)")
print("length exceeds C * q^{n-1} for arbitrarily large C — no finite leading coefficient — REFUTED")

# ---------- gate 4: the true leading coefficient is 1 (q^2/1), i.e. volume, not boundary measure ----------
# The Newton polyhedron of (x,y) is the quadrant; its "boundary measure" reading cannot give
# the correct coefficient 1/(0!·2!)-type value: len ~ q^2 exactly, coefficient 1.
assert F(length(4), 4 ** 2) == F(15, 16)
print("true leading coefficient: len/q^2 -> 1 (the box volume), not a boundary measure — OK")

print("\nALL CHECKS PASSED: conjecture 00000003901 REFUTED "
      "(leading exponent is n = 2, not n - 1; no finite coefficient at n - 1)")
