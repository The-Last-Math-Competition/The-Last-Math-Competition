#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000002805 (REFUTED).

Conjecture: the Schilder rate vanishes iff the path is in the
Cameron-Martin unit ball; the spectral distribution of the rate on
the sphere is a chi-square-type law.

Refutation: I(w) = ||w||_H^2 / 2 vanishes iff w = 0 (the zero path),
not on the whole unit ball: w(t) = t/2 is in the ball with I = 1/8.
On the unit sphere the rate is the CONSTANT 1/2 -- a point mass,
not a chi-square-type law.
"""

from fractions import Fraction as F

# Cameron-Martin inner product: <w,v>_H = int_0^1 w' v' dt (w(0)=0 paths)
# one-dimensional subspaces w_c(t) = c*t have ||w_c||_H^2 = c^2, I = c^2/2.

# ---------- gate 1: rate vanishes iff w = 0 (exact rationals) ----------
for c in [F(0), F(1, 4), F(1, 2), F(1), F(3, 2)]:
    I = c * c / 2
    norm2 = c * c
    in_ball = norm2 <= 1
    if c == 0:
        assert I == 0
    else:
        assert I > 0
    print(f"c = {c}: ||w||_H^2 = {norm2}, in unit ball = {in_ball}, I = {I}")

c = F(1, 2)
assert c <= 1 and c * c / 2 == F(1, 8) and F(1, 8) > 0
print("counterexample w(t) = t/2: IN the unit ball with I = 1/8 != 0 — OK")
print("rate vanishes iff w = 0, NOT iff w in the unit ball — rigidity clause REFUTED")

# ---------- gate 2: rate on the sphere is constant, not chi-square ----------
for c in (F(1), F(-1)):
    assert abs(c) == 1 and c * c / 2 == F(1, 2)
print("on the unit sphere (|c| = 1): I = 1/2 for EVERY point — point mass — OK")
print("a chi-square-type law is non-degenerate; the sphere rate is constant — spectral clause REFUTED")

# ---------- gate 3: full 2D Cameron-Martin coordinates ----------
# w(t) = a1*e1(t) + a2*e2(t), e_k(t) = sqrt(2) sin(k pi t)/(k pi):
# ||w||_H^2 = a1^2 + a2^2, I = (a1^2 + a2^2)/2 — depends only on the norm;
# the "spectral distribution" on the sphere r = 1 is delta_{1/2}.
import math
for (a1, a2) in ((1.0, 0.0), (0.6, 0.8), (1 / math.sqrt(2), 1 / math.sqrt(2))):
    n2 = a1 * a1 + a2 * a2
    assert abs(n2 - 1) < 1e-12 and abs(n2 / 2 - 0.5) < 1e-12
print("2D check: every sphere point (a1,a2), a1^2+a2^2 = 1 has I = 1/2 exactly — OK")

print("\nALL CHECKS PASSED: conjecture 00000002805 REFUTED "
      "(rate vanishes only at w=0; sphere rate constant 1/2, not chi-square)")
