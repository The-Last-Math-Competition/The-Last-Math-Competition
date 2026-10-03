#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000004165 (REFUTED).

Conjecture: shifted energy of squares has main-term coefficient
4/pi^2 and remainder decaying like sqrt(shift), unimprovable.

Refutation: (1) at X = 1, E_0(1) = 1 and E_h(1) = 0 for all h >= 1,
while sqrt(h) >= 1: the claimed remainder grows although the energy
vanishes (for h > 2X^2 the energy is identically 0 at any X).
(2) The off-diagonal energy E_h (fixed h >= 1) has main term C*X^2
WITHOUT a log factor, while the diagonal E_0 has an X^2 log X term —
two different structures, neither with coefficient 4/pi^2 ≈ 0.405
(diagonal measured ~0.66-0.72 of X^2 log X; off-diagonal ~0.67 of X^2).
"""

import math
from collections import Counter

def energy(X, h):
    cc = Counter()
    for a in range(1, X+1):
        for b in range(1, X+1):
            cc[a*a+b*b] += 1
    return sum(cnt * cc[s-h] for s, cnt in cc.items() if s-h in cc)

# ---------- gate 1: X = 1 ----------
assert energy(1, 0) == 1      # (1,1,1,1)
assert energy(1, 5) == 0      # no quadruple with diff 5
print("X = 1: E_0 = 1, E_h = 0 for h >= 1 — while sqrt(h) >= 1 grows — remainder clause REFUTED")

# ---------- gate 2: the energy vanishes for h > 2X^2 ----------
for X in (2, 5, 20):
    assert energy(X, 2 * X * X + 1) == 0
print("E_h = 0 for h > 2X^2 (max squared-sum difference) — sqrt(h) grows forever: unimprovable-sqrt claim impossible — OK")

# ---------- gate 3: two regimes, neither with 4/pi^2 ----------
for X in (120, 240, 480):
    E0 = energy(X, 0)
    E5 = energy(X, 5)
    print(f"X={X}: diagonal E_0/(X^2 log X) = {E0/(X*X*math.log(X)):.4f}; "
          f"off-diagonal E_5/X^2 = {E5/(X*X):.4f}")
print("diagonal has X^2 log X structure (~0.66-0.72); off-diagonal X^2 structure (~0.67) — "
      "a single coefficient 4/pi^2 = 0.405 matches neither — REFUTED")
assert abs(energy(480, 5) / (480**2) - 0.6730) < 0.001
assert abs(energy(480, 0) / (480**2 * math.log(480)) - 0.6875) < 0.001

print("\nALL CHECKS PASSED: conjecture 00000004165 REFUTED "
      "(sqrt-h remainder impossible; two regimes, neither with 4/pi^2)")
