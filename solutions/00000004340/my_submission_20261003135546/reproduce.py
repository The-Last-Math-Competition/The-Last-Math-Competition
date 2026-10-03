#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000004340 (REFUTED).

Conjecture: two centrally symmetric functional measures with equal
even moments but different odd moments, realized by the
symmetry-breaking perturbation of phi^4_2.

Refutation: for ANY centrally symmetric measure the substitution
x -> -x forces every odd moment to vanish (<x^{2k+1}> = -<x^{2k+1}>),
so all symmetric measures have identical (zero) odd moments: no
separation exists. The proposed realization e^{-x^4 + x/2} is NOT
centrally symmetric (<x^3> = 1/8 ≠ 0), so it cannot serve as one of
the two measures. Verified by numerical quadrature.
"""

import numpy as np
from scipy import integrate

# ---------- gate 1: odd moments of symmetric measures vanish ----------
f_sym = lambda x: np.exp(-x**4)
Z1 = integrate.quad(f_sym, -np.inf, np.inf)[0]
for k in (1, 3, 5, 7, 9):
    m = integrate.quad(lambda x, k=k: x**k * f_sym(x), -np.inf, np.inf)[0] / Z1
    assert abs(m) < 1e-12, (k, m)
    print(f"<x^{k}> of e^(-x^4) = {m:.2e} — zero (substitution law) — OK")

# two different symmetric measures (e^{-x^4} and e^{-x^4 - x^6/2}) have identical odd moments
f_sym2 = lambda x: np.exp(-x**4 - x**6/2)
Z2 = integrate.quad(f_sym2, -np.inf, np.inf)[0]
m3a = integrate.quad(lambda x: x**3 * f_sym(x), -np.inf, np.inf)[0] / Z1
m3b = integrate.quad(lambda x: x**3 * f_sym2(x), -np.inf, np.inf)[0] / Z2
assert abs(m3a - m3b) < 1e-14
print(f"two different symmetric measures: <x^3> = {m3a:.2e} = {m3b:.2e} — odd moments identical — separation impossible — REFUTED")

# ---------- gate 2: the proposed realization is not symmetric ----------
f_asym = lambda x: np.exp(-x**4 + x/2)
Z3 = integrate.quad(f_asym, -np.inf, np.inf)[0]
m3 = integrate.quad(lambda x: x**3 * f_asym(x), -np.inf, np.inf)[0] / Z3
assert abs(m3 - 0.125) < 1e-6
print(f"<x^3> of e^(-x^4 + x/2) = {m3:.6f} = 1/8 ≠ 0: NOT centrally symmetric — cannot realize the pair — OK")

print("\nALL CHECKS PASSED: conjecture 00000004340 REFUTED "
      "(odd moments of symmetric measures all zero; proposed realization is asymmetric)")
