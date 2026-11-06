"""
Verification script for conjecture 00000001559.

Definition used: r_n = min { r >= 0 : there exist n centres c_1..c_n in R^2 with
    closed unit disk D = {|p| <= 1}  subset  union_i closed disk(c_i, r) }.
(Standard covering radius of the unit disk by n equal disks; centres unrestricted.)

Claim checked: r_6 = (1+sqrt3)/2 * (sqrt3-1)  (Chinese text states equality).

Parts:
  A. Exact symbolic evaluation of the claimed expression.
  B. Exact-rational + analytic covering certificate: 4 disks of radius 1/sqrt2 at the
     corners (+-1/2, +-1/2) cover D; duplicating two of them gives 6 disks, so r_6 <= 1/sqrt2.
     Verified (i) analytically by the identity below and (ii) on a polar grid.
  C. The scanner's suggested certificate: 6 disks of radius 0.7 at 0.7*(cos 60k, sin 60k).
     Verified on a polar grid (the convexity bound is also checked numerically).
  D. Numerical upper-bound search for r_6 (random-restart pattern search), as evidence
     of the true order of magnitude; it is an upper bound only.
"""

import math
import numpy as np
import sympy as sp

print("=" * 72)
print("A. Exact value of the claimed expression")
print("=" * 72)
s3 = sp.sqrt(3)
claimed = (1 + s3) / 2 * (s3 - 1)
claimed_simpl = sp.nsimplify(sp.simplify(claimed))
print("claimed expression      :", sp.simplify(claimed))
print("expanded                :", sp.expand(claimed))
print("equals exactly 1 ?      :", sp.simplify(claimed - 1) == 0)
print("is rational (no irrational part):", claimed.is_rational)
print()

# Polar grid on the closed unit disk, including the rim and the origin.
def polar_grid(nr=600, nt=2400):
    rs = np.linspace(0.0, 1.0, nr)
    ts = np.linspace(0.0, 2 * np.pi, nt, endpoint=False)
    R, T = np.meshgrid(rs, ts)
    X = (R * np.cos(T)).ravel()
    Y = (R * np.sin(T)).ravel()
    return np.stack([X, Y], axis=1)

P = polar_grid()
# Add exact sample points on the rim and the origin.
extra = np.array([[0.0, 0.0]] + [[math.cos(t), math.sin(t)] for t in np.linspace(0, 2 * math.pi, 3601)])
P = np.vstack([P, extra])


def covering_radius_on_grid(centres, pts):
    """max over pts of distance to nearest centre (a lower bound on the true covering
    radius of this centre set, and an upper bound on the value of r_n as witnessed by
    this set when the grid is fine enough)."""
    C = np.asarray(centres, dtype=float)
    d2 = ((pts[:, None, :] - C[None, :, :]) ** 2).sum(axis=2)
    return math.sqrt(d2.min(axis=1).max())


print("=" * 72)
print("B. Certificate: corners (+-1/2,+-1/2), duplicated to six disks")
print("=" * 72)
corners = [(0.5, 0.5), (-0.5, 0.5), (-0.5, -0.5), (0.5, -0.5)]
six_B = corners + [corners[0], corners[2]]  # 6 centres, two duplicated
rB = 1 / math.sqrt(2)
mB = covering_radius_on_grid(six_B, P)
print("grid max nearest-centre distance :", mB)
print("radius used 1/sqrt2              :", rB)
print("grid covered with radius 1/sqrt2 :", mB <= rB + 1e-12)

# Analytic identity: for p=(x,y) in D, nearest corner (sign(x)/2, sign(y)/2) has
#   |p - c|^2 = x^2 + y^2 - |x| - |y| + 1/2 <= 1/2,
# because |x| <= 1 gives x^2 <= |x| (same for y), so x^2+y^2 - |x| - |y| <= 0.
# Symbolic check of the identity on a random rational sample, exactly:
import random
from fractions import Fraction
random.seed(1)
ok_identity = True
worst_exact = Fraction(0)
n_used = 0
for _ in range(20000):
    x = Fraction(random.randint(-10**6, 10**6), 10**6)
    y = Fraction(random.randint(-10**6, 10**6), 10**6)
    if x * x + y * y > 1:
        continue
    n_used += 1
    sx = Fraction(1 if x >= 0 else -1, 2)
    sy = Fraction(1 if y >= 0 else -1, 2)
    d2 = (x - sx) ** 2 + (y - sy) ** 2
    ident = x * x + y * y - abs(x) - abs(y) + Fraction(1, 2)
    if d2 != ident or d2 > Fraction(1, 2):
        ok_identity = False
    worst_exact = max(worst_exact, d2)
print("rational points in disk tested                  :", n_used)
print("exact identity d^2 = x^2+y^2-|x|-|y|+1/2 and d^2<=1/2 :", ok_identity)
print("exact max squared distance among samples        :", worst_exact, "(bound 1/2)")
print()

print("=" * 72)
print("C. Scanner's suggested certificate: six disks of radius 0.7 at hexagon of radius 0.7")
print("=" * 72)
hexC = [(0.7 * math.cos(math.radians(60 * k)), 0.7 * math.sin(math.radians(60 * k))) for k in range(6)]
mC = covering_radius_on_grid(hexC, P)
print("grid max nearest-centre distance :", mC)
print("covered with radius 0.7          :", mC <= 0.7 + 1e-12)
# Convexity bound check: for rho in [0,1], max over angles-with-delta<=30 deg is
# rho^2 - 1.2124 rho + 0.49 (convex in rho, so max at endpoints = 0.49 at rho=0)
rhos = np.linspace(0, 1, 100001)
bound = rhos ** 2 + 0.49 - 2 * 0.7 * rhos * math.cos(math.radians(30))
print("max of convex bound over rho in [0,1] :", bound.max(), "(should be 0.49)")
print()

print("=" * 72)
print("D. Numerical upper-bound search for r_6 (evidence only)")
print("=" * 72)
rng = np.random.default_rng(0)
# Coarser grid for the search, then the best configuration is re-checked on P.
G = polar_grid(nr=120, nt=480)


def objective(flat):
    C = flat.reshape(6, 2)
    d2 = ((G[:, None, :] - C[None, :, :]) ** 2).sum(axis=2).min(axis=1)
    return math.sqrt(d2.max())


best_val = float("inf")
best_C = None
for restart in range(8):
    C = rng.uniform(-0.8, 0.8, size=(6, 2)).ravel()
    val = objective(C)
    step = 0.2
    while step > 1e-4:
        improved = False
        for _ in range(60):
            cand = C + rng.normal(0, step, size=C.shape)
            v = objective(cand)
            if v < val:
                C, val = cand, v
                improved = True
        if not improved:
            step *= 0.6
    if val < best_val:
        best_val, best_C = val, C.copy()
print("best search value on coarse grid :", best_val)
print("re-check on fine grid P          :", covering_radius_on_grid(best_C.reshape(6, 2), P))
print("best centres (rounded)           :")
print(np.round(best_C.reshape(6, 2), 4))
print()

print("=" * 72)
print("VERDICT SUMMARY")
print("=" * 72)
print("claimed r_6 value                :", float(sp.N(claimed)))
print("certified upper bound r_6 <=     :", rB, "(1/sqrt2, exact certificate B)")
print("alternative upper bound          :", 0.7, "(certificate C)")
print("numerical upper bound found      :", best_val)
print("claim r_6 = 1 refuted (r_6 <= 1/sqrt2 < 1):", rB < 1)
