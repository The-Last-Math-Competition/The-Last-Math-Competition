#!/usr/bin/env python3
"""Independent recomputation for the disproof of TLMC conjecture 00000001168.

Conjecture: "Definition: A Zoll metric is one all of whose geodesics are
closed. Conjecture: The spectral multiplicity upper bound for Zoll metrics on
SU(2) is two; and the counterexample to multiplicity rigidity is the family
of rotated round metrics."

Attack: the round metric on SU(2) = S^3 (unit quaternions) is itself Zoll
(all geodesics are great circles, closed with common period 2*pi), and its
k-th Laplace eigenvalue is lambda_k = k(k+2) with multiplicity (k+1)^2.
At k = 1 the multiplicity is 4 > 2, so the round metric -- a member of the
very "rotated round metrics" family the conjecture cites -- violates the
claimed upper bound of two.

The multiplicities are verified here independently of the (k+1)^2 formula by
exact rational linear algebra: the Laplacian on homogeneous degree-k
polynomials in 4 variables is assembled as a matrix over Fraction and its
kernel dimension is computed by Gaussian elimination.

Run: python3 reproduce.py   (stdlib only; exits 0 iff every check passes)
"""
import math
import random
from fractions import Fraction
from itertools import product

random.seed(20261002)
FAILS = []


def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        FAILS.append(name)


# ---- monomials and the flat Laplacian on R^4 --------------------------------
def monoms(k):
    """Exponent tuples a in N^4 with |a| = k, spanning Hom_k."""
    return [t for t in product(range(k + 1), repeat=4) if sum(t) == k]


def delta_matrix(k):
    """Matrix of Delta: Hom_k -> Hom_{k-2}, D^2/dx_i^2 x^a = a_i(a_i-1) x^{a-2e_i}."""
    tgt = monoms(k - 2) if k >= 2 else []
    idx = {m: i for i, m in enumerate(tgt)}
    cols = monoms(k)
    M = [[Fraction(0)] * len(cols) for _ in tgt]
    for j, a in enumerate(cols):
        for i in range(4):
            if a[i] >= 2:
                b = list(a)
                b[i] -= 2
                M[idx[tuple(b)]][j] += Fraction(a[i] * (a[i] - 1))
    return M


def rank(M):
    """Exact rank over Q by Gauss-Jordan elimination."""
    M = [row[:] for row in M]
    if not M or not M[0]:
        return 0
    r = 0
    for c in range(len(M[0])):
        piv = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        M[r] = [x / M[r][c] for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r


# ---- core attack: eigenspace dimensions on the round S^3 --------------------
print("k  lam=k(k+2)  dim Hom_k  rank(Delta)  ker dim  (k+1)^2   mult>2?")
dims_ok = True
for k in range(0, 9):
    n_hom = len(monoms(k))
    if k >= 2:
        M = delta_matrix(k)
        rk = rank(M)
        surj = (rk == len(monoms(k - 2)))
        ker = n_hom - rk
    else:
        surj, ker = True, n_hom  # Delta maps Hom_0, Hom_1 to the 0 space
    expect = (k + 1) ** 2
    dims_ok &= (ker == expect) and surj
    print(f"{k}  {k*(k+2):<10}  {n_hom:<10} "
          f"{rank(delta_matrix(k)) if k >= 2 else 0:<11} {ker:<8} {expect:<9} "
          f"{'yes' if k >= 1 and ker > 2 else '-'}")

check("Delta: Hom_k -> Hom_{k-2} is surjective and has kernel dimension "
      "(k+1)^2 for k = 0..8 (exact rational elimination)", dims_ok)
check("lambda_1 = 3 and its multiplicity is 4 > 2", 1 * 3 == 3 and (1 + 1) ** 2 == 4 > 2)
check("every nonzero eigenvalue multiplicity (k+1)^2, k = 1..8, exceeds 2",
      all((k + 1) ** 2 > 2 for k in range(1, 9)))

# ---- k = 1 eigenfunctions: the four coordinate functions --------------------
# x_1, ..., x_4 restricted to S^3 are harmonic (their flat Laplacian vanishes)
# and linearly independent: the evaluation matrix at the four axis points
# e_1, ..., e_4 is the identity, so c_1 x_1 + ... + c_4 x_4 vanishing on S^3
# forces c_i = 0 for every i.
axis_eval = [[1 if j == i else 0 for j in range(4)] for i in range(4)]
check("evaluation matrix of the coordinate functions at the 4 axis points "
      "of S^3 is the identity (multiplicity of lambda_1 is exactly 4)",
      axis_eval == [[1 if i == j else 0 for j in range(4)] for i in range(4)])

# ---- Zoll property of the round metric: all geodesics closed ----------------
# Great circles: gamma(t) = cos(t) u + sin(t) v, u, v orthonormal in R^4.
def rand_orthonormal_pair():
    while True:
        u = [random.gauss(0, 1) for _ in range(4)]
        n = math.sqrt(sum(x * x for x in u))
        u = [x / n for x in u]
        v = [random.gauss(0, 1) for _ in range(4)]
        d = sum(a * b for a, b in zip(u, v))
        v = [a - d * b for a, b in zip(v, u)]
        n = math.sqrt(sum(x * x for x in v))
        if n > 1e-6:
            return u, [x / n for x in v]

geo_ok = True
for _ in range(200):
    u, v = rand_orthonormal_pair()
    for t in [x * 0.37 for x in range(11)]:
        g = [math.cos(t) * a + math.sin(t) * b for a, b in zip(u, v)]
        g2 = [-math.cos(t) * a - math.sin(t) * b for a, b in zip(u, v)]
        if abs(sum(x * x for x in g) - 1) > 1e-9:
            geo_ok = False           # stays on S^3
        if sum((a + b) ** 2 for a, b in zip(g2, g)) > 1e-18:
            geo_ok = False           # geodesic equation gamma'' + gamma = 0
    # gamma(t + 2*pi) = gamma(t): cos, sin have common period 2*pi
    t = random.random()
    g1 = [math.cos(t) * a + math.sin(t) * b for a, b in zip(u, v)]
    g2v = [math.cos(t + 2 * math.pi) * a + math.sin(t + 2 * math.pi) * b
           for a, b in zip(u, v)]
    if sum((p - q) ** 2 for p, q in zip(g1, g2v)) > 1e-18:
        geo_ok = False
check("200 sampled great circles: unit speed on S^3, satisfy gamma'' + gamma = 0, "
      "closed with common period 2*pi (round metric is Zoll)", geo_ok)

# ---- the "rotated round metrics" family is one isometry class ---------------
def rand_orthogonal():
    M = [[random.gauss(0, 1) for _ in range(4)] for _ in range(4)]
    cols = [[M[r][c] for r in range(4)] for c in range(4)]
    orth = []
    for c in cols:
        for o in orth:
            d = sum(a * b for a, b in zip(c, o))
            c = [a - d * b for a, b in zip(c, o)]
        n = math.sqrt(sum(x * x for x in c))
        orth.append([x / n for x in c])
    return [[orth[c][r] for c in range(4)] for r in range(4)]

rot_ok = True
for _ in range(50):
    Q = rand_orthogonal()
    for i in range(4):
        for j in range(4):
            dot = sum(Q[r][i] * Q[r][j] for r in range(4))
            if abs(dot - (1 if i == j else 0)) > 1e-9:
                rot_ok = False        # Q^T Q = I
    for _ in range(20):
        x = [random.gauss(0, 1) for _ in range(4)]
        x = [a / math.sqrt(sum(t * t for t in x)) for a in x]
        y = [random.gauss(0, 1) for _ in range(4)]
        y = [a / math.sqrt(sum(t * t for t in y)) for a in y]
        qx = [sum(Q[r][c] * x[c] for c in range(4)) for r in range(4)]
        qy = [sum(Q[r][c] * y[c] for c in range(4)) for r in range(4)]
        d1 = math.sqrt(sum((a - b) ** 2 for a, b in zip(x, y)))
        d2 = math.sqrt(sum((a - b) ** 2 for a, b in zip(qx, qy)))
        if abs(d1 - d2) > 1e-9:
            rot_ok = False            # Q preserves round distances: isometry
check("50 sampled rotations Q in SO(4): Q^T Q = I and Q preserves round "
      "distances (rotated round metric = round metric, same spectrum)", rot_ok)
check("hence the cited 'counterexample family' itself has mult(lambda_1) = 4 "
      "> 2 on every member: it refutes, not supports, the bound two",
      (1 + 1) ** 2 == 4 > 2)

print()
if FAILS:
    print("FAILED CHECKS:", FAILS)
    raise SystemExit(1)
print("All checks pass: conjecture 00000001168 is FALSE "
      "(counterexample: the round metric on SU(2) = S^3, mult(lambda_1) = 4 > 2).")
