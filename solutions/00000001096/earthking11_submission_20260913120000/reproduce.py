#!/usr/bin/env python3
"""Reproduce the rule-3 disproof of conjecture 00000001096.

Conjecture (00000001096): over F_q, the VC dimension of degree-<= d
polynomial functions on F_q^n is exactly n*d for d < q.

Refutation: n = 2, d = 2, q = 5.  The six monomials 1, x, y, x^2, xy, y^2
of degree <= 2 in two variables have a 6x6 evaluation matrix (at the six
points below) that is invertible over F_5 (determinant == 1 mod 5).  Hence
the six points are shattered in the natural generalised (F_q-valued) VC
sense: all 5^6 labellings are realisable.  VC dim >= 6 > n*d = 4.

Standard-library only.  Prints PASS/FAIL and exits 0 on success.
"""
import itertools
import sys

Q = 5  # field characteristic

# Points p0..p5 = (0,0),(0,1),(0,2),(1,0),(1,1),(2,0)
POINTS = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)]

# Monomials of degree <= 2: 1, x, y, x^2, xy, y^2  (exponent pairs)
MONS = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]


def eval_mono(e, x, y):
    return (x ** e[0] * y ** e[1]) % Q


def eval_matrix():
    return [[eval_mono(e, x, y) for e in MONS] for (x, y) in POINTS]


def det_mod(M, p):
    """Determinant mod p, by the Leibniz formula."""
    n = len(M)
    total = 0
    for perm in itertools.permutations(range(n)):
        inv = sum(1 for i in range(n) for j in range(i + 1, n) if perm[i] > perm[j])
        sgn = -1 if inv % 2 else 1
        prod = 1
        for i in range(n):
            prod *= M[i][perm[i]]
        total += sgn * prod
    return total % p


def rank_mod(M, p):
    """Rank over F_p by Gaussian elimination."""
    A = [row[:] for row in M]
    rows, cols = len(A), len(A[0])
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i][c] % p), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c] % p, -1, p)
        A[r] = [(v * inv) % p for v in A[r]]
        for i in range(rows):
            if i != r and A[i][c] % p:
                f = A[i][c] % p
                A[i] = [(A[i][k] - f * A[r][k]) % p for k in range(cols)]
        r += 1
        if r == rows:
            break
    return r


def inverse_mod(M, p):
    """Explicit inverse of a square matrix over F_p (or None)."""
    n = len(M)
    A = [row[:] + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(M)]
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, n) if A[i][c] % p), None)
        if piv is None:
            return None
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c] % p, -1, p)
        A[r] = [(v * inv) % p for v in A[r]]
        for i in range(n):
            if i != r and A[i][c] % p:
                f = A[i][c] % p
                A[i] = [(A[i][k] - f * A[r][k]) % p for k in range(2 * n)]
        r += 1
    return [row[n:] for row in A]


def mat_vec(M, v, p):
    return [sum(M[i][j] * v[j] for j in range(len(v))) % p for i in range(len(M))]


def main():
    M = eval_matrix()
    print("Evaluation matrix over F_5 (rows = points, cols = 1,x,y,x^2,xy,y^2):")
    for row in M:
        print("  ", row)

    d = det_mod(M, Q)
    r = rank_mod(M, Q)
    print(f"\ndet(M) mod 5 = {d}")
    print(f"rank_F5(M)   = {r}")

    ok = True
    if d != 1:
        print("FAIL: determinant is not 1 mod 5")
        ok = False
    if r != 6:
        print("FAIL: rank is not 6")
        ok = False

    # Every labelling of the 6 points is realisable iff the evaluation map
    # F_5^6 -> F_5^6 is surjective, which holds iff rank = 6.  We also verify
    # this exhaustively for all 5^6 labellings using the explicit inverse.
    inv = inverse_mod(M, Q)
    if inv is None:
        print("FAIL: matrix not invertible, no explicit inverse")
        ok = False
    else:
        print("\nInverse matrix mod 5 (rows = coefficients c0..c5):")
        for row in inv:
            print("  ", row)
        # Verify M * inv == I and inv * M == I.
        I = [[1 if i == j else 0 for j in range(6)] for i in range(6)]
        if [[sum(M[i][k] * inv[k][j] for k in range(6)) % Q for j in range(6)] for i in range(6)] != I:
            print("FAIL: M*inv != I")
            ok = False

    count = 0
    for y in itertools.product(range(Q), repeat=6):
        c = mat_vec(inv, list(y), Q)
        if mat_vec(M, c, Q) != list(y):
            print(f"FAIL: labelling {y} not realised")
            ok = False
            break
        count += 1
    print(f"\nVerified all {count} = 5^6 labellings are realisable via M*c = y.")
    if count != Q ** 6:
        ok = False

    # Also confirm the five non-constant monomials (excluding 1) shatter five
    # points: drop p0 = (0,0); the 5x5 minor must be invertible.
    M5 = [[eval_mono(MONS[j], *POINTS[i]) for j in range(1, 6)] for i in range(1, 6)]
    d5 = det_mod(M5, Q)
    print(f"\nMinor on points p1..p5 and monomials x,y,x^2,xy,y^2: det = {d5} mod 5")
    if d5 == 0:
        print("FAIL: 5-point minor singular")
        ok = False

    print(f"\nn*d = 2*2 = 4, but 6 points are shattered: VC dimension >= 6.")
    print("PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
