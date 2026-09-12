#!/usr/bin/env python3
"""
Independent recomputation for the disproof of TLMC conjecture 00000001231.

Conjecture (as stated):
    |Jac(J(n,k))| = (C(n-2,k-1))^(C(n,k)-1) * prod_i (i^2-i+1)^{e_i}

We check the concrete instance J(4,1) = K_4 (and corroborate with J(4,2)):
  1. tau(K_4) = 16, computed from the Laplacian 3x3 principal minor
     (matrix-tree theorem) by exact rational Gaussian elimination.
  2. tau(J(4,2)) = 384 (octahedral graph = line graph of K_4).
  3. Leading factors: C(2,0)^(C(4,1)-1) = 1 and C(2,1)^(C(4,2)-1) = 32.
  4. Parity: i^2-i+1 is odd for every integer i (checked i = 0..100);
     hence any product of the f(i) factors is odd, while 16 is even.
  5. Therefore the conjecture's literal formula fails at (4,1).

Pure standard library; no external dependencies; no absolute paths.
Run:  python3 reproduce.py
"""

from fractions import Fraction
from itertools import combinations
from math import comb


def det_exact(M):
    """Determinant of a square integer matrix via exact fraction Gaussian elimination."""
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]
    d = Fraction(1)
    for c in range(n):
        pivot = next((r for r in range(c, n) if A[r][c] != 0), None)
        if pivot is None:
            return 0
        if pivot != c:
            A[c], A[pivot] = A[pivot], A[c]
            d = -d
        d *= A[c][c]
        inv = Fraction(1, 1) / A[c][c]
        for r in range(c + 1, n):
            factor = A[r][c] * inv
            if factor:
                for k in range(c, n):
                    A[r][k] -= factor * A[c][k]
    assert d.denominator == 1
    return int(d)


def johnson_graph(n, k):
    """Vertices are k-subsets of {0..n-1}; adjacent iff |symmetric difference| = 2."""
    verts = list(combinations(range(n), k))
    edges = [(a, b) for a, b in combinations(verts, 2)
             if len(set(a) ^ set(b)) == 2]
    return verts, edges


def laplacian(verts, edges):
    idx = {v: i for i, v in enumerate(verts)}
    L = [[0] * len(verts) for _ in verts]
    for u, v in edges:
        L[idx[u]][idx[v]] -= 1
        L[idx[v]][idx[u]] -= 1
        L[idx[u]][idx[u]] += 1
        L[idx[v]][idx[v]] += 1
    return L


def tau(verts, edges):
    """Number of spanning trees: det of the Laplacian minor (delete row 0, col 0)."""
    L = laplacian(verts, edges)
    minor = [row[1:] for row in L[1:]]
    return det_exact(minor)


def main():
    ok = True

    # --- 1. J(4,1) = K4, tau = 16 -------------------------------------------
    verts1, edges1 = johnson_graph(4, 1)
    assert len(verts1) == 4 and len(edges1) == 6, "J(4,1) should be K4"
    L1 = laplacian(verts1, edges1)
    expected_L1 = [[3, -1, -1, -1],
                   [-1, 3, -1, -1],
                   [-1, -1, 3, -1],
                   [-1, -1, -1, 3]]
    assert L1 == expected_L1, f"unexpected K4 Laplacian: {L1}"
    minor1 = [row[1:] for row in L1[1:]]
    tau_k4 = tau(verts1, edges1)
    print(f"[1] K4 Laplacian = {L1}")
    print(f"[1] 3x3 minor = {minor1}")
    print(f"[1] tau(K4) = det(minor) = {tau_k4}   (Cayley: 4^(4-2) = {4 ** 2})")
    ok &= tau_k4 == 16 == 4 ** 2

    # --- 2. J(4,2) = octahedron, tau = 384 ----------------------------------
    verts2, edges2 = johnson_graph(4, 2)
    assert len(verts2) == 6 and len(edges2) == 12, "J(4,2) should be the octahedron"
    tau_j42 = tau(verts2, edges2)
    print(f"[2] J(4,2): |V| = {len(verts2)}, |E| = {len(edges2)}, tau = {tau_j42}")
    ok &= tau_j42 == 384

    # --- 3. Leading factors of the conjecture -------------------------------
    lead_41 = comb(2, 0) ** (comb(4, 1) - 1)
    lead_42 = comb(2, 1) ** (comb(4, 2) - 1)
    print(f"[3] leading factor (4,1): C(2,0)^(C(4,1)-1) = {lead_41}")
    print(f"[3] leading factor (4,2): C(2,1)^(C(4,2)-1) = {lead_42}")
    print(f"[3] remaining factor at (4,2): 384 / 32 = {tau_j42 // lead_42}"
          f"  (even? {(tau_j42 // lead_42) % 2 == 0})")
    ok &= lead_41 == 1 and lead_42 == 32 and (tau_j42 // lead_42) % 2 == 0

    # --- 4. Parity of i^2 - i + 1 -------------------------------------------
    bad = [i for i in range(101) if (i * i - i + 1) % 2 != 1]
    print(f"[4] i^2-i+1 odd for all i in 0..100: {not bad} (violations: {bad})")
    print(f"[4] samples: " + ", ".join(
        f"i={i}: {i*i - i + 1}" for i in range(6)))
    ok &= not bad

    # --- 5. Contradiction ----------------------------------------------------
    prod_first4 = 1
    for i in range(4):
        prod_first4 *= (i * i - i + 1)
    print(f"[5] prod_(i=0..3) (i^2-i+1) = {prod_first4}, parity = {'odd' if prod_first4 % 2 else 'even'}")
    print(f"[5] 16 is even: {16 % 2 == 0}; an odd product can never equal 16.")
    ok &= prod_first4 % 2 == 1 and 16 % 2 == 0

    print()
    if ok:
        print("ALL CHECKS PASSED — conjecture 00000001231 is FALSE at (n,k) = (4,1).")
    else:
        print("SOME CHECK FAILED — do not trust the disproof; investigate.")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
