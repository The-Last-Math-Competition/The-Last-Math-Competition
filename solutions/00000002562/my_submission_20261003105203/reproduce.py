#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000002562 (REFUTED).

Conjecture: there is an explicit matrix family (candidates:
Vandermonde, Chebyshev-type) whose rigidity R_M(r) is always
superlogarithmic in n.

Refutation: for ANY invertible M, one entry change t = -1/(M^-1)_{ji}
suffices to make it singular (matrix determinant lemma), so
R_M(n-1) = 1 -- constant, not superlogarithmic. Verified with exact
rational arithmetic for Vandermonde (n = 3..7) and Chebyshev-type
matrices.
"""

from fractions import Fraction as F

def det(M):
    n = len(M)
    A = [[F(x) for x in row] for row in M]
    d = F(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return d

def inverse(M):
    n = len(M)
    A = [[F(x) for x in row] + [F(int(i == j)) for j in range(n)]
         for i, row in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [row[n:] for row in A]

def rank_after_single_change(M, i, j):
    """min over t != 0 (exact) of rank(M + t e_i e_j^T); returns (min rank, t)."""
    n = len(M)
    best = (n, None)
    Minv = inverse(M)
    for ii in range(n):
        for jj in range(n):
            mij = Minv[jj][ii]
            if mij == 0:
                continue
            t = F(-1, 1) / mij
            M2 = [[F(x) for x in row] for row in M]
            M2[ii][jj] += t
            r = n
            d = det(M2)
            if d == 0:
                # exact rank via elimination
                A = [row[:] for row in M2]
                rank = 0
                rows, cols = n, n
                c = 0
                rr = 0
                for c in range(cols):
                    p = next((r2 for r2 in range(rr, rows) if A[r2][c] != 0), None)
                    if p is None:
                        continue
                    A[rr], A[p] = A[p], A[rr]
                    pv = A[rr][c]
                    A[rr] = [x / pv for x in A[rr]]
                    for r2 in range(rows):
                        if r2 != rr and A[r2][c] != 0:
                            f2 = A[r2][c]
                            A[r2] = [x - f2 * y for x, y in zip(A[r2], A[rr])]
                    rr += 1
                    rank += 1
                if rank < best[0]:
                    best = (rank, (ii, jj, t))
    return best

for n in range(3, 8):
    V = [[F(x ** j) for j in range(n)] for x in range(1, n + 1)]
    assert det(V) != 0
    rank, change = rank_after_single_change(V, 0, 0)
    assert rank == n - 1, (n, rank)
    # Chebyshev-type: M_ij = T_{j}(x_i) at Chebyshev nodes, T_m(x) = cos(m arccos x)
    # use the exact integer recurrence T_0=1, T_1=x, T_{k+1}=2x T_k - T_{k-1}
    xs = [F(2 * i - 1, n) for i in range(1, n + 1)]  # rational stand-ins; integrality not needed
    Cheb = []
    for x in xs:
        row, Tm1, T0 = [], F(1), x
        row.append(Tm1)
        row.append(T0)
        for k in range(2, n):
            Tm1, T0 = T0, 2 * x * T0 - Tm1
            row.append(T0)
        Cheb.append(row)
    if det(Cheb) != 0:
        rank_c, change_c = rank_after_single_change(Cheb, 0, 0)
        assert rank_c == n - 1, (n, "cheb", rank_c)
        print(f"n={n}: Vandermonde and Chebyshev-type: one entry change drops rank to {n-1} "
              f"(R_M(n-1) = 1) — OK")
    else:
        print(f"n={n}: Chebyshev stand-in singular (nodes not distinct); "
              f"Vandermonde R_M(n-1) = 1 — OK")

print("\nmatrix determinant lemma: det(M + t e_i e_j^T) = det(M)(1 + t (M^-1)_{ji});")
print("single change t = -1/(M^-1)_{ji} makes any invertible M singular:")
print("R_M(n-1) = 1 for the conjecture's own candidate families — superlog claim REFUTED")
