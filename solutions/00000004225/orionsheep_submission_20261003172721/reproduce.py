#!/usr/bin/env python3
"""
Reproduction script for the refutation of TLMC conjecture 00000004225.

Conjecture (verbatim):
  "The higher Dirichlet-Neumann operator is the boundary response operator on
   k-chains.  The multiplicity of its zero eigenvalue equals exactly the count
   of k-spanning trees of the boundary, and the multiplicity is one if and only
   if the boundary is a sphere triangulation."

Standard reading (Hodge theory): the zero eigenspace of the boundary-response /
higher DN operator on k-chains of a boundary complex B = dM is the space of
harmonic k-chains of B, hence

    mult_k(B) = dim ker Delta_k(B) = beta_k(B) = f_k - rank d_k - rank d_{k+1},

while the simplicial spanning-tree count tau_k(B) is a *determinantal* quantity
(Kalai's matrix-tree theorem: a weighted product of the NONZERO eigenvalues),
not a kernel dimension.  The identity  mult_k = tau_k  therefore fails
generically, and the "multiplicity one iff sphere" clause fails in both
directions.

Counterexamples verified below:

  (A) B = boundary of the tetrahedron, a triangulation of S^2, k = 1:
        f_1 = 6, rank d_1 = 3, rank d_2 = 3  ==>  mult_1 = 0.
        Delta_1 = 4 * I_6 (det = 4096).
        tau_1 = tau(K_4) = 16  (matrix-tree / Cayley).
        => mult_1 = 0 != 16 = tau_1          (first clause fails)
        => B is a sphere triangulation but mult != 1   (the "if" fails)

  (B) B = the 7-vertex minimal triangulation of the torus T^2
      (boundary of a solid torus), k = 2:
        f_2 = 14, rank d_2 = 13  ==>  mult_2 = beta_2(T^2) = 1.
        An explicit harmonic 2-chain c = (-1,..., -1, +1, ..., +1) and a
        nonzero 13x13 minor (det = 50421) certify nullity = 1.
        T^2 is closed, connected and chi = 0 != 2, hence not a sphere.
        Also tau_2 = 0: a simplicial 2-tree requires H_2(Q) = 0, but
        beta_2(T^2) = 1, so no 2-trees exist at all.
        => mult_2 = 1 but B is NOT a sphere   (the "only if" fails)
        => also mult_2 = 1 != 0 = tau_2        (first clause fails again)

  (C) k = 0 sanity check: the classical (scalar) DN operator on a connected
      boundary has kernel = constants, mult_0 = 1 for EVERY connected
      boundary (e.g. T^2), already contradicting "iff sphere".

Only Python stdlib + sympy are used; every rank/det/nullspace is exact.
"""

import sympy as sp
from itertools import combinations


def boundary_matrix(faces_k, faces_km1):
    """Signed incidence matrix  d_k : C_k -> C_{k-1}
    (rows = (k-1)-faces, columns = k-faces)."""
    idx = {f: i for i, f in enumerate(faces_km1)}
    B = sp.zeros(len(faces_km1), len(faces_k))
    for j, f in enumerate(faces_k):
        for i in range(len(f)):
            B[idx[f[:i] + f[i + 1:]], j] += (-1) ** i
    return B


def euler(f):
    return sum((-1) ** k * n for k, n in enumerate(f))


def main():
    print("=" * 70)
    print("(A)  B = boundary of tetrahedron (triangulated S^2),  k = 1")
    print("=" * 70)
    verts = [(i,) for i in range(4)]
    edges = [tuple(sorted(c)) for c in combinations(range(4), 2)]
    tris = [tuple(sorted(c)) for c in combinations(range(4), 3)]
    B1 = boundary_matrix(edges, verts)   # 4 x 6
    B2 = boundary_matrix(tris, edges)    # 6 x 4
    D1 = B1.T * B1 + B2 * B2.T           # Delta_1 on C_1 (6 x 6)
    print("f =", (len(verts), len(edges), len(tris)),
          " euler chi =", euler([4, 6, 4]), "  (= 2 => sphere)")
    print("rank d_1 =", B1.rank(), " rank d_2 =", B2.rank())
    print("Delta_1 =")
    for row in D1.tolist():
        print("   ", row)
    assert D1 == 4 * sp.eye(6)
    print("mult_1 = nullity Delta_1 =", 6 - B1.rank() - B2.rank())
    print("det Delta_1 =", D1.det())
    assert D1.det() != 0

    # tau_1 = spanning trees of the 1-skeleton K_4 (Kirchhoff)
    B1r = B1[:-1, :]                     # delete last vertex row
    tau1 = (B1r * B1r.T).det()
    print("tau_1 = det reduced vertex-edge Laplacian =", tau1)
    assert tau1 == 16
    # brute force check: spanning trees of K_4
    cnt = 0
    for T in combinations(range(6), 3):
        sub = B1[:, list(T)]
        # a spanning tree = 3 edges whose vertex-incidence columns span rank 3
        # on a connected 4-vertex graph: check connectedness via union-find
        p = list(range(4))
        def find(x):
            while p[x] != x:
                p[x] = p[p[x]]
                x = p[x]
            return x
        for i in T:
            a, b = edges[i]
            p[find(a)] = find(b)
        if len({find(v) for v in range(4)}) == 1:
            cnt += 1
    print("brute-force spanning-tree count of K_4 =", cnt)
    assert cnt == 16
    assert (6 - B1.rank() - B2.rank()) != tau1
    print(">> clause 1 fails:  mult_1 = 0  !=  16 = tau_1")
    print(">> 'if' fails:      sphere boundary has mult_1 = 0, not 1")

    print()
    print("=" * 70)
    print("(B)  B = 7-vertex torus T^2 (= boundary of solid torus),  k = 2")
    print("=" * 70)
    tmap = {i + 1: i for i in range(7)}
    trisT = [tuple(sorted(tmap[v] for v in t)) for t in
             [(1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 7), (5, 6, 1), (6, 7, 2),
              (7, 1, 3), (1, 2, 6), (2, 3, 7), (3, 4, 1), (4, 5, 2), (5, 6, 3),
              (6, 7, 4), (7, 1, 5)]]
    edgesT = sorted({tuple(sorted(e)) for t in trisT for e in combinations(t, 2)})
    vertsT = [(v,) for v in range(7)]
    Tb1 = boundary_matrix(edgesT, vertsT)   # 7 x 21
    Tb2 = boundary_matrix(trisT, edgesT)    # 21 x 14
    assert Tb1.rank() == 6 and Tb2.rank() == 13
    # closedness: every edge in exactly two triangles; chi = 0 => torus, not sphere
    from collections import Counter
    ec = Counter(e for t in trisT for e in combinations(t, 2))
    assert set(ec.values()) == {2}
    print("f =", (7, 21, 14), " chi =", euler([7, 21, 14]), "  (!= 2 => not S^2)")
    D2 = Tb2.T * Tb2                        # Delta_2 on C_2 (14 x 14)
    assert D2.rank() == 13
    ker = D2.nullspace()
    print("Delta_2 nullity = mult_2 =", 14 - D2.rank(), "  (beta_2(T^2) = 1)")
    assert 14 - D2.rank() == 1
    c = ker[0]
    print("harmonic 2-chain c =", list(c))
    assert (D2 * c).norm() == 0 and c.norm() != 0
    # nonzero 13x13 minor -> rank >= 13
    idx = list(range(13))
    print("13x13 principal minor det =", D2.extract(idx, idx).det())
    assert D2.extract(idx, idx).det() != 0
    # tau_2 = 0: 2-trees need H_2(Q)=0, but beta_2 = 1
    # (rank d_2 = 13 < 14 = f_2: there is an integer 2-cycle, so the up-Laplacian
    #  restricted to ANY candidate 2-tree -- a set of f_2-... columns -- is
    #  still singular: no full-rank square subsystem exists.  Numerically:
    #  Delta_2 itself is singular with nullity 1, i.e. H_2(Q) != 0, hence by
    #  Kalai's definition no simplicial 2-tree exists.)
    print("tau_2 = 0  (H_2(T^2; Q) != 0, so by Kalai's definition a 2-tree")
    print("        requires rank d_2 = f_2 = 14, but rank d_2 = 13: none exist)")
    assert Tb2.rank() < 14
    print(">> 'only if' fails:  T^2 boundary has mult_2 = 1 but is not a sphere")
    print(">> clause 1 fails again:  mult_2 = 1 != 0 = tau_2")

    print()
    print("=" * 70)
    print("(C)  k = 0 (classical scalar DN operator)")
    print("=" * 70)
    # connected boundary => ker = constants => mult_0 = 1, regardless of topology
    print("For ANY connected boundary B,  mult_0 = dim ker L_0 = 1.")
    print("T^2 boundary: mult_0 = 1 but not a sphere -- 'only if' fails;")
    print("and 'mult = tau_0' would read 1 = #vertices, e.g. 1 != 7.")

    print()
    print("ALL CHECKS PASSED -- conjecture 00000004225 is FALSE.")


if __name__ == "__main__":
    main()
