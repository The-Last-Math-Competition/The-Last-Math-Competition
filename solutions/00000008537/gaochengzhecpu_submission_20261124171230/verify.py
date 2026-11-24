#!/usr/bin/env python3
"""Independent finite-model verification for Conjecture 00000008537 (Disproof).

Constructs the subspace lattices Sub(F_2^3) (16 elements) and Sub(F_3^3) (28 elements)
directly from vector-subspace closure over F_2^3 and F_3^3, glues them along
1_{Sub(F_2^3)} = 0_{Sub(F_3^3)} to obtain the 43-element lattice L_43, exhaustively
verifies all 43^3 = 79,507 modular-law triples, verifies the characteristic-2 and
characteristic-3 forcing lattice configurations, and checks initial members of the
infinite non-isomorphic family L^(m) = L_43 x C_{m+1}.
"""

from __future__ import annotations

import itertools
from typing import FrozenSet, List, Tuple

Vec = Tuple[int, int, int]
Subspace = FrozenSet[Vec]


def span_fp3(generators: List[Vec], p: int) -> Subspace:
    """Return the F_p-linear span of `generators` inside F_p^3."""
    zero: Vec = (0, 0, 0)
    if not generators:
        return frozenset([zero])
    basis: List[Vec] = []
    current = {zero}
    for g in generators:
        if g not in current:
            basis.append(g)
            new_set = set()
            for u in current:
                for c in range(p):
                    new_set.add(
                        (
                            (u[0] + c * g[0]) % p,
                            (u[1] + c * g[1]) % p,
                            (u[2] + c * g[2]) % p,
                        )
                    )
            current = new_set
    return frozenset(current)


def all_subspaces_fp3(p: int) -> List[Subspace]:
    """Enumerate all F_p-linear subspaces of F_p^3."""
    all_vecs: List[Vec] = list(itertools.product(range(p), repeat=3))
    zero: Subspace = frozenset([(0, 0, 0)])
    full: Subspace = frozenset(all_vecs)
    lines = {span_fp3([v], p) for v in all_vecs if v != (0, 0, 0)}
    planes = set()
    for u, v in itertools.combinations(all_vecs, 2):
        s = span_fp3([u, v], p)
        if len(s) == p * p:
            planes.add(s)
    subspaces = [zero] + sorted(lines, key=sorted) + sorted(planes, key=sorted) + [full]
    return subspaces


def sub_join(u: Subspace, w: Subspace, p: int) -> Subspace:
    """Minkowski sum U + W of two subspaces of F_p^3."""
    return frozenset(
        ((a[0] + b[0]) % p, (a[1] + b[1]) % p, (a[2] + b[2]) % p)
        for a in u
        for b in w
    )


def verify_modular_lattice(
    elements: List[int],
    le_mat: List[List[bool]],
    meet_mat: List[List[int]],
    join_mat: List[List[int]],
    name: str,
) -> None:
    """Exhaustively check poset, lattice, Dedekind modular, and dual modular laws."""
    n = len(elements)
    for x in range(n):
        assert le_mat[x][x], f"{name}: reflexivity failed at {x}"
        assert meet_mat[x][x] == x, f"{name}: meet idempotence failed at {x}"
        assert join_mat[x][x] == x, f"{name}: join idempotence failed at {x}"

    for x in range(n):
        for y in range(n):
            if le_mat[x][y] and le_mat[y][x]:
                assert x == y, f"{name}: antisymmetry failed at ({x}, {y})"
            m = meet_mat[x][y]
            j = join_mat[x][y]
            assert m == meet_mat[y][x], f"{name}: meet commutativity failed"
            assert j == join_mat[y][x], f"{name}: join commutativity failed"
            assert le_mat[m][x] and le_mat[m][y], f"{name}: meet lower bound failed"
            assert le_mat[x][j] and le_mat[y][j], f"{name}: join upper bound failed"
            assert join_mat[x][m] == x, f"{name}: absorption 1 failed"
            assert meet_mat[x][j] == x, f"{name}: absorption 2 failed"
            assert le_mat[x][y] == (m == x), f"{name}: order-meet consistency failed"

    modular_checked = 0
    for x in range(n):
        for y in range(n):
            for z in range(n):
                if le_mat[x][y] and le_mat[y][z]:
                    assert le_mat[x][z], f"{name}: transitivity failed"
                if le_mat[z][x] and le_mat[z][y]:
                    assert le_mat[z][meet_mat[x][y]], f"{name}: greatest lower bound failed"
                if le_mat[x][z] and le_mat[y][z]:
                    assert le_mat[join_mat[x][y]][z], f"{name}: least upper bound failed"
                assert (
                    meet_mat[meet_mat[x][y]][z] == meet_mat[x][meet_mat[y][z]]
                ), f"{name}: meet associativity failed"
                assert (
                    join_mat[join_mat[x][y]][z] == join_mat[x][join_mat[y][z]]
                ), f"{name}: join associativity failed"
                # Dedekind modular law: z <= x -> x ^ (y v z) = (x ^ y) v z
                if le_mat[z][x]:
                    lhs = meet_mat[x][join_mat[y][z]]
                    rhs = join_mat[meet_mat[x][y]][z]
                    assert lhs == rhs, f"{name}: modular law failed at ({x}, {y}, {z})"
                    modular_checked += 1
                # Dual modular law: x <= z -> x v (y ^ z) = (x v y) ^ z
                if le_mat[x][z]:
                    lhs_d = join_mat[x][meet_mat[y][z]]
                    rhs_d = meet_mat[join_mat[x][y]][z]
                    assert lhs_d == rhs_d, f"{name}: dual modular law failed at ({x}, {y}, {z})"

    print(
        f"[OK] {name}: |L| = {n}, all {n}^3 = {n**3:,} triples verified "
        f"({modular_checked:,} comparable modular pairs)."
    )


def build_subspace_tables(subspaces: List[Subspace], p: int):
    idx = {s: i for i, s in enumerate(subspaces)}
    n = len(subspaces)
    le_mat = [[subspaces[i].issubset(subspaces[j]) for j in range(n)] for i in range(n)]
    meet_mat = [[idx[subspaces[i] & subspaces[j]] for j in range(n)] for i in range(n)]
    join_mat = [[idx[sub_join(subspaces[i], subspaces[j], p)] for j in range(n)] for i in range(n)]
    return idx, le_mat, meet_mat, join_mat


def verify_char_configurations(sub2: List[Subspace], sub3: List[Subspace]) -> None:
    """Verify the exact lattice identities used in Theorems 4.2 and 4.3."""
    # Characteristic-2 Fano configuration in Sub(F_2^3)
    bot2 = span_fp3([], 2)
    s1 = span_fp3([(1, 0, 0)], 2)
    s2 = span_fp3([(0, 1, 0)], 2)
    s3 = span_fp3([(0, 0, 1)], 2)
    sd = span_fp3([(1, 1, 1)], 2)
    s12 = span_fp3([(1, 1, 0)], 2)
    s13 = span_fp3([(1, 0, 1)], 2)
    s23 = span_fp3([(0, 1, 1)], 2)

    assert not s1.issubset(bot2)
    assert (s1 & sub_join(s2, s3, 2)) == bot2
    assert (s2 & sub_join(s1, s3, 2)) == bot2
    assert (s3 & sub_join(s1, s2, 2)) == bot2
    assert (sd & sub_join(s2, s3, 2)) == bot2
    assert (sd & sub_join(s1, s3, 2)) == bot2
    assert (sd & sub_join(s1, s2, 2)) == bot2
    assert s1.issubset(sub_join(sd, sub_join(s2, s3, 2), 2))
    assert (sub_join(s1, s2, 2) & sub_join(s3, sd, 2)) == s12
    assert (sub_join(s1, s3, 2) & sub_join(s2, sd, 2)) == s13
    assert (sub_join(s2, s3, 2) & sub_join(s1, sd, 2)) == s23
    # Characteristic-2 collinearity: s23 <= s12 v s13
    assert s23.issubset(sub_join(s12, s13, 2))
    print("[OK] Sub(F_2^3): all 12 Fano characteristic-2 forcing identities verified.")

    # Characteristic-3 configuration in Sub(F_3^3)
    bot3 = span_fp3([], 3)
    t1 = span_fp3([(1, 0, 0)], 3)
    t2 = span_fp3([(0, 1, 0)], 3)
    t3 = span_fp3([(0, 0, 1)], 3)
    td = span_fp3([(1, 1, 1)], 3)
    t12 = span_fp3([(1, 1, 0)], 3)
    t13 = span_fp3([(1, 0, 1)], 3)
    t23 = span_fp3([(0, 1, 1)], 3)
    tc = span_fp3([(1, 2, 0)], 3)
    tdp = span_fp3([(1, 2, 1)], 3)

    assert not t1.issubset(bot3)
    assert (t1 & sub_join(t2, t3, 3)) == bot3
    assert (t2 & sub_join(t1, t3, 3)) == bot3
    assert (t3 & sub_join(t1, t2, 3)) == bot3
    assert (td & sub_join(t2, t3, 3)) == bot3
    assert (td & sub_join(t1, t3, 3)) == bot3
    assert (td & sub_join(t1, t2, 3)) == bot3
    assert t1.issubset(sub_join(td, sub_join(t2, t3, 3), 3))
    assert (sub_join(t1, t2, 3) & sub_join(t3, td, 3)) == t12
    assert (sub_join(t1, t3, 3) & sub_join(t2, td, 3)) == t13
    assert (sub_join(t2, t3, 3) & sub_join(t1, td, 3)) == t23
    assert (sub_join(t13, t23, 3) & sub_join(t1, t2, 3)) == tc
    assert (sub_join(tc, t3, 3) & sub_join(t13, t2, 3)) == tdp
    # Characteristic-3 failure of Fano collinearity & satisfaction of ternary collinearity:
    assert not t23.issubset(sub_join(t12, t13, 3))
    assert t12.issubset(sub_join(tdp, t23, 3))
    print("[OK] Sub(F_3^3): all 15 ternary characteristic-3 forcing identities verified.")


def main() -> None:
    print("=== Independent Finite-Model Verification for Conjecture 00000008537 ===")

    sub2 = all_subspaces_fp3(2)
    sub3 = all_subspaces_fp3(3)
    assert len(sub2) == 16, f"Expected 16 subspaces of F_2^3, got {len(sub2)}"
    assert len(sub3) == 28, f"Expected 28 subspaces of F_3^3, got {len(sub3)}"

    counts2 = [sum(1 for s in sub2 if len(s) == 2**k) for k in range(4)]
    counts3 = [sum(1 for s in sub3 if len(s) == 3**k) for k in range(4)]
    assert counts2 == [1, 7, 7, 1], f"Unexpected rank counts in F_2^3: {counts2}"
    assert counts3 == [1, 13, 13, 1], f"Unexpected rank counts in F_3^3: {counts3}"
    print(f"[OK] Sub(F_2^3) rank profile {counts2} (total 16); Sub(F_3^3) rank profile {counts3} (total 28).")

    _, le2, meet2, join2 = build_subspace_tables(sub2, 2)
    _, le3, meet3, join3 = build_subspace_tables(sub3, 3)
    verify_modular_lattice(list(range(16)), le2, meet2, join2, "Sub(F_2^3)")
    verify_modular_lattice(list(range(28)), le3, meet3, join3, "Sub(F_3^3)")

    verify_char_configurations(sub2, sub3)

    # Glued 43-element lattice L_43 <= Sub(F_2^3) x Sub(F_3^3): y == 0 or x == 15
    top2 = 15
    bot3 = 0
    l43_pairs: List[Tuple[int, int]] = [
        (x, y) for x in range(16) for y in range(28) if (y == bot3 or x == top2)
    ]
    assert len(l43_pairs) == 43, f"Expected |L_43| = 43, got {len(l43_pairs)}"
    pair_idx = {pair: i for i, pair in enumerate(l43_pairs)}

    le43 = [
        [le2[x1][x2] and le3[y1][y2] for (x2, y2) in l43_pairs]
        for (x1, y1) in l43_pairs
    ]
    meet43 = []
    join43 = []
    for x1, y1 in l43_pairs:
        m_row = []
        j_row = []
        for x2, y2 in l43_pairs:
            mp = (meet2[x1][x2], meet3[y1][y2])
            jp = (join2[x1][x2], join3[y1][y2])
            assert mp in pair_idx, f"L_43 not closed under meet at {(x1, y1)}, {(x2, y2)}"
            assert jp in pair_idx, f"L_43 not closed under join at {(x1, y1)}, {(x2, y2)}"
            m_row.append(pair_idx[mp])
            j_row.append(pair_idx[jp])
        meet43.append(m_row)
        join43.append(j_row)

    verify_modular_lattice(list(range(43)), le43, meet43, join43, "CounterexampleLattice L_43")

    # Verify embeddings Sub(F_2^3) -> L_43 and Sub(F_3^3) -> L_43
    iota2 = [pair_idx[(x, bot3)] for x in range(16)]
    iota3 = [pair_idx[(top2, y)] for y in range(28)]
    assert len(set(iota2)) == 16 and len(set(iota3)) == 28
    for a in range(16):
        for b in range(16):
            assert meet43[iota2[a]][iota2[b]] == iota2[meet2[a][b]]
            assert join43[iota2[a]][iota2[b]] == iota2[join2[a][b]]
    for a in range(28):
        for b in range(28):
            assert meet43[iota3[a]][iota3[b]] == iota3[meet3[a][b]]
            assert join43[iota3[a]][iota3[b]] == iota3[join3[a][b]]
    print("[OK] Lattice embeddings Sub(F_2^3) -> L_43 and Sub(F_3^3) -> L_43 verified.")

    # Verify initial members L^(1) (size 86) of infinite family L_43 x C_{m+1}
    m = 1
    fam_elems = [(i, c) for i in range(43) for c in range(m + 1)]
    fam_idx = {p: idx for idx, p in enumerate(fam_elems)}
    le_fam = [
        [le43[i1][i2] and (c1 <= c2) for (i2, c2) in fam_elems]
        for (i1, c1) in fam_elems
    ]
    meet_fam = [
        [fam_idx[(meet43[i1][i2], min(c1, c2))] for (i2, c2) in fam_elems]
        for (i1, c1) in fam_elems
    ]
    join_fam = [
        [fam_idx[(join43[i1][i2], max(c1, c2))] for (i2, c2) in fam_elems]
        for (i1, c1) in fam_elems
    ]
    verify_modular_lattice(
        list(range(len(fam_elems))), le_fam, meet_fam, join_fam, "Family member L^(1) = L_43 x C_2"
    )

    print("=== ALL FINITE-MODEL CHECKS PASSED ===")


if __name__ == "__main__":
    main()
