#!/usr/bin/env python3
"""
Reproduction script for the refutation of conjecture 00000002604.

Conjecture (natural reading): two finite distributive lattices with the same
"layer-count vector" are isomorphic.  Via Birkhoff's theorem a finite distributive
lattice is J(P), the lattice of order ideals of a finite poset P; the layer-count
vector is the rank-size vector of J(P), i.e. the numbers of order ideals of P of
each cardinality.  We refute the conjecture by exhibiting non-isomorphic posets
P, Q with equal ideal-count vectors.

The script:
  1. computes the ideal-count vectors of the specific posets A, B (n = 5) and
     P, Q (n = 4), confirming the two pairs of equalities;
  2. verifies non-isomorphism of each pair by brute force over all bijections;
  3. exhaustively enumerates all posets on n <= 4 elements, confirming that no
     non-isomorphic collision exists for n <= 3 and that n = 4 is minimal
     (a collision exists there).

stdlib only.  Prints PASS/FAIL and exits 0 on success, 1 on failure.
"""

from itertools import permutations, product

# --------------------------------------------------------------------------
# Posets as boolean matrices (relation is reflexive, transitive, antisymmetric)
# --------------------------------------------------------------------------


def transpose_ok(rel, n):
    for a in range(n):
        for b in range(n):
            if rel[a][b] and rel[b][a] and a != b:
                return False
    return True


def transitive(rel, n):
    for a in range(n):
        for b in range(n):
            if not rel[a][b]:
                continue
            for c in range(n):
                if rel[b][c] and not rel[a][c]:
                    return False
    return True


def is_poset(rel, n):
    for i in range(n):
        if not rel[i][i]:
            return False
    return transitive(rel, n) and transpose_ok(rel, n)


def from_edges(n, edges, reflexive=True):
    """Reflexive-transitive closure of a strict edge list."""
    rel = [[False] * n for _ in range(n)]
    if reflexive:
        for i in range(n):
            rel[i][i] = True
    for a, b in edges:
        rel[a][b] = True
    # Floyd-Warshall transitive closure
    for k in range(n):
        for i in range(n):
            if rel[i][k]:
                for j in range(n):
                    if rel[k][j]:
                        rel[i][j] = True
    return rel


def down_closed(rel, mask, n):
    """Bitmask subset is an order ideal (down-closed)."""
    for x in range(n):
        if not (mask >> x) & 1:
            continue
        for y in range(n):
            if rel[y][x] and not (mask >> y) & 1:
                return False
    return True


def ideal_count_vector(rel, n):
    """Number of down-closed subsets of each cardinality 0..n."""
    vec = [0] * (n + 1)
    for mask in range(1 << n):
        if down_closed(rel, mask, n):
            vec[bin(mask).count("1")] += 1
    return tuple(vec)


def is_isomorphic(rel1, rel2, n):
    """True iff some bijection is an order isomorphism (rel1 a b <=> rel2 s(a) s(b))."""
    for perm in permutations(range(n)):
        ok = True
        for a in range(n):
            for b in range(n):
                if rel1[a][b] != rel2[perm[a]][perm[b]]:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False


def all_posets(n):
    """All labeled posets on {0..n-1} as boolean matrices."""
    off = [(i, j) for i in range(n) for j in range(n) if i != j]
    result = []
    for bits in product((False, True), repeat=len(off)):
        rel = [[False] * n for _ in range(n)]
        for i in range(n):
            rel[i][i] = True
        for (i, j), bit in zip(off, bits):
            if bit:
                rel[i][j] = True
        if is_poset(rel, n):
            result.append(rel)
    return result


# --------------------------------------------------------------------------
# Specific counterexamples
# --------------------------------------------------------------------------

# n = 5, poset A: 0<1, 0<2, 0<3, 1<3, 2<3, 4 isolated.
A = from_edges(5, [(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)])
# n = 5, poset B: 1<2, 2<3, 0<4.
B = from_edges(5, [(1, 2), (2, 3), (0, 4)])

# n = 4, poset P: 0<1<2, 3 isolated.
P = from_edges(4, [(0, 1), (1, 2)])
# n = 4, poset Q: 0<2, 0<3, 1<2.
Q = from_edges(4, [(0, 2), (0, 3), (1, 2)])

EXPECTED_A = (1, 2, 3, 3, 2, 1)
EXPECTED_B = (1, 2, 3, 3, 2, 1)
EXPECTED_P = (1, 2, 2, 2, 1)
EXPECTED_Q = (1, 2, 2, 2, 1)


def main():
    ok = True

    va = ideal_count_vector(A, 5)
    vb = ideal_count_vector(B, 5)
    vp = ideal_count_vector(P, 4)
    vq = ideal_count_vector(Q, 4)

    print("Specific counterexamples")
    print(f"  n=5  A vector = {va}")
    print(f"  n=5  B vector = {vb}")
    print(f"  n=4  P vector = {vp}")
    print(f"  n=4  Q vector = {vq}")

    checks = [
        ("A vector equals (1,2,3,3,2,1)", va == EXPECTED_A),
        ("B vector equals (1,2,3,3,2,1)", vb == EXPECTED_B),
        ("A and B have equal vectors", va == vb),
        ("P vector equals (1,2,2,2,1)", vp == EXPECTED_P),
        ("Q vector equals (1,2,2,2,1)", vq == EXPECTED_Q),
        ("P and Q have equal vectors", vp == vq),
        ("A is not isomorphic to B (all 5! = 120 bijections)", not is_isomorphic(A, B, 5)),
        ("P is not isomorphic to Q (all 4! = 24 bijections)", not is_isomorphic(P, Q, 4)),
    ]
    for name, passed in checks:
        print(f"  [{'PASS' if passed else 'FAIL'}] {name}")
        ok = ok and passed

    # ----------------------------------------------------------------------
    # Exhaustive minimality search over all labeled posets on n <= 4
    # ----------------------------------------------------------------------
    print("\nExhaustive search over all labeled posets on n <= 4")
    min_collision_n = None
    for n in range(1, 5):
        posets = all_posets(n)
        # group by ideal-count vector
        groups = {}
        for rel in posets:
            groups.setdefault(ideal_count_vector(rel, n), []).append(rel)
        collisions = 0
        for vec, members in groups.items():
            if len(members) < 2:
                continue
            for i in range(len(members)):
                for j in range(i + 1, len(members)):
                    if not is_isomorphic(members[i], members[j], n):
                        collisions += 1
        print(
            f"  n={n}: {len(posets)} labeled posets, "
            f"{len(groups)} distinct vectors, {collisions} non-isomorphic colliding pair(s)"
        )
        if collisions > 0 and min_collision_n is None:
            min_collision_n = n
        if n <= 3:
            no_collision = collisions == 0
            print(f"    [{'PASS' if no_collision else 'FAIL'}] no non-isomorphic collision at n={n}")
            ok = ok and no_collision

    n4_ok = min_collision_n == 4
    print(f"    [{'PASS' if n4_ok else 'FAIL'}] n=4 is the minimal size with a collision")
    ok = ok and n4_ok

    print("\n" + ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
