#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000002175.

Conjecture (as filed):

    Definition: A 3-wise odd-intersecting family is one where the intersection
    of any three members is odd.  Conjecture: The maximal size is always
    2^{n-3}; and the extremal families consist of indicator functions of
    3-dimensional affine subspaces.

The conjecture is FALSE.  This script verifies, using only the Python 3
standard library:

  * the witness at n = 4:  F = {{1,2}, {1,3}, {1,4}, {1,2,3,4}} is
    3-wise odd-intersecting (all C(4,3) = 4 triples meet in exactly {1}, of odd
    size 1), yet |F| = 4 > 2^{4-3} = 2;
  * the exact maxima M(n) for n = 0..7, computed two independent ways
    (exhaustive search over subfamilies for n <= 4, and a branch-and-bound
    maximum-independent-set search in the 3-uniform "forbidden triple"
    hypergraph for n = 5, 6, 7):
        M(n) = 1, 2, 2, 4, 5, 7, 8, 10     (n = 0..7)
    compared with the claimed 2^{n-3}.  The claim is too small at n = 3, 4, 5
    and too large at n = 7 (no family of size 16 exists), and n = 6 agrees only
    by coincidence;
  * the construction achieving the maxima at n = 3..7,
        F = {x} u G,  G = {0} u {singletons} u {edges of a matching},
    of size n + floor((n-1)/2), together with the asymptotic construction
    "all unions of pairs", of size 2^{floor((n-1)/2)} = 2^{Theta(n)};
  * the failure of the affine-subspace characterisation: no affine coset is
    extremal for n = 4..7, and under the literal reading "3-dimensional
    affine subspace" there are zero 3-wise odd-intersecting such cosets for
    n = 4, 5, 6 and 105 for n = 7, all of size 8 < M(7) = 10.

Prints PASS / FAIL and exits non-zero if any check fails.

Standard library only.  Python 3.8+.  Runtime is dominated by the n = 7
branch-and-bound search (about 10-15 seconds).
"""

from itertools import combinations
import sys


# ----------------------------------------------------------------------
# Basic utilities.  A subset of {1,...,n} is a frozenset of ints; for the
# affine part a subset is also encoded as the n-bit integer of its indicator
# vector, so that bitwise AND is intersection.
# ----------------------------------------------------------------------

def popcount(x):
    return bin(x).count("1")


def all_subsets(n):
    """All 2^n subsets of {1,...,n}, as frozensets."""
    el = list(range(1, n + 1))
    return [frozenset(c) for r in range(n + 1) for c in combinations(el, r)]


def triple_odd(a, b, c):
    """The intersection of a, b, c (frozensets) has odd size."""
    return len(a & b & c) % 2 == 1


def family_ok(F):
    """F is 3-wise odd-intersecting (all triples of distinct members are odd)."""
    return all(triple_odd(a, b, c) for a, b, c in combinations(F, 3))


# ----------------------------------------------------------------------
# Part 1.  The witness at n = 4.
# ----------------------------------------------------------------------

WITNESS = [frozenset({1, 2}), frozenset({1, 3}),
           frozenset({1, 4}), frozenset({1, 2, 3, 4})]


def check_witness():
    """Verify the n = 4 witness: four triples, each meeting in {1}."""
    rows = []
    triples = list(combinations(WITNESS, 3))
    assert len(WITNESS) == 4, "the witness must have four members"
    assert len(triples) == 4, "C(4,3) = 4 triples of distinct members"
    for a, b, c in triples:
        inter = a & b & c
        rows.append((tuple(sorted(a)), tuple(sorted(b)), tuple(sorted(c)),
                     tuple(sorted(inter)), len(inter)))
        assert inter == frozenset({1}), (
            f"triple {sorted(a)},{sorted(b)},{sorted(c)} meets in {sorted(inter)}, "
            "expected {1}")
        assert len(inter) % 2 == 1, "intersection must be odd"
    return rows


# ----------------------------------------------------------------------
# Part 2.  Exhaustive maximum for n <= 4.
# ----------------------------------------------------------------------

def max_family_exhaustive(n):
    """Exact maximum by exhaustive depth-first search over subfamilies.

    Returns (best_size, one_optimal_family).  Complete for n <= 4 (it explores
    all 2^(2^n) subfamilies, with a cardinality prune)."""
    elems = all_subsets(n)
    m = len(elems)
    best = [0]
    bestfam = [None]
    cur = []

    def rec(i):
        if len(cur) + (m - i) <= best[0]:
            return
        if i == m:
            if len(cur) > best[0]:
                best[0] = len(cur)
                bestfam[0] = list(cur)
            return
        e = elems[i]
        if all(triple_odd(e, a, b) for a, b in combinations(cur, 2)):
            cur.append(e)
            rec(i + 1)
            cur.pop()
        rec(i + 1)

    rec(0)
    return best[0], bestfam[0]


# ----------------------------------------------------------------------
# Part 3.  Branch-and-bound maximum for n = 5, 6, 7.
#
# Vertices are the 2^n subsets (encoded as ints).  A triple of distinct
# vertices is forbidden when its intersection has even size.  We want a maximum
# subset containing no forbidden triple.  For a pair (v, u) the forbidden third
# vertices are exactly those c with popcount((v & u) & c) even, so the whole
# conflict structure is precomputed from a table `evenMask`.
# ----------------------------------------------------------------------

def max_family_branch_and_bound(n):
    """Exact maximum for n = 5, 6, 7 by branch and bound.

    Returns (best_size, one_optimal_family, node_count)."""
    N = 1 << n
    full = (1 << N) - 1

    # evenMask[D] = bitmask of all c with popcount(D & c) even.
    evenMask = [0] * N
    for D in range(N):
        m = 0
        for c in range(N):
            if ((D & c).bit_count() & 1) == 0:
                m |= 1 << c
        evenMask[D] = m

    # fpair[v][u] = bitmask of c != v, u with popcount(v & u & c) even.
    fpair = [None] * N
    for v in range(N):
        row = [0] * N
        bv = 1 << v
        for u in range(N):
            if u != v:
                row[u] = evenMask[v & u] & ~bv & ~(1 << u)
        fpair[v] = row

    # Order vertices by conflict degree, descending; remap to that order.
    deg = [0] * N
    for v in range(N):
        d = 0
        for u in range(N):
            if u != v:
                d += fpair[v][u].bit_count()
        deg[v] = d
    order = sorted(range(N), key=lambda v: -deg[v])
    pos = [0] * N
    for p, v in enumerate(order):
        pos[v] = p

    FP = [[0] * N for _ in range(N)]
    nb = [0] * N
    for a in range(N):
        va = order[a]
        for b in range(N):
            if a == b:
                continue
            m = fpair[va][order[b]]
            nm = 0
            x = m
            while x:
                lb = x & -x
                nm |= 1 << pos[lb.bit_length() - 1]
                x ^= lb
            FP[a][b] = nm
            if nm:
                nb[a] |= 1 << b
    del fpair, evenMask

    # Seed a lower bound with a greedy family.
    S = 0
    x = full
    while x:
        lb = x & -x
        v = lb.bit_length() - 1
        x ^= lb
        bad = 0
        y = S
        while y:
            l2 = y & -y
            bad |= FP[v][l2.bit_length() - 1]
            y ^= l2
        S |= lb
        x &= ~bad

    best = [S.bit_count()]
    bestset = [S]
    nodes = [0]

    def rec(S, C):
        nodes[0] += 1
        sc = S.bit_count()
        nc = C.bit_count()
        if sc + nc <= best[0]:
            return
        if C == 0:
            if sc > best[0]:
                best[0] = sc
                bestset[0] = S
            return
        # Upper bound: greedy packing of vertex-disjoint forbidden triples;
        # each such triple allows at most 2 of its 3 vertices.
        used = 0
        cnt = 0
        y = C
        while y:
            lb = y & -y
            v = lb.bit_length() - 1
            y ^= lb
            if used & lb:
                continue
            rest = C & ~used & ~lb
            mm = nb[v] & rest
            yy = mm
            while yy:
                l2 = yy & -yy
                u = l2.bit_length() - 1
                yy ^= l2
                m3 = FP[v][u] & rest & ~l2
                if m3:
                    used |= lb | l2 | (m3 & -m3)
                    cnt += 1
                    break
        if sc + nc - cnt <= best[0]:
            return
        # Pivot: vertex of maximum conflict degree inside C.
        bestv = -1
        bestd = -1
        y = C
        while y:
            lb = y & -y
            v = lb.bit_length() - 1
            y ^= lb
            d = (nb[v] & C).bit_count()
            if d > bestd:
                bestd = d
                bestv = v
        v = bestv
        lbv = 1 << v
        rest = C & ~lbv
        bad = 0
        y = S
        while y:
            l2 = y & -y
            bad |= FP[v][l2.bit_length() - 1]
            y ^= l2
        inc = rest & ~bad
        if sc + 1 + inc.bit_count() > best[0]:
            rec(S | lbv, inc)
        rec(S, rest)

    rec(0, full)
    fam = []
    x = bestset[0]
    while x:
        lb = x & -x
        i = lb.bit_length() - 1
        x ^= lb
        fam.append(frozenset(j + 1 for j in range(n) if (order[i] >> j) & 1))
    return best[0], fam, nodes[0]


# ----------------------------------------------------------------------
# Part 4.  Constructions.
# ----------------------------------------------------------------------

def construction_matching(n):
    """F = {x} u G with G = {0} u {singletons} u {edges of a matching}.

    x = 1, the other points are partitioned into consecutive pairs.  This has
    n + floor((n-1)/2) members and is 3-wise odd-intersecting (a triple
    intersection is {1} u (even set), of odd size)."""
    others = list(range(2, n + 1))
    G = [frozenset()]
    G += [frozenset({p}) for p in others]
    for i in range(0, len(others) - 1, 2):
        G.append(frozenset({others[i], others[i + 1]}))
    return [frozenset({1}) | g for g in G]


def construction_all_unions_of_pairs(n):
    """F = {x} u G with G = all unions of pairs of a fixed partition of the
    other n-1 points.  This has 2^{floor((n-1)/2)} members and is 3-wise
    odd-intersecting: an intersection is {1} u (a union of pairs), of odd size.
    It shows the true order is at least 2^{n/2}, not 2^{n-3}."""
    others = list(range(2, n + 1))
    pairs = [(others[i], others[i + 1]) for i in range(0, len(others) - 1, 2)]
    G = set()
    for r in range(len(pairs) + 1):
        for combo in combinations(pairs, r):
            s = set()
            for pr in combo:
                s |= set(pr)
            G.add(frozenset(s))
    return [frozenset({1}) | g for g in G]


# ----------------------------------------------------------------------
# Part 5.  Affine cosets.
# ----------------------------------------------------------------------

def span(basis):
    """F_2-span of a list of int vectors."""
    s = {0}
    for v in basis:
        s |= {x ^ v for x in s}
    return frozenset(s)


def dim_subspaces(n, d):
    """All d-dimensional linear subspaces of F_2^n, as frozensets of ints."""
    if d == 0:
        return {frozenset({0})}
    vecs = list(range(1, 1 << n))
    subs = set()
    for basis in combinations(vecs, d):
        U = span(basis)
        if len(U) == 1 << d:          # basis is linearly independent
            subs.add(U)
    return subs


def cosets_of_dim(n, d):
    """All affine cosets of d-dimensional subspaces of F_2^n."""
    out = set()
    for U in dim_subspaces(n, d):
        for p in range(1 << n):
            out.add(frozenset(x ^ p for x in U))
    return out


def coset_is_3wise_odd(coset):
    """Test a coset (a family of ints/subset-indicators) for the property."""
    return all(popcount(a & b & c) % 2 == 1 for a, b, c in combinations(coset, 3))


# ----------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------

def main():
    checks = []
    all_ok = [True]

    def check(name, ok, detail=""):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    line = "=" * 74
    print(line)
    print("Disproof of conjecture 00000002175 -- reproduction")
    print(line)

    # ------------------------------------------------------------------
    # 1. Witness at n = 4.
    # ------------------------------------------------------------------
    print("\n[1] Witness  n = 4,  F = {{1,2}, {1,3}, {1,4}, {1,2,3,4}}")
    rows = check_witness()
    for a, b, c, inter, size in rows:
        print(f"    {a} ^ {b} ^ {c} = {inter}   (size {size}, odd)")
    check("witness: four members", len(WITNESS) == 4, f"|F| = {len(WITNESS)}")
    check("witness: all 4 triples meet in {1}, of odd size 1",
          all(sz == 1 for *_rest, sz in rows),
          f"{len(rows)} triples checked, each intersection size 1")
    check("witness: |F| = 4 > 2^{4-3} = 2",
          len(WITNESS) > 2 ** (4 - 3),
          f"|F| = {len(WITNESS)}, claimed maximum = {2 ** (4 - 3)}")
    check("witness: F is 3-wise odd-intersecting", family_ok(WITNESS))
    print(f"    => |F| = {len(WITNESS)} > 2 = 2^(4-3): the size claim fails at n = 4.")

    # ------------------------------------------------------------------
    # 2. Exact maxima.
    # ------------------------------------------------------------------
    M = {}
    print("\n[2a] Exhaustive maximum over all subfamilies (n = 0..4)")
    for n in range(0, 5):
        size, fam = max_family_exhaustive(n)
        M[n] = size
        print(f"     n = {n}: M(n) = {size}   "
              f"example = {sorted(sorted(s) for s in fam)}")
    assert M[0] == 1 and M[1] == 2 and M[2] == 2 and M[3] == 4 and M[4] == 5
    check("exhaustive maxima n = 0..4 equal 1, 2, 2, 4, 5",
          [M[n] for n in range(5)] == [1, 2, 2, 4, 5],
          f"got {[M[n] for n in range(5)]}")

    print("\n[2b] Branch-and-bound maximum (n = 5, 6, 7)")
    for n in (5, 6, 7):
        size, fam, nodes = max_family_branch_and_bound(n)
        M[n] = size
        print(f"     n = {n}: M(n) = {size}   (nodes {nodes})")
    check("branch-and-bound maxima n = 5, 6, 7 equal 7, 8, 10",
          [M[5], M[6], M[7]] == [7, 8, 10],
          f"got {[M[5], M[6], M[7]]}")

    # Cross-check the two methods where they overlap (n = 4).
    M_cross, _ = max_family_exhaustive(4)
    M_bb, _, _ = max_family_branch_and_bound(4)
    check("methods agree at n = 4 (exhaustive = branch-and-bound = 5)",
          M_cross == 5 and M_bb == 5, f"{M_cross} = {M_bb} = 5")

    # ------------------------------------------------------------------
    # 3. Table: true maxima versus 2^{n-3}.
    # ------------------------------------------------------------------
    print("\n[3] True maxima M(n) versus the claim 2^(n-3)")
    print(f"    {'n':>2}  {'M(n)':>5}  {'2^(n-3)':>8}  comparison")
    too_small, too_large, match = [], [], []
    for n in range(0, 8):
        claim = 2 ** (n - 3) if n >= 3 else None
        if claim is None:
            comp = "(claim undefined for n < 3)"
        elif M[n] > claim:
            comp = f"M(n) > claim  (+{M[n] - claim})"
            too_small.append(n)
        elif M[n] < claim:
            comp = f"M(n) < claim  (-{claim - M[n]})"
            too_large.append(n)
        else:
            comp = "equal (coincidence)"
            match.append(n)
        if claim is None:
            print(f"    {n:>2}  {M[n]:>5}  {'-':>8}  {comp}")
        else:
            print(f"    {n:>2}  {M[n]:>5}  {claim:>8}  {comp}")
    check("the claim 2^(n-3) is too small at n = 3, 4, 5",
          too_small == [3, 4, 5], f"too small at n = {too_small}")
    check("the claim 2^(n-3) is too large at n = 7 (no size-16 family exists)",
          too_large == [7], f"too large at n = {too_large}")
    check("n = 6 matches only by coincidence", match == [6], f"matches at n = {match}")

    # ------------------------------------------------------------------
    # 4. Constructions.
    # ------------------------------------------------------------------
    print("\n[4a] Construction  F = {{x}} u G,  G = {{0}} u singletons u matching")
    for n in range(3, 8):
        F = construction_matching(n)
        expected = n + (n - 1) // 2
        ok = family_ok(F) and len(F) == expected
        print(f"     n = {n}: |F| = {len(F)} = n + floor((n-1)/2) = {expected}, "
              f"3-wise odd = {family_ok(F)}, equals M(n) = {M[n]} = {len(F) == M[n]}")
        check(f"matching construction for n = {n} is valid and optimal",
              ok and len(F) == M[n],
              f"|F| = {len(F)}, M(n) = {M[n]}")

    print("\n[4b] Asymptotic construction  G = all unions of pairs")
    for n in range(3, 10):
        F = construction_all_unions_of_pairs(n)
        expected = 2 ** ((n - 1) // 2)
        print(f"     n = {n}: |F| = {len(F)} = 2^floor((n-1)/2) = {expected}, "
              f"3-wise odd = {family_ok(F)}")
        check(f"all-unions-of-pairs construction for n = {n} is valid of size "
              f"2^floor((n-1)/2)", family_ok(F) and len(F) == expected,
              f"|F| = {len(F)}, expected {expected}")
    check("the pairs construction is an infinite valid family of size "
          "2^floor((n-1)/2), i.e. M(n) grows at least like 2^{n/2} -- a "
          "different exponential rate from the claimed 2^{n-3}",
          all(len(construction_all_unions_of_pairs(n)) == 2 ** ((n - 1) // 2)
              for n in range(3, 12)),
          "verified for n = 3..11; the lower bound is 2^{n/2}, whereas the "
          "claim asserts 2^{n-3}")

    # ------------------------------------------------------------------
    # 5. Failure of the affine-subspace characterisation.
    # ------------------------------------------------------------------
    print("\n[5a] Literal reading: 3-dimensional affine subspaces (2^3 = 8 points)")
    good_3dim = {}
    for n in (4, 5, 6, 7):
        cs = cosets_of_dim(n, 3)
        good = [c for c in cs if coset_is_3wise_odd(c)]
        good_3dim[n] = len(good)
        print(f"     n = {n}: {len(dim_subspaces(n, 3))} subspaces, "
              f"{len(cs)} cosets, {len(good)} that are 3-wise odd")
    check("literal reading: zero 3-dim affine cosets are 3-wise odd for n = 4, 5, 6",
          good_3dim[4] == 0 and good_3dim[5] == 0 and good_3dim[6] == 0,
          f"counts = {[good_3dim[n] for n in (4, 5, 6)]}")
    check("literal reading: for n = 7 exactly 105 are 3-wise odd, all of size "
          "8 < M(7) = 10, hence none is extremal",
          good_3dim[7] == 105 and 8 < M[7],
          f"count = {good_3dim[7]}, coset size 8 < M(7) = {M[7]}")

    print("\n[5b] Codimension-3 reading: cosets of size 2^(n-3)")
    for n in (4, 5, 6):
        d = n - 3
        cs = cosets_of_dim(n, d)
        good = [c for c in cs if coset_is_3wise_odd(c)]
        size = 2 ** d
        print(f"     n = {n}: d = {d}, {len(cs)} cosets of size {size}, "
              f"{len(good)} 3-wise odd, size {size} vs M(n) = {M[n]} "
              f"({'extremal' if size == M[n] and good else 'not extremal'})")
    check("codimension-3 reading: for n = 4, 5 the cosets are too small "
          "(2 < 5 and 4 < 7) and for n = 6 none is 3-wise odd",
          2 < M[4] and 4 < M[5] and good_3dim[6] == 0,
          "no codimension-3 coset is extremal")
    check("codimension-3 reading for n = 7 predicts a size-16 family, "
          "impossible since M(7) = 10 < 16",
          M[7] < 2 ** (7 - 3),
          f"M(7) = {M[7]} < 16 = 2^(7-3)")

    print("\n[5c] No affine coset is extremal (n = 4..7)")
    for n in range(4, 8):
        Mn = M[n]
        d = Mn.bit_length() - 1
        if (1 << d) != Mn:
            print(f"     n = {n}: M(n) = {Mn} is not a power of two; no coset "
                  f"(all of power-of-two size) has size M(n) -> none extremal")
            check(f"n = {n}: no affine coset is extremal (M(n) not a power of 2)",
                  True)
        else:
            cs = cosets_of_dim(n, d)
            good = [c for c in cs if coset_is_3wise_odd(c)]
            print(f"     n = {n}: M(n) = {Mn} = 2^{d}; {len(cs)} cosets of size "
                  f"{Mn}, of which {len(good)} are 3-wise odd -> "
                  f"{'none extremal' if not good else 'EXTREMAL FOUND'}")
            check(f"n = {n}: no size-{Mn} affine coset is 3-wise odd, so none "
                  f"is extremal", len(good) == 0, f"{len(good)} found")

    # ------------------------------------------------------------------
    # Report.
    # ------------------------------------------------------------------
    print("\n[6] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        if detail:
            print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000002175 is FALSE.")
        print("  n = 4 witness: |F| = 4 > 2 = 2^(4-3) with every triple meeting")
        print("  in {1}; true maxima M = [1,2,2,4,5,7,8,10] for n = 0..7;")
        print("  no affine coset is an extremal family.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
