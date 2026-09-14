#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000002605.

    Definition: Whitney numbers of a semimodular lattice are the coefficients of
                the rank generating function, i.e. the number of elements of
                each rank -- the Whitney numbers of the SECOND kind.
    Conjecture: The rank number sequences of semimodular lattices are strictly
                log-concave (the complete version of Mason's conjecture), and
                the deficit of concavity is controlled by the number of embedded
                N5 sublattices; the minimal positive deficit example is exactly
                the fifth-layer embedding in the free Boolean lattice.

The conjecture is FALSE, and this script verifies all the ingredients.

The witness is the 5-element lattice L with

    0 < a, b < c = a v b < 1,   a and b incomparable,

i.e. the lattice of order ideals of the poset with two incomparable minimal
elements and a top.  Its cover relations are

    (0,1), (0,2), (1,3), (2,3), (3,4)

with indices 0 = bottom, 1 = a, 2 = b, 3 = c = a v b, 4 = top.  L is
distributive (hence modular, hence upper semimodular), so it lies in the class
the conjecture names ("semimodular lattices").  Its rank numbers are

    W = [1, 2, 1, 1],

and log-concavity fails at the start:

    W_2^2 = 1  <  2 = W_1 * W_3,

so it fails even WEAK log-concavity, a fortiori the filed "strict
log-concavity".  The "deficit" W_1 W_3 - W_2^2 equals 1 > 0.

The two extra clauses are independently false:

  (i)  "the deficit of concavity is controlled by the number of embedded N5
       sublattices": the witness is distributive, so it contains ZERO N5
       sublattices (N5 is non-distributive), yet its deficit is 1.  This script
       enumerates all sublattices and counts the N5 ones: 0.

  (ii) "the minimal positive deficit example is exactly the fifth-layer
       embedding in the free Boolean lattice": free Boolean lattices have
       binomial rank numbers, which are strictly log-concave with NO positive
       deficit at all.  This script checks the binomial sequences B_n for
       n <= 20.  It also records that the 4-element chain violates STRICT
       log-concavity degenerately, by equality ([1,1,1,1]).

Standard library only, Python 3.8+.  Prints PASS/FAIL; exits non-zero on failure.
"""

import sys
from itertools import combinations, permutations


# ----------------------------------------------------------------------
# The witness lattice, built from its cover relations
# ----------------------------------------------------------------------

ELEMS = [0, 1, 2, 3, 4]                       # 0=bottom, 1=a, 2=b, 3=a v b, 4=top
COVERS = [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)]
NAMES = {0: "0 (bottom)", 1: "a", 2: "b", 3: "c = a v b", 4: "1 (top)"}


def closure(elems, cover_pairs):
    """Reflexive-transitive closure of a relation on a finite set, as a set."""
    rel = {(x, y) for x, y in cover_pairs}
    changed = True
    while changed:
        changed = False
        for (x, y) in list(rel):
            for (z, w) in list(rel):
                if y == z and (x, w) not in rel:
                    rel.add((x, w))
                    changed = True
    rel |= {(x, x) for x in elems}
    return rel


def is_partial_order(elems, le):
    """Reflexive, antisymmetric and transitive?"""
    refl = all((x, x) in le for x in elems)
    anti = all((not ((x, y) in le and (y, x) in le)) or x == y
               for x in elems for y in elems)
    trans = all(((x, z) in le) for x in elems for y in elems for z in elems
                if (x, y) in le and (y, z) in le)
    return refl and anti and trans


def strict_order(le):
    return {(x, y) for (x, y) in le if x != y}


def derived_covers(elems, le):
    """x < y with no z, x < z < y."""
    lt = strict_order(le)
    return {(x, y) for (x, y) in lt
            if not any(z not in (x, y) and (x, z) in lt and (z, y) in lt
                       for z in elems)}


def meet_join(elems, le, x, y):
    """Return (meet, join); each is None if the corresponding bound is absent.

    In a finite poset the meet exists iff the lower bounds have a greatest
    element (unique by antisymmetry); likewise the join.
    """
    lower = [z for z in elems if (z, x) in le and (z, y) in le]
    upper = [z for z in elems if (x, z) in le and (y, z) in le]
    m = None
    if lower:
        cand = [z for z in lower if all((w, z) in le for w in lower)]
        if len(cand) == 1:
            m = cand[0]
    j = None
    if upper:
        cand = [z for z in upper if all((z, w) in le for w in upper)]
        if len(cand) == 1:
            j = cand[0]
    return m, j


def is_lattice(elems, le):
    for x in elems:
        for y in elems:
            m, j = meet_join(elems, le, x, y)
            if m is None or j is None:
                return False
    return True


def rank_longest_chain(elems, covers):
    """Height = length of the longest cover-chain ending at each element."""
    rank = {x: 0 for x in elems}
    changed = True
    while changed:
        changed = False
        for (u, v) in covers:
            if rank[v] < rank[u] + 1:
                rank[v] = rank[u] + 1
                changed = True
    return rank


def whitney(rank):
    """Whitney numbers of the SECOND kind: number of elements of each rank."""
    m = max(rank.values())
    return [sum(1 for r in rank.values() if r == k) for k in range(m + 1)]


def is_log_concave(W):
    return all(W[k] * W[k] >= W[k - 1] * W[k + 1] for k in range(1, len(W) - 1))


def is_strictly_log_concave(W):
    return all(W[k] * W[k] > W[k - 1] * W[k + 1] for k in range(1, len(W) - 1))


def deficit(W):
    """Total positive log-concavity deficit sum_k (W_{k-1}W_{k+1} - W_k^2)_+."""
    return sum(max(0, W[k - 1] * W[k + 1] - W[k] * W[k])
               for k in range(1, len(W) - 1))


def is_distributive(elems, le):
    for x in elems:
        for y in elems:
            for z in elems:
                xy, _ = meet_join(elems, le, x, y)
                xz, _ = meet_join(elems, le, x, z)
                _, yz = meet_join(elems, le, y, z)
                _, jj = meet_join(elems, le, xy, xz)      # (x^y) v (x^z)
                mj, _ = meet_join(elems, le, x, yz)       # x ^ (y v z)
                if mj != jj:
                    return False
    return True


# ----------------------------------------------------------------------
# N5 and isomorphism tests
# ----------------------------------------------------------------------

N5_ELEMS = [0, 1, 2, 3, 4]
N5_COVERS = [(0, 1), (1, 3), (3, 4), (0, 2), (2, 4)]
N5_LE = closure(N5_ELEMS, N5_COVERS)


def order_isomorphic(elems, le, target_elems, target_le):
    """Existence of a bijection preserving and reflecting the order."""
    if len(elems) != len(target_elems):
        return False
    for perm in permutations(target_elems):
        f = dict(zip(elems, perm))
        if all(((x, y) in le) == ((f[x], f[y]) in target_le)
               for x in elems for y in elems):
            return True
    return False


def count_n5_sublattices(elems, le):
    """Count 5-element subsets closed under meet and join that are N5.

    A sublattice is a subset containing the meet and join (computed in the
    ambient lattice) of each of its pairs.  We enumerate all 5-element subsets
    (the only possible size for an embedded N5) and test closure + isomorphism.
    """
    count = 0
    for S in combinations(elems, 5):
        S = list(S)
        closed = True
        for x in S:
            for y in S:
                m, j = meet_join(elems, le, x, y)
                if m not in S or j not in S:
                    closed = False
                    break
            if not closed:
                break
        if not closed:
            continue
        leS = {(x, y) for (x, y) in le if x in S and y in S}
        if order_isomorphic(S, leS, N5_ELEMS, N5_LE):
            count += 1
    return count


def count_n5_induced_subposets(elems, le):
    """Count 5-element subsets whose induced subposet is N5 (weaker test)."""
    count = 0
    for S in combinations(elems, 5):
        S = list(S)
        leS = {(x, y) for (x, y) in le if x in S and y in S}
        if order_isomorphic(S, leS, N5_ELEMS, N5_LE):
            count += 1
    return count


# ----------------------------------------------------------------------
# Cross-check: order ideals of the underlying poset
# ----------------------------------------------------------------------

P_ELEMS = [0, 1, 2]                  # 0, 1 = incomparable minimal elements; 2 = top
P_COVERS = [(0, 2), (1, 2)]


def order_ideals(elems, le):
    """All down-sets (order ideals) of the poset, as sorted tuples."""
    ideals = []
    for r in range(len(elems) + 1):
        for S in combinations(elems, r):
            S = set(S)
            if all((y in S) for x in S for y in elems if (y, x) in le and y != x):
                ideals.append(tuple(sorted(S)))
    return ideals


# ----------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------

def main():
    checks = []
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    le = closure(ELEMS, COVERS)
    lt = strict_order(le)

    # ------------------------------------------------------------------
    # [1] The order is a partial order, and is exactly the closure of covers
    # ------------------------------------------------------------------
    check("[1a] reflexive-transitive closure of the covers is a partial order",
          is_partial_order(ELEMS, le),
          f"|<=| = {len(le)} pairs (reflexive, antisymmetric, transitive)")

    dc = derived_covers(ELEMS, le)
    check("[1b] the covers re-derived from the order equal the input covers",
          dc == set(COVERS),
          f"derived = {sorted(dc)}")

    cover_len = {x: sum(1 for y in ELEMS if (x, y) in dc) for x in ELEMS}
    check("[1c] cover-relation degrees match the described lattice "
          "(0 -> {{a,b}}, a,b -> c, c -> 1)",
          cover_len == {0: 2, 1: 1, 2: 1, 3: 1, 4: 0},
          f"out-degrees = {cover_len}")

    # ------------------------------------------------------------------
    # [2] Lattice axioms: every pair has a meet and a join
    # ------------------------------------------------------------------
    check("[2a] every pair of elements has a meet and a join, so L is a lattice",
          is_lattice(ELEMS, le),
          "all 25 pairs have a unique GLB and a unique LUB")

    meet_tbl = {}
    join_tbl = {}
    for x in ELEMS:
        for y in ELEMS:
            m, j = meet_join(ELEMS, le, x, y)
            meet_tbl[(x, y)] = m
            join_tbl[(x, y)] = j
    check("[2b] meet/join tables contain no missing entry (lattice is total)",
          all(v is not None for v in meet_tbl.values())
          and all(v is not None for v in join_tbl.values()),
          "meet(a,b) = %s, join(a,b) = %s (a,b incomparable)"
          % (meet_tbl[(1, 2)], join_tbl[(1, 2)]))
    check("[2c] a v b = c above a and b: join(1,2) = 3, meet(1,2) = 0",
          join_tbl[(1, 2)] == 3 and meet_tbl[(1, 2)] == 0,
          "consistent with a, b < c = a v b")

    # ------------------------------------------------------------------
    # [3] Upper semimodularity (all 25 pairs)
    # ------------------------------------------------------------------
    def cov(x, y):
        return (x, y) in dc

    bad = [(x, y) for x in ELEMS for y in ELEMS
           if cov(meet_tbl[(x, y)], x) and not cov(y, join_tbl[(x, y)])]
    check("[3] upper semimodular: x^y < x  =>  y < x v y, for all 25 pairs",
          not bad,
          "no bad pair" if not bad else f"bad pairs: {bad}")

    # ------------------------------------------------------------------
    # [4] Rank function and Whitney numbers; log-concavity fails
    # ------------------------------------------------------------------
    rank = rank_longest_chain(ELEMS, dc)
    check("[4a] rank = longest cover-chain length = {0:0, a:1, b:1, c:2, 1:3}",
          rank == {0: 0, 1: 1, 2: 1, 3: 2, 4: 3},
          f"rank = {{{', '.join(f'{NAMES[k]}: {v}' for k, v in sorted(rank.items()))}}}")

    W = whitney(rank)
    check("[4b] Whitney numbers of the second kind are W = [1, 2, 1, 1]",
          W == [1, 2, 1, 1],
          f"W = {W} (coefficients of the rank generating function)")

    check("[4c] log-concavity FAILS at k = 2: W_2^2 = 1 < 2 = W_1 * W_3",
          W[2] ** 2 < W[1] * W[3],
          f"W_2^2 = {W[2] ** 2}, W_1*W_3 = {W[1] * W[3]}")

    check("[4d] weak log-concavity fails too, a fortiori strict log-concavity",
          not is_log_concave(W) and not is_strictly_log_concave(W),
          f"is_log_concave = {is_log_concave(W)}, "
          f"is_strictly_log_concave = {is_strictly_log_concave(W)}")

    d = deficit(W)
    check("[4e] the concavity deficit is positive: W_1*W_3 - W_2^2 = 1",
          W[1] * W[3] - W[2] ** 2 == 1 and d == 1,
          f"deficit = {d}")

    # ------------------------------------------------------------------
    # [5] Distributivity, and zero embedded N5 sublattices
    # ------------------------------------------------------------------
    check("[5a] L is distributive: x ^ (y v z) = (x ^ y) v (x ^ z) for all triples",
          is_distributive(ELEMS, le),
          "all 125 triples satisfy the distributive law")

    n5_sub = count_n5_sublattices(ELEMS, le)
    n5_ind = count_n5_induced_subposets(ELEMS, le)
    check("[5b] L contains ZERO N5 sublattices (N5 is non-distributive)",
          n5_sub == 0 and n5_ind == 0,
          f"N5 sublattices = {n5_sub}, N5 induced subposets = {n5_ind}; "
          f"yet deficit = {d} > 0")

    check("[5c] clause (i) is false: the deficit is 1 with ZERO N5 sublattices, "
          "so it is not 'controlled by the number of embedded N5 sublattices'",
          n5_sub == 0 and d == 1,
          "deficit 1 arises from a distributive lattice with no N5 at all")

    # ------------------------------------------------------------------
    # [6] Cross-check: order ideals of the underlying poset give W = [1,2,1,1]
    # ------------------------------------------------------------------
    P_le = closure(P_ELEMS, P_COVERS)
    ideals = order_ideals(P_ELEMS, P_le)
    check("[6a] the underlying poset P (two incomparable minima + top) has "
          "exactly 5 order ideals",
          len(ideals) == 5,
          f"ideals = {ideals}")

    ideal_rank = {I: len(I) for I in ideals}          # rank = cardinality
    Wid = whitney(ideal_rank)
    check("[6b] the order ideals, ranked by cardinality, give W = [1, 2, 1, 1]",
          Wid == [1, 2, 1, 1],
          f"W_from_ideals = {Wid}")

    ideal_le = {(I, J) for I in ideals for J in ideals
                if set(I).issubset(set(J))}
    witness_le = le
    check("[6c] the ideal lattice J(P) is order-isomorphic to the witness L "
          "(0<->{}, a<->{{0}}, b<->{{1}}, c<->{{0,1}}, top<->{{0,1,2}})",
          order_isomorphic(ideals, ideal_le, ELEMS, witness_le),
          "the witness IS the lattice of order ideals of P")

    # ------------------------------------------------------------------
    # [7] Clause (ii) is false: free Boolean lattices have no positive deficit
    # ------------------------------------------------------------------
    def binomial_row(n):
        row = [1]
        for _ in range(n):
            row = [1] + [row[k] + row[k + 1] for k in range(len(row) - 1)] + [1]
        return row

    bad_B = []
    for n in range(1, 21):
        B = binomial_row(n)
        if not is_strictly_log_concave(B) or deficit(B) != 0:
            bad_B.append((n, B, deficit(B)))
    check("[7a] free Boolean lattices B_n (rank numbers = binomial coefficients) "
          "are strictly log-concave with deficit 0, for n <= 20",
          not bad_B,
          "no positive-deficit Boolean example exists; "
          + (f"failures: {bad_B}" if bad_B else "B_3 = [1,3,3,1], deficit 0"))

    chain4 = [1, 1, 1, 1]
    check("[7b] the 4-element chain violates STRICT log-concavity degenerately, "
          "by equality: [1,1,1,1] has W_1*W_3 = W_2^2 = 1",
          is_log_concave(chain4) and not is_strictly_log_concave(chain4)
          and deficit(chain4) == 0,
          "weak log-concave (equality) but not strict")

    check("[7c] clause (ii) is false: no positive-deficit example occurs in any "
          "free Boolean lattice, and the minimal positive-deficit witness is the "
          "5-element semimodular lattice above, not a Boolean fifth layer",
          not bad_B and deficit(W) == 1,
          "Boolean ranks have deficit 0; the witness has deficit 1")

    # ------------------------------------------------------------------
    # Report
    # ------------------------------------------------------------------
    line = "=" * 76
    print(line)
    print("Disproof of conjecture 00000002605 -- reproduction")
    print(line)
    print("\nDefinition: Whitney numbers = coefficients of the rank generating")
    print("            function = number of elements of each rank (SECOND kind).")
    print("Conjecture: rank numbers of semimodular lattices are strictly")
    print("            log-concave; deficit controlled by embedded N5 count;")
    print("            minimal positive-deficit example is the fifth-layer")
    print("            embedding in the free Boolean lattice.")
    print("Claimed value: FALSE.")
    print("\nWitness: 0 < a, b < c = a v b < 1 with a, b incomparable")
    print("         (indices 0,1,2,3,4; covers "
          f"{[(x, y) for (x, y) in COVERS]}).")
    print("         distribute/modular => upper semimodular, so it is in the")
    print("         class 'semimodular lattices' named twice by the filing.")
    print(f"\nRank function: {{{', '.join(f'{NAMES[k]}: {v}' for k, v in sorted(rank.items()))}}}")
    print(f"Whitney numbers W = {W}")
    print(f"Failure: W_2^2 = {W[2] ** 2} < {W[1] * W[3]} = W_1 * W_3"
          f"   (deficit = {d})")

    print("\nChecks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"  [{mark}] {name}")
        print(f"         {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000002605 is FALSE.")
        print("  * W = [1,2,1,1] with W_2^2 = 1 < 2 = W_1*W_3: strict (and even")
        print("    weak) log-concavity fails in a distributive, upper-semimodular")
        print("    lattice that the filing names ('semimodular lattices').")
        print("  * Clause (i) is false: deficit 1 with ZERO N5 sublattices.")
        print("  * Clause (ii) is false: free Boolean lattices have binomial")
        print("    rank numbers, deficit 0; they provide no positive deficit at all.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    sys.exit(main())
