#!/usr/bin/env python3
"""Exhaustive computational verification for Conjecture 00000008560.

Verifies from first principles (using only the Python standard library):
  1. Unlabeled finite lattice classification for 1 <= |L| <= 6 (OEIS A006966: 1, 1, 1, 2, 5, 15).
  2. Clause 1 (Thin poset category): For finite lattices L1, L2, categorical equivalence
     C(L1) ~ C(L2) holds iff L1 and L2 are isomorphic lattices.
  3. Global category Lat_ord (and Lat_hom): Order duality (-)^op is an involutive covariant
     autoequivalence that is not naturally isomorphic to Id (already obstructed on {C_1, C_2}).
  4. Complete refutation of Clause 2 under every reading:
     - At |L| = 3, the unique lattice is the chain C_3 (distributive, modular, self-dual);
       no pentagon lattice exists of size 3.
     - The pentagon lattice N_5 (|N_5| = 5, height 3, 3 interior elements, unique minimal
       non-modular lattice) IS SELF-DUAL (N_5^op ~= N_5) and RIGID (|Aut(N_5)| = 1).
     - All lattices of size <= 4 (and all of height <= 2) are self-dual; the unique smallest
       non-self-dual lattices (both by size 5 and by height 3) are the mutually dual
       distributive lattices 1 (+) B_2 and B_2 (+) 1, NOT the pentagon lattice N_5.
     - On individual lattice categories C(L), the smallest nontrivial covariant autoequivalence
       occurs on B_2 (size 4, height 2; whereas |Aut(N_5)| = 1), and the smallest nontrivial
       contravariant self-duality occurs on C_2 (size 2, height 1).
"""

from __future__ import annotations
import itertools
import sys
from typing import Dict, List, Optional, Tuple

Matrix = Tuple[Tuple[bool, ...], ...]


def is_partial_order(n: int, leq: List[List[bool]]) -> bool:
    for i in range(n):
        if not leq[i][i]:
            return False
    for i in range(n):
        for j in range(i + 1, n):
            if leq[i][j] and leq[j][i]:
                return False
    for i in range(n):
        for j in range(n):
            if leq[i][j]:
                for k in range(n):
                    if leq[j][k] and not leq[i][k]:
                        return False
    return True


def join_meet_tables(
    n: int, leq: List[List[bool]]
) -> Optional[Tuple[List[List[int]], List[List[int]]]]:
    join_tbl = [[-1] * n for _ in range(n)]
    meet_tbl = [[-1] * n for _ in range(n)]
    for x in range(n):
        for y in range(x, n):
            ubs = [z for z in range(n) if leq[x][z] and leq[y][z]]
            if not ubs:
                return None
            lubs = [z for z in ubs if all(leq[z][u] for u in ubs)]
            if len(lubs) != 1:
                return None
            lbs = [z for z in range(n) if leq[z][x] and leq[z][y]]
            if not lbs:
                return None
            glbs = [z for z in lbs if all(leq[l][z] for l in lbs)]
            if len(glbs) != 1:
                return None
            join_tbl[x][y] = join_tbl[y][x] = lubs[0]
            meet_tbl[x][y] = meet_tbl[y][x] = glbs[0]
    return join_tbl, meet_tbl


def canonical_signature(n: int, leq: List[List[bool]]) -> Tuple[bool, ...]:
    best: Optional[Tuple[bool, ...]] = None
    for perm in itertools.permutations(range(n)):
        sig = tuple(leq[perm[i]][perm[j]] for i in range(n) for j in range(n))
        if best is None or sig < best:
            best = sig
    assert best is not None
    return best


def dual_order(n: int, leq: List[List[bool]]) -> List[List[bool]]:
    return [[leq[j][i] for j in range(n)] for i in range(n)]


def order_isomorphisms(
    n: int, leq1: List[List[bool]], leq2: List[List[bool]]
) -> List[Tuple[int, ...]]:
    isos: List[Tuple[int, ...]] = []
    for perm in itertools.permutations(range(n)):
        if all(
            leq1[i][j] == leq2[perm[i]][perm[j]]
            for i in range(n)
            for j in range(n)
        ):
            isos.append(perm)
    return isos


def covering_relations(n: int, leq: List[List[bool]]) -> List[Tuple[int, int]]:
    covs: List[Tuple[int, int]] = []
    for i in range(n):
        for j in range(n):
            if i != j and leq[i][j]:
                if not any(
                    k != i and k != j and leq[i][k] and leq[k][j]
                    for k in range(n)
                ):
                    covs.append((i, j))
    return covs


def lattice_height(n: int, leq: List[List[bool]]) -> int:
    memo: Dict[int, int] = {}

    def longest_from(u: int) -> int:
        if u in memo:
            return memo[u]
        best = 0
        for v in range(n):
            if v != u and leq[u][v]:
                best = max(best, 1 + longest_from(v))
        memo[u] = best
        return best

    return max(longest_from(u) for u in range(n))


def is_modular(
    n: int,
    leq: List[List[bool]],
    join_tbl: List[List[int]],
    meet_tbl: List[List[int]],
) -> bool:
    # Dedekind modular law: x <= z implies x v (y ^ z) = (x v y) ^ z
    for x in range(n):
        for z in range(n):
            if leq[x][z]:
                for y in range(n):
                    lhs = join_tbl[x][meet_tbl[y][z]]
                    rhs = meet_tbl[join_tbl[x][y]][z]
                    if lhs != rhs:
                        return False
    return True


def is_distributive(
    n: int, join_tbl: List[List[int]], meet_tbl: List[List[int]]
) -> bool:
    for x in range(n):
        for y in range(n):
            for z in range(n):
                if meet_tbl[x][join_tbl[y][z]] != join_tbl[meet_tbl[x][y]][meet_tbl[x][z]]:
                    return False
    return True


def enumerate_unlabeled_lattices(n: int) -> List[List[List[bool]]]:
    """Enumerate all unlabeled finite lattices on n elements up to isomorphism.

    Every finite lattice has a unique minimum (placed at 0) and maximum (placed at n-1),
    and admits a linear extension 0, 1, ..., n-1 so x <= y implies x <= y as integers.
    """
    if n == 1:
        return [[[True]]]
    upper_pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    forced = {(0, i) for i in range(1, n)} | {(i, n - 1) for i in range(n - 1)}
    free_pairs = [p for p in upper_pairs if p not in forced]
    seen: Dict[Tuple[bool, ...], List[List[bool]]] = {}
    for bits in itertools.product((False, True), repeat=len(free_pairs)):
        leq = [[i == j for j in range(n)] for i in range(n)]
        for i, j in forced:
            leq[i][j] = True
        for (i, j), b in zip(free_pairs, bits):
            if b:
                leq[i][j] = True
        if not is_partial_order(n, leq):
            continue
        if join_meet_tables(n, leq) is None:
            continue
        sig = canonical_signature(n, leq)
        if sig not in seen:
            seen[sig] = leq
    return [seen[k] for k in sorted(seen.keys())]


def monotone_maps(
    n1: int, leq1: List[List[bool]], n2: int, leq2: List[List[bool]]
) -> List[Tuple[int, ...]]:
    res: List[Tuple[int, ...]] = []
    edges1 = [(i, j) for i in range(n1) for j in range(n1) if i != j and leq1[i][j]]
    for tup in itertools.product(range(n2), repeat=n1):
        if all(leq2[tup[i]][tup[j]] for i, j in edges1):
            res.append(tup)
    return res


def thin_categories_equivalent(
    n1: int, leq1: List[List[bool]], n2: int, leq2: List[List[bool]]
) -> bool:
    """Check categorical equivalence C(L1) ~ C(L2) directly from category axioms.

    In a thin poset category C(L), two functors H1, H2 : C(A) -> C(B) are naturally
    isomorphic iff for every x in A, H1(x) <= H2(x) and H2(x) <= H1(x); by antisymmetry
    of L, this is pointwise equality H1 = H2.
    """
    funcs_12 = monotone_maps(n1, leq1, n2, leq2)
    funcs_21 = monotone_maps(n2, leq2, n1, leq1)
    for f in funcs_12:
        for g in funcs_21:
            gf_iso_id = all(
                leq1[g[f[x]]][x] and leq1[x][g[f[x]]] for x in range(n1)
            )
            fg_iso_id = all(
                leq2[f[g[y]]][y] and leq2[y][f[g[y]]] for y in range(n2)
            )
            if gf_iso_id and fg_iso_id:
                return True
    return False


def main() -> None:
    print("========================================================================")
    print("Computational Verification for Conjecture 00000008560")
    print("========================================================================\n")

    expected_counts = {1: 1, 2: 1, 3: 1, 4: 2, 5: 5, 6: 15}
    catalog: Dict[int, List[Dict[str, object]]] = {}

    print("[1] Exhaustive classification of finite lattices for 1 <= |L| <= 6")
    for n in range(1, 7):
        lats = enumerate_unlabeled_lattices(n)
        assert len(lats) == expected_counts[n], (
            f"Count mismatch at n={n}: got {len(lats)}, expected {expected_counts[n]}"
        )
        entries: List[Dict[str, object]] = []
        for idx, leq in enumerate(lats):
            jm = join_meet_tables(n, leq)
            assert jm is not None
            join_tbl, meet_tbl = jm
            d_leq = dual_order(n, leq)
            auts = order_isomorphisms(n, leq, leq)
            anti_auts = order_isomorphisms(n, leq, d_leq)
            self_dual = len(anti_auts) > 0
            h = lattice_height(n, leq)
            mod = is_modular(n, leq, join_tbl, meet_tbl)
            dist = is_distributive(n, join_tbl, meet_tbl)
            if dist:
                assert mod, "Every distributive lattice must be modular"
            covs = covering_relations(n, leq)
            entry = {
                "n": n,
                "idx": idx,
                "leq": leq,
                "dual_leq": d_leq,
                "join": join_tbl,
                "meet": meet_tbl,
                "height": h,
                "auts": auts,
                "anti_auts": anti_auts,
                "self_dual": self_dual,
                "modular": mod,
                "distributive": dist,
                "covers": covs,
            }
            entries.append(entry)
        catalog[n] = entries
        sd_count = sum(1 for e in entries if e["self_dual"])
        nsd_count = len(entries) - sd_count
        print(
            f"  n = {n}: {len(entries):2d} lattices "
            f"(self-dual: {sd_count:2d}, non-self-dual: {nsd_count:2d}) [OEIS A006966 OK]"
        )

    print("\n  Detailed table for 1 <= |L| <= 5:")
    for n in range(1, 6):
        for e in catalog[n]:
            print(
                f"    L({n},{e['idx']}): height={e['height']}, "
                f"|Aut|={len(e['auts'])}, |Iso(L,L^op)|={len(e['anti_auts'])}, "
                f"self_dual={str(e['self_dual']):5s}, modular={str(e['modular']):5s}, "
                f"dist={str(e['distributive']):5s}, covers={e['covers']}"
            )

    # 2. Verify Clause 1 on all lattices of size <= 5
    print("\n[2] Checking Clause 1 (C(L1) ~ C(L2) iff L1 ~= L2 as lattices) for |L| <= 5")
    small_entries = [e for n in range(1, 6) for e in catalog[n]]
    pairs_checked = 0
    for i, e1 in enumerate(small_entries):
        for j, e2 in enumerate(small_entries):
            n1, leq1 = int(e1["n"]), e1["leq"]  # type: ignore[arg-type]
            n2, leq2 = int(e2["n"]), e2["leq"]  # type: ignore[arg-type]
            cat_eq = thin_categories_equivalent(n1, leq1, n2, leq2)  # type: ignore[arg-type]
            lat_iso = (n1 == n2) and len(order_isomorphisms(n1, leq1, leq2)) > 0  # type: ignore[arg-type]
            assert cat_eq == lat_iso, f"Mismatch between C(L1)~C(L2) and L1~=L2 at {(i, j)}"
            pairs_checked += 1
    print(f"  Verified {pairs_checked} ordered pairs (L1, L2): C(L1) ~ C(L2) <=> L1 ~= L2 holds 100%.")

    # Also verify every order isomorphism preserves meet and join explicitly
    for n in range(1, 7):
        for e in catalog[n]:
            leq = e["leq"]  # type: ignore[assignment]
            join_tbl = e["join"]  # type: ignore[assignment]
            meet_tbl = e["meet"]  # type: ignore[assignment]
            for perm in e["auts"]:  # type: ignore[attr-defined]
                for x in range(n):
                    for y in range(n):
                        assert perm[join_tbl[x][y]] == join_tbl[perm[x]][perm[y]]
                        assert perm[meet_tbl[x][y]] == meet_tbl[perm[x]][perm[y]]

    # 3. Verify naturality obstruction for (-)^op on Lat_ord already on {C_1, C_2}
    print("\n[3] Checking global category Lat_ord duality autoequivalence (-)^op")
    c1_leq = catalog[1][0]["leq"]  # type: ignore[assignment]
    c2_leq = catalog[2][0]["leq"]  # type: ignore[assignment]
    c1_isos = order_isomorphisms(1, c1_leq, dual_order(1, c1_leq))  # type: ignore[arg-type]
    c2_isos = order_isomorphisms(2, c2_leq, dual_order(2, c2_leq))  # type: ignore[arg-type]
    assert c1_isos == [(0,)]
    assert c2_isos == [(1, 0)]
    eta_c1 = c1_isos[0]
    eta_c2 = c2_isos[0]
    # Constant map c_0 : C_1 -> C_2 sending 0 -> 0
    c0 = (0,)
    # Naturality square D(c0) o eta_C1 == eta_C2 o c0 where D(c0) = c0 on underlying sets
    lhs_nat = c0[eta_c1[0]]
    rhs_nat = eta_c2[c0[0]]
    assert lhs_nat != rhs_nat, "Expected naturality failure on C_1 -> C_2"
    print(
        f"  Unique iso C_1 -> C_1^op is {eta_c1}; unique iso C_2 -> C_2^op is {eta_c2}."
    )
    print(
        f"  On constant monotone map c_0: C_1 -> C_2 (0 |-> 0), "
        f"D(c_0)(eta_C1(0)) = {lhs_nat} != {rhs_nat} = eta_C2(c_0(0))."
    )
    print("  => (-)^op is NOT naturally isomorphic to Id_Lat_ord (already obstructed at |L| <= 2).")

    # 4. Verify all refutation claims against Clause 2
    print("\n[4] Refuting Clause 2 ('smallest example is the pentagon lattice at n = 3')")

    # 4a. Size 3 check
    assert len(catalog[3]) == 1
    c3 = catalog[3][0]
    assert c3["distributive"] is True and c3["modular"] is True and c3["self_dual"] is True
    print("  [4a] At |L| = 3: unique lattice is C_3 (chain 0 < 1 < 2), distributive, modular, self-dual.")
    print("       NO pentagon lattice exists of cardinality 3.")

    # 4b. Identify pentagon lattice N_5 uniquely at n <= 5
    non_mod_le5 = [e for n in range(1, 6) for e in catalog[n] if not e["modular"]]
    assert len(non_mod_le5) == 1
    n5 = non_mod_le5[0]
    assert n5["n"] == 5
    assert n5["height"] == 3
    assert len(n5["auts"]) == 1  # type: ignore[arg-type]
    assert len(n5["anti_auts"]) == 1  # type: ignore[arg-type]
    assert n5["self_dual"] is True
    n5_dual_iso = n5["anti_auts"][0]  # type: ignore[index]
    print(
        f"  [4b] Pentagon lattice N_5 is the unique non-modular lattice with |L| <= 5:\n"
        f"       |N_5| = {n5['n']}, height = {n5['height']}, covers = {n5['covers']},\n"
        f"       |Aut(N_5)| = {len(n5['auts'])} (rigid), "  # type: ignore[arg-type]
        f"|Iso(N_5, N_5^op)| = {len(n5['anti_auts'])} via perm = {n5_dual_iso} (SELF-DUAL!)."  # type: ignore[arg-type]
    )

    # 4c. Check all non-self-dual lattices up to size 6
    nsd_le4 = [e for n in range(1, 5) for e in catalog[n] if not e["self_dual"]]
    assert len(nsd_le4) == 0, "Expected all lattices of size <= 4 to be self-dual"
    nsd_h_le2 = [e for n in range(1, 7) for e in catalog[n] if int(e["height"]) <= 2 and not e["self_dual"]]  # type: ignore[arg-type]
    assert len(nsd_h_le2) == 0, "Expected all lattices of height <= 2 (|L|<=6; in fact all finite) to be self-dual"

    nsd_5 = [e for e in catalog[5] if not e["self_dual"]]
    assert len(nsd_5) == 2
    assert all(e["distributive"] is True and e["modular"] is True and e["height"] == 3 for e in nsd_5)
    # Verify the two non-self-dual lattices of size 5 are duals of each other
    assert len(order_isomorphisms(5, nsd_5[0]["leq"], nsd_5[1]["dual_leq"])) == 2  # type: ignore[arg-type]
    # Verify 1 (+) B_2 has 1 atom and B_2 (+) 1 has 2 atoms
    atoms_0 = [x for x, y in nsd_5[0]["covers"] if x == 0]  # type: ignore[attr-defined]
    atoms_1 = [x for x, y in nsd_5[1]["covers"] if x == 0]  # type: ignore[attr-defined]
    assert len(atoms_0) == 1 and len(atoms_1) == 2
    print(
        "  [4c] All lattices with |L| <= 4 (and all with height <= 2) are self-dual.\n"
        "       At |L| = 5 (height 3, 3 proper elements), there are EXACTLY 2 non-self-dual lattices:\n"
        f"         - 1 (+) B_2: covers = {nsd_5[0]['covers']}, distributive = {nsd_5[0]['distributive']}\n"
        f"         - B_2 (+) 1: covers = {nsd_5[1]['covers']}, distributive = {nsd_5[1]['distributive']}\n"
        "       Both are modular & distributive; NEITHER is the pentagon lattice N_5 (which is self-dual!)."
    )

    nsd_nonmod_6 = [e for e in catalog[6] if not e["self_dual"] and not e["modular"]]
    print(
        f"       (Even among non-modular lattices, non-self-duality first occurs at |L| = 6: "
        f"{len(nsd_nonmod_6)} examples.)"
    )

    # 4d. Check individual lattice category C(L) covariant and contravariant self-equivalences
    nontriv_cov = [
        e for n in range(1, 6) for e in catalog[n] if len(e["auts"]) > 1  # type: ignore[arg-type]
    ]
    first_cov = nontriv_cov[0]
    assert first_cov["n"] == 4 and first_cov["height"] == 2
    nontriv_contra = [
        e
        for n in range(1, 6)
        for e in catalog[n]
        if any(perm != tuple(range(n)) for perm in e["anti_auts"])  # type: ignore[attr-defined]
    ]
    first_contra = nontriv_contra[0]
    assert first_contra["n"] == 2 and first_contra["height"] == 1
    print(
        f"  [4d] Individual poset category C(L):\n"
        f"       - Smallest nontrivial covariant autoequivalence (Aut(L) != {{id}}): "
        f"B_2 at |L| = {first_cov['n']}, height = {first_cov['height']} (whereas |Aut(N_5)| = 1).\n"
        f"       - Smallest nontrivial contravariant self-duality (delta != id): "
        f"C_2 at |L| = {first_contra['n']}, height = {first_contra['height']} "
        f"(and C_3 at |L| = 3, C_4 at height = 3)."
    )

    print("\n========================================================================")
    print("ALL ASSERTIONS PASSED: Conjecture 00000008560 is REFUTED (FALSE).")
    print("========================================================================")


if __name__ == "__main__":
    main()
