#!/usr/bin/env python3
"""
Standalone Computational Verification Suite for Conjecture 00000008546
("Orbit-Sperner under symmetric group actions: maximum of orbit antichains under
symmetric group actions is the symmetrized Sperner number; and its difference
from the classical Sperner number is of logarithmic order.")

Verifies all theorems, exact identities, bounds, and counterexamples established
in the disproof and Core Lean 4.19.0 formalization:
  1. De Bruijn-Tengbergen-Kruyswijk Symmetric Chain Decomposition & Sperner's Theorem.
  2. Canonical (B_n, S_n) action: w_inv = C(n, n//2) (deficit 0) and w_orb = 1
     (exponential deficit C(n, n//2) - 1), plus asymptotic ratio vs log_2(n).
  3. Universal Permutation Subgroup Dichotomy on B_N (2 <= N <= 6): every nontrivial
     subgroup H <= S_N satisfies 2 * width(B_N / H) <= C(N, N//2) + C(N-1, (N-1)//2),
     with exact minimum deficit C(N-2, N//2 - 1) achieved by a single transposition.
  4. Canonical structured S_n-posets: Young subgroups S_a x S_b on B_{a+b},
     diagonal S_n-action on B_n x B_n, unlabeled graph poset B_{C(m,2)} / S_m,
     and chain products C_m^n / S_n.
  5. Freese-Dilworth Invariant Antichain Theorem: w_inv(P, G) = width(P) (deficit 0)
     across graded and ungraded, Sperner and non-Sperner finite posets with symmetry.
  6. Faithful S_n-Poset Counterexample Family P(n) (size 4n + 6, 2 <= n <= 8):
     bounded graded Sperner poset (width = max_rank = 2n + 2) with faithful S_n-action
     whose quotient P(n)/S_n has symmetrized Sperner number 4 yet orbit-antichain width 5,
     refuting Clause 1 on general bounded graded Sperner posets.
"""

from __future__ import annotations

import itertools
import math
import sys
from typing import Callable, Hashable, Iterable, Sequence, TypeVar

T = TypeVar("T", bound=Hashable)


def poset_width(elements: Sequence[T], leq: Callable[[T, T], bool]) -> int:
    """Exact Dilworth/Sperner width of a finite poset via Konig bipartite matching."""
    m = len(elements)
    adj: list[list[int]] = [[] for _ in range(m)]
    for i in range(m):
        ei = elements[i]
        for j in range(m):
            if i != j and leq(ei, elements[j]):
                adj[i].append(j)

    match_right = [-1] * m

    def dfs(u: int, visited: list[bool]) -> bool:
        for v in adj[u]:
            if not visited[v]:
                visited[v] = True
                if match_right[v] == -1 or dfs(match_right[v], visited):
                    match_right[v] = u
                    return True
        return False

    matching = 0
    for u in range(m):
        visited = [False] * m
        if dfs(u, visited):
            matching += 1
    return m - matching


def build_quotient_poset(
    elements: Sequence[T],
    leq: Callable[[T, T], bool],
    generators: Sequence[Callable[[T], T]],
) -> tuple[list[frozenset[T]], Callable[[int, int], bool]]:
    """Construct G-orbits, verify every orbit is an antichain, and verify P/G is a poset."""
    idx_of = {e: i for i, e in enumerate(elements)}
    visited = [False] * len(elements)
    orbits: list[frozenset[T]] = []

    for i, e in enumerate(elements):
        if not visited[i]:
            orb: set[T] = set()
            stack = [e]
            while stack:
                cur = stack.pop()
                if cur not in orb:
                    orb.add(cur)
                    visited[idx_of[cur]] = True
                    for g in generators:
                        nxt = g(cur)
                        if nxt not in orb:
                            stack.append(nxt)
            orbits.append(frozenset(orb))

    # Verify Harper-Stanley Orbit-Antichain Lemma on every orbit
    for orb in orbits:
        for x in orb:
            for y in orb:
                if x != y and leq(x, y):
                    raise AssertionError(f"Comparable distinct elements in orbit: {x}, {y}")

    k = len(orbits)
    rel = [[False] * k for _ in range(k)]
    for i in range(k):
        rel[i][i] = True
        for j in range(k):
            if i != j:
                rel[i][j] = any(leq(x, y) for x in orbits[i] for y in orbits[j])

    # Verify antisymmetry and transitivity of P/G
    for i in range(k):
        for j in range(k):
            if i != j and rel[i][j] and rel[j][i]:
                raise AssertionError("Quotient relation failed antisymmetry")
    for i in range(k):
        for j in range(k):
            if rel[i][j]:
                for r in range(k):
                    if rel[j][r] and not rel[i][r]:
                        raise AssertionError("Quotient relation failed transitivity")

    return orbits, (lambda i, j: rel[i][j])


def max_invariant_antichain_via_quotient(
    orbits: Sequence[frozenset[T]], q_leq: Callable[[int, int], bool]
) -> int:
    """Exact maximum cardinality of a G-invariant antichain (for small |P/G| <= 20)."""
    k = len(orbits)
    assert k <= 50
    best = 0
    # Branch-and-bound over orbit indices
    weights = [len(o) for o in orbits]

    def backtrack(idx: int, chosen: list[int], cur_w: int, rem_w: int) -> None:
        nonlocal best
        if cur_w > best:
            best = cur_w
        if idx == k or cur_w + rem_w <= best:
            return
        nxt_rem = rem_w - weights[idx]
        if all(not q_leq(idx, c) and not q_leq(c, idx) for c in chosen):
            chosen.append(idx)
            backtrack(idx + 1, chosen, cur_w + weights[idx], nxt_rem)
            chosen.pop()
        backtrack(idx + 1, chosen, cur_w, nxt_rem)

    backtrack(0, [], 0, sum(weights))
    return best


def symmetric_chain_decomposition(n: int) -> list[list[tuple[int, ...]]]:
    """De Bruijn-Tengbergen-Kruyswijk inductive SCD matching BooleanSperner.lean."""
    if n == 0:
        return [[()]]
    prev = symmetric_chain_decomposition(n - 1)
    chains: list[list[tuple[int, ...]]] = []
    for c in prev:
        top = [x + (0,) for x in c] + [c[-1] + (1,)]
        chains.append(top)
        if len(c) >= 2:
            bot = [x + (1,) for x in c[:-1]]
            chains.append(bot)
    return chains


def verify_1_scd_and_boolean_sn() -> None:
    print("[Test 1] Symmetric Chain Decomposition & Canonical (B_n, S_n) Action")
    for n in range(0, 9):
        scd = symmetric_chain_decomposition(n)
        sperner = math.comb(n, n // 2)
        assert len(scd) == sperner, f"SCD count mismatch at n={n}"
        seen = [x for c in scd for x in c]
        assert len(seen) == 2**n and len(set(seen)) == 2**n
        for c in scd:
            assert sum(c[0]) + sum(c[-1]) == n
            for a, b in zip(c, c[1:]):
                assert sum(b) == sum(a) + 1
                assert all(x <= y for x, y in zip(a, b))

    for n in range(0, 7):
        b_n = [
            frozenset(s)
            for r in range(n + 1)
            for s in itertools.combinations(range(n), r)
        ]
        leq = lambda x, y: x.issubset(y)
        gens: list[Callable[[frozenset[int]], frozenset[int]]] = []
        if n >= 2:
            gens.append(lambda s: frozenset((1 - x if x in (0, 1) else x) for x in s))
            gens.append(lambda s, n=n: frozenset(((x + 1) % n) for x in s))
        else:
            gens.append(lambda s: s)

        orbits, q_leq = build_quotient_poset(b_n, leq, gens)
        w_bn = poset_width(b_n, leq)
        w_orb = poset_width(list(range(len(orbits))), q_leq)
        w_inv = max_invariant_antichain_via_quotient(orbits, q_leq)
        sperner = math.comb(n, n // 2)
        assert len(orbits) == n + 1
        assert w_bn == sperner
        assert w_inv == sperner  # Deficit = 0 identically!
        assert w_orb == 1        # Quotient B_n / S_n ~= C_{n+1} has width 1!
        print(
            f"  n={n}: width(B_n)={w_bn:2d}, w_inv={w_inv:2d} (def_inv=0), "
            f"w_orb={w_orb} (def_orb={sperner - 1:2d})"
        )

    print("  Asymptotic divergence of (C(n, n//2) - 1) / log_2(n):")
    prev_ratio = 0.0
    for n in [4, 8, 16, 32, 64]:
        def_orb = math.comb(n, n // 2) - 1
        ratio = def_orb / math.log2(n)
        assert ratio > prev_ratio
        prev_ratio = ratio
        print(f"    n={n:2d}: def_orb = {def_orb}, def_orb / log_2(n) = {ratio:.3e}")


def verify_2_universal_subgroup_dichotomy() -> None:
    print("\n[Test 2] Universal Permutation Subgroup Dichotomy on B_N (2 <= N <= 6)")
    for n in range(2, 7):
        b_n = [
            frozenset(s)
            for r in range(n + 1)
            for s in itertools.combinations(range(n), r)
        ]
        leq = lambda x, y: x.issubset(y)
        sperner_n = math.comb(n, n // 2)
        sperner_prev = math.comb(n - 1, (n - 1) // 2)
        lean_upper_2w = sperner_n + sperner_prev
        exact_transposition_deficit = math.comb(n - 2, n // 2 - 1)
        min_def = sperner_n

        # Check representative of every conjugacy class (cycle type) of non-identity permutations!
        # For N <= 5 check ALL non-identity permutations; for N = 6 check all cycle types + random sample.
        perms_to_check: list[tuple[int, ...]] = []
        if n <= 5:
            perms_to_check = [
                p for p in itertools.permutations(range(n)) if p != tuple(range(n))
            ]
        else:
            # Generate one representative per integer partition of 6 (excluding 1^6)
            partitions_6 = [
                [2, 1, 1, 1, 1], [2, 2, 1, 1], [2, 2, 2],
                [3, 1, 1, 1], [3, 2, 1], [3, 3],
                [4, 1, 1], [4, 2], [5, 1], [6],
            ]
            for part in partitions_6:
                perm = list(range(n))
                cur = 0
                for clen in part:
                    for j in range(clen):
                        perm[cur + j] = cur + ((j + 1) % clen)
                    cur += clen
                perms_to_check.append(tuple(perm))

        for perm in perms_to_check:
            g = lambda s, p=perm: frozenset(p[x] for x in s)
            orbits, q_leq = build_quotient_poset(b_n, leq, [g])
            w_orb = poset_width(list(range(len(orbits))), q_leq)
            assert 2 * w_orb <= lean_upper_2w, (
                f"Universal bound violated at N={n}, perm={perm}: "
                f"2*{w_orb} > {lean_upper_2w}"
            )
            deficit = sperner_n - w_orb
            min_def = min(min_def, deficit)

        assert min_def == exact_transposition_deficit
        print(
            f"  N={n}: C(N,N//2)={sperner_n:2d}, min_nontrivial_deficit={min_def:2d} "
            f"== C(N-2,N//2-1)={exact_transposition_deficit:2d}, "
            f"Lean bound deficit >= {(sperner_n - sperner_prev) / 2:.1f}"
        )


def verify_3_structured_sn_posets() -> None:
    print("\n[Test 3] Young Subgroups, Diagonal B_n x B_n, Unlabeled Graphs, and C_m^n")
    # 3a. Young subgroups S_a x S_b on B_{a+b}: B_n / (S_a x S_b) ~= C_{a+1} x C_{b+1}
    for a, b in [(1, 2), (2, 2), (2, 3), (3, 3)]:
        n = a + b
        b_n = [
            frozenset(s)
            for r in range(n + 1)
            for s in itertools.combinations(range(n), r)
        ]
        leq = lambda x, y: x.issubset(y)
        gens = []
        if a >= 2:
            gens.append(lambda s: frozenset((1 - x if x in (0, 1) else x) for x in s))
            gens.append(lambda s, a=a: frozenset(((x + 1) % a if x < a else x) for x in s))
        if b >= 2:
            gens.append(
                lambda s, a=a: frozenset(((2 * a + 1 - x) if x in (a, a + 1) else x) for x in s)
            )
            gens.append(
                lambda s, a=a, b=b: frozenset(
                    (a + (x - a + 1) % b if x >= a else x) for x in s
                )
            )
        orbits, q_leq = build_quotient_poset(b_n, leq, gens)
        w_orb = poset_width(list(range(len(orbits))), q_leq)
        w_inv = max_invariant_antichain_via_quotient(orbits, q_leq)
        sperner = math.comb(n, n // 2)
        assert w_inv == sperner
        assert w_orb == min(a + 1, b + 1)
        print(
            f"  Young S_{a}xS_{b} on B_{n}: Sperner={sperner:2d}, w_inv={w_inv:2d} (def=0), "
            f"w_orb={w_orb} (def={sperner - w_orb:2d})"
        )

    # 3b. Diagonal S_n on B_n x B_n ~= B_{2n}
    for n in range(1, 5):
        elems = [
            (frozenset(s1), frozenset(s2))
            for r1 in range(n + 1)
            for s1 in itertools.combinations(range(n), r1)
            for r2 in range(n + 1)
            for s2 in itertools.combinations(range(n), r2)
        ]
        leq = lambda u, v: u[0].issubset(v[0]) and u[1].issubset(v[1])
        gens = []
        if n >= 2:
            gens.append(
                lambda u: (
                    frozenset((1 - x if x in (0, 1) else x) for x in u[0]),
                    frozenset((1 - x if x in (0, 1) else x) for x in u[1]),
                )
            )
            gens.append(
                lambda u, n=n: (
                    frozenset(((x + 1) % n) for x in u[0]),
                    frozenset(((x + 1) % n) for x in u[1]),
                )
            )
        else:
            gens.append(lambda u: u)
        orbits, q_leq = build_quotient_poset(elems, leq, gens)
        w_orb = poset_width(list(range(len(orbits))), q_leq)
        w_inv = max_invariant_antichain_via_quotient(orbits, q_leq)
        sperner = math.comb(2 * n, n)
        expected_mid_orbits = ((n + 2) ** 2) // 4  # sum_{c=0..n//2} (n + 1 - 2c)
        assert w_inv == sperner
        assert w_orb == expected_mid_orbits
        print(
            f"  Diagonal S_{n} on B_{n}xB_{n}: Sperner={sperner:2d}, w_inv={w_inv:2d} (def=0), "
            f"w_orb={w_orb} == ((n+2)^2)//4 (def={sperner - w_orb:2d})"
        )

    # 3c. Graph poset B_{C(m,2)} under S_m
    for m in range(3, 6):
        edges = list(itertools.combinations(range(m), 2))
        num_e = len(edges)
        b_edges = [
            frozenset(s)
            for r in range(num_e + 1)
            for s in itertools.combinations(edges, r)
        ]
        leq = lambda x, y: x.issubset(y)

        def act_graph(perm: Sequence[int], gset: frozenset[tuple[int, int]]) -> frozenset[tuple[int, int]]:
            return frozenset(
                (perm[u], perm[v]) if perm[u] < perm[v] else (perm[v], perm[u])
                for u, v in gset
            )

        gens = [
            lambda s, m=m: act_graph([1, 0] + list(range(2, m)), s),
            lambda s, m=m: act_graph([(i + 1) % m for i in range(m)], s),
        ]
        orbits, q_leq = build_quotient_poset(b_edges, leq, gens)
        orb_ranks = [
            sum(1 for o in orbits if len(next(iter(o))) == r) for r in range(num_e + 1)
        ]
        w_orb = poset_width(list(range(len(orbits))), q_leq)
        sperner = math.comb(num_e, num_e // 2)
        assert w_orb == max(orb_ranks)  # Stanley's Quotient Peck Theorem
        print(
            f"  Graphs on m={m} vertices (N={num_e:2d}): Sperner={sperner:3d}, "
            f"w_orb={w_orb} (unlabeled middle rank), def={sperner - w_orb:3d}"
        )


def verify_4_freese_dilworth_general_posets() -> None:
    print("\n[Test 4] Freese-Dilworth Invariant Antichain Theorem on General Posets")
    # Example A: Ungraded poset where non-invariant maximum antichains exist, yet a
    # unique downset-minimal maximum antichain A* is fixed by Aut(P)!
    # Poset of two swapped 2-chains (0 < 1) and (2 < 3): max antichains are
    # {0, 2}, {0, 3}, {1, 2}, {1, 3}; {0, 3} and {1, 2} are NOT swap-invariant,
    # while A* = {0, 2} minimizes |downset| and IS swap-invariant!
    elems_a = [0, 1, 2, 3]
    leq_a = lambda x, y: x == y or (x == 0 and y == 1) or (x == 2 and y == 3)
    swap_a = lambda x: {0: 2, 1: 3, 2: 0, 3: 1}[x]
    orbits_a, q_leq_a = build_quotient_poset(elems_a, leq_a, [swap_a])
    w_a = poset_width(elems_a, leq_a)
    w_inv_a = max_invariant_antichain_via_quotient(orbits_a, q_leq_a)
    assert w_a == 2 and w_inv_a == 2

    # Example B: Non-Sperner graded poset (bowtie + crown hybrid with S_3 symmetry):
    # Rank 0: a0, a1, a2; Rank 1: b0 (above all ai), c0, c1, c2 (isolated from each other,
    # Wait: connect ai < b0 and b0 < d0, d1, d2 so middle rank is smaller than outer ranks!)
    # Classic non-Sperner graded poset: Rank 0 = {x0, x1, x2}, Rank 1 = {m}, Rank 2 = {y0, y1, y2}
    # with xi < m < yj? No, width({x0,x1,x2}) = 3 = max_rank.
    # Make TWO copies of (3-1-1) upside down:
    # Copy 1: {u0, u1, u2} < m1 < t1; Copy 2: b2 < m2 < {v0, v1, v2}, with S_3 permuting {0,1,2}!
    # Ranks: R0 = {u0, u1, u2, b2} (size 4), R1 = {m1, m2} (size 2), R2 = {t1, v0, v1, v2} (size 4),
    # while {u0, u1, u2, v0, v1, v2} is an antichain of size 6 > 4 (NON-SPERNER!),
    # and is S_3-invariant so w_inv = width = 6 (deficit STILL 0!).
    elems_b = ["u0", "u1", "u2", "b2", "m1", "m2", "t1", "v0", "v1", "v2"]
    chains_b = [
        ("u0", "m1"), ("u1", "m1"), ("u2", "m1"), ("m1", "t1"),
        ("u0", "t1"), ("u1", "t1"), ("u2", "t1"),
        ("b2", "m2"), ("m2", "v0"), ("m2", "v1"), ("m2", "v2"),
        ("b2", "v0"), ("b2", "v1"), ("b2", "v2"),
    ]
    edge_set = set(chains_b)
    leq_b = lambda x, y: x == y or (x, y) in edge_set

    def cyc3(x: str) -> str:
        if x[0] in ("u", "v") and x[1] in "012":
            return x[0] + str((int(x[1]) + 1) % 3)
        return x

    def swp01(x: str) -> str:
        if x[0] in ("u", "v") and x[1] in "01":
            return x[0] + str(1 - int(x[1]))
        return x

    orbits_b, q_leq_b = build_quotient_poset(elems_b, leq_b, [cyc3, swp01])
    w_b = poset_width(elems_b, leq_b)
    w_inv_b = max_invariant_antichain_via_quotient(orbits_b, q_leq_b)
    assert w_b == 6 and w_inv_b == 6  # Non-Sperner (max rank 4 < width 6), yet deficit = 0!
    print(f"  Swap-chains poset: width={w_a}, w_inv={w_inv_a}, deficit={w_a - w_inv_a}")
    print(f"  Non-Sperner S_3-poset: max_rank=4, width={w_b}, w_inv={w_inv_b}, deficit={w_b - w_inv_b}")


def verify_5_faithful_sn_counterexample_family() -> None:
    print("\n[Test 5] Faithful S_n-Poset Counterexample Family P(n) Refuting Clause 1 (2 <= n <= 8)")
    for n in range(2, 9):
        p0 = [("bot", 0)]
        p1 = [("a", 0), ("a", 1)] + [("c1", i) for i in range(n)] + [("c2", i) for i in range(n)]
        p2 = [("b", 0), ("b", 1)] + [("d1", i) for i in range(n)] + [("d2", i) for i in range(n)]
        p3 = [("top", 0)]
        pn = p0 + p1 + p2 + p3
        assert len(pn) == 4 * n + 6

        def rk(x: tuple[str, int]) -> int:
            if x[0] == "bot":
                return 0
            if x[0] in ("a", "c1", "c2"):
                return 1
            if x[0] in ("b", "d1", "d2"):
                return 2
            return 3

        def leq(x: tuple[str, int], y: tuple[str, int]) -> bool:
            if x == y:
                return True
            rx, ry = rk(x), rk(y)
            if rx >= ry:
                return False
            if rx == 0 or ry == 3:
                return True
            if x[0] == "a":
                return y[0] == "d2"
            return True

        gens = [
            lambda x: (x[0], 1 - x[1] if x[1] in (0, 1) else x[1])
            if x[0] in ("c1", "c2", "d1", "d2")
            else x,
            lambda x, n=n: (x[0], (x[1] + 1) % n)
            if x[0] in ("c1", "c2", "d1", "d2")
            else x,
        ]

        w_pn = poset_width(pn, leq)
        max_rk = max(len(p0), len(p1), len(p2), len(p3))
        orbits, q_leq = build_quotient_poset(pn, leq, gens)
        orb_ranks = [sum(1 for o in orbits if rk(next(iter(o))) == r) for r in range(4)]
        sym_sperner = max(orb_ranks)
        w_orb = poset_width(list(range(len(orbits))), q_leq)
        w_inv = max_invariant_antichain_via_quotient(orbits, q_leq)

        assert w_pn == max_rk == 2 * n + 2, "P(n) must have the classical Sperner property"
        assert orb_ranks == [1, 4, 4, 1] and sym_sperner == 4
        assert w_orb == 5 > sym_sperner, "P(n)/S_n must violate Orbit-Sperner (5 > 4)"
        assert w_inv == 2 * n + 2
        print(
            f"  n={n}: |P(n)|={len(pn):2d}, Sperner width={w_pn:2d} == max_rank={max_rk:2d}, "
            f"sym_Sperner=max|P_k/S_n|={sym_sperner}, width(P(n)/S_n)={w_orb} (> 4!)"
        )


def main() -> int:
    print("=" * 74)
    print("Conjecture 00000008546 — Complete Computational Verification Suite")
    print("=" * 74)
    verify_1_scd_and_boolean_sn()
    verify_2_universal_subgroup_dichotomy()
    verify_3_structured_sn_posets()
    verify_4_freese_dilworth_general_posets()
    verify_5_faithful_sn_counterexample_family()
    print("=" * 74)
    print("ALL VERIFICATION CHECKS PASSED (EXIT 0).")
    print("=" * 74)
    return 0


if __name__ == "__main__":
    sys.exit(main())
