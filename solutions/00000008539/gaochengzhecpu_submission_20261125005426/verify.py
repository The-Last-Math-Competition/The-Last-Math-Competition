#!/usr/bin/env python3
"""
Independent computational verification for Conjecture 00000008539
(The Last Math Competition).

Verifies from first principles using only the Python 3.12 standard library:
1. Incidence algebra construction I(P, Z) and two-sided inverse mu * zeta = delta = zeta * mu.
2. Geometric lattice axioms (finite lattice, atomistic, covering rank, submodularity)
   and Boolean lattice axioms (distributivity and complementation) across an extensive
   suite of Boolean and non-Boolean geometric lattices:
     B_0, B_1, B_2, B_3, B_4, M_3, M_4, M_5, U_{3,4}, U_{3,5}, U_{4,5},
     Pi_4 (partition lattice), PG(2, 2) (Fano plane), and M_3 x B_1.
3. Weisner's identity, Rota's strict sign theorem, and the characterization
   IsBooleanLattice(L) <=> |mu(bot, top)| == 1.
4. Explicit disproofs and structural classifications across all natural conventions:
   - Convention I (Unsigned Whitney numbers of the first kind w_k^+(L)):
     Global equality fails on B_n for all n >= 2 (e.g. B_2 gives (1, 2, 1), 2^2 = 4 != 1)
     and indeed fails on EVERY geometric lattice of rank >= 2.
   - Convention II (Maximal-chain elementwise |mu(0, c_k)|, rank-average w_k^+/W_k,
     rank-min, and rank-max):
     Boolean lattices give (1, ..., 1) with global equality, while EVERY non-Boolean
     geometric lattice fails log-concavity (e.g. M_3 gives (1, 1, 2), 1^2 = 1 < 2).
   - Convention III (Binomial-normalized w_k^+(L) / C(n, k), ultra-log-concavity):
     Fails log-concavity on U_{3,4} (b = (1, 4/3, 2, 3), (4/3)^2 = 16/9 < 2).
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from math import comb
import sys


class FinitePosetLattice:
    """Explicit finite lattice built from a closure/flat system (subsets of a ground set)."""

    def __init__(self, name: str, flats: list[frozenset[int]]) -> None:
        self.name = name
        # Sort flats deterministically by cardinality then sorted tuple
        self.elems: list[frozenset[int]] = sorted(
            set(flats), key=lambda s: (len(s), tuple(sorted(s)))
        )
        assert len(self.elems) == len(flats), f"{name}: duplicate flats"
        self.n_elems = len(self.elems)
        self.idx = {x: i for i, x in enumerate(self.elems)}

        # Partial order: subset inclusion
        self.le = [
            [self.elems[i].issubset(self.elems[j]) for j in range(self.n_elems)]
            for i in range(self.n_elems)
        ]
        self.bot = 0
        self.top = self.n_elems - 1
        assert all(self.le[self.bot][i] for i in range(self.n_elems)), f"{name}: invalid bot"
        assert all(self.le[i][self.top] for i in range(self.n_elems)), f"{name}: invalid top"

        # Meet = set intersection (must belong to flats); Join = smallest flat containing union
        self.inf = [[0] * self.n_elems for _ in range(self.n_elems)]
        self.sup = [[0] * self.n_elems for _ in range(self.n_elems)]
        flat_set = set(self.elems)
        for i, a in enumerate(self.elems):
            for j, b in enumerate(self.elems):
                inter = a & b
                assert inter in flat_set, f"{name}: not closed under intersection"
                self.inf[i][j] = self.idx[inter]
                u = a | b
                uppers = [k for k, c in enumerate(self.elems) if u.issubset(c)]
                # Least upper bound must exist and be unique
                lubs = [k for k in uppers if all(self.le[k][m] for m in uppers)]
                assert len(lubs) == 1, f"{name}: join failed for {a}, {b}"
                self.sup[i][j] = lubs[0]

        # Covering relation x <. y
        self.covers = [[False] * self.n_elems for _ in range(self.n_elems)]
        for i in range(self.n_elems):
            for j in range(self.n_elems):
                if i != j and self.le[i][j]:
                    between = [
                        k
                        for k in range(self.n_elems)
                        if k != i and k != j and self.le[i][k] and self.le[k][j]
                    ]
                    self.covers[i][j] = len(between) == 0

        self.atoms = [i for i in range(self.n_elems) if self.covers[self.bot][i]]

        # Compute rank function via BFS/DFS along covers and verify grading
        self.rk = [-1] * self.n_elems
        self.rk[self.bot] = 0
        for i in range(self.n_elems):
            for j in range(self.n_elems):
                if self.covers[i][j]:
                    assert self.rk[i] >= 0
                    if self.rk[j] == -1:
                        self.rk[j] = self.rk[i] + 1
                    else:
                        assert self.rk[j] == self.rk[i] + 1, f"{name}: not graded"
        assert all(r >= 0 for r in self.rk), f"{name}: unranked element"
        self.rank = self.rk[self.top]

        # Incidence algebra: zeta, delta, and two-sided inverse mu
        self.zeta = [
            [1 if self.le[i][j] else 0 for j in range(self.n_elems)]
            for i in range(self.n_elems)
        ]
        self.delta = [
            [1 if i == j else 0 for j in range(self.n_elems)]
            for i in range(self.n_elems)
        ]
        self.mu = [[0] * self.n_elems for _ in range(self.n_elems)]
        for i in range(self.n_elems):
            self.mu[i][i] = 1
        for i in range(self.n_elems):
            for j in range(i + 1, self.n_elems):
                if self.le[i][j]:
                    self.mu[i][j] = -sum(
                        self.mu[i][k]
                        for k in range(i, j)
                        if self.le[i][k] and self.le[k][j]
                    )

    def verify_incidence_algebra(self) -> None:
        # Check both mu * zeta == delta and zeta * mu == delta
        for i in range(self.n_elems):
            for j in range(self.n_elems):
                mz = sum(self.mu[i][k] * self.zeta[k][j] for k in range(self.n_elems))
                zm = sum(self.zeta[i][k] * self.mu[k][j] for k in range(self.n_elems))
                assert mz == self.delta[i][j], f"{self.name}: (mu * zeta)[{i},{j}] != delta"
                assert zm == self.delta[i][j], f"{self.name}: (zeta * mu)[{i},{j}] != delta"
                if not self.le[i][j]:
                    assert self.mu[i][j] == 0, f"{self.name}: mu supported outside order"

    def verify_geometric_lattice(self) -> None:
        # 1. Atomistic: every element is the join of atoms below it
        for x in range(self.n_elems):
            cur = self.bot
            for p in self.atoms:
                if self.le[p][x]:
                    cur = self.sup[cur][p]
            assert cur == x, f"{self.name}: not atomistic at {x}"
        # 2. Submodularity: rk(x v y) + rk(x ^ y) <= rk(x) + rk(y)
        for x in range(self.n_elems):
            for y in range(self.n_elems):
                lhs = self.rk[self.sup[x][y]] + self.rk[self.inf[x][y]]
                rhs = self.rk[x] + self.rk[y]
                assert lhs <= rhs, f"{self.name}: submodularity failed at {x}, {y}"

    def is_boolean(self) -> bool:
        # Distributive + complemented
        for x in range(self.n_elems):
            for y in range(self.n_elems):
                for z in range(self.n_elems):
                    if self.inf[x][self.sup[y][z]] != self.sup[self.inf[x][y]][self.inf[x][z]]:
                        return False
        for x in range(self.n_elems):
            if not any(
                self.inf[x][y] == self.bot and self.sup[x][y] == self.top
                for y in range(self.n_elems)
            ):
                return False
        return True

    def verify_weisner_and_rota(self) -> None:
        # Weisner's identity for all a > bot and all y
        for a in range(1, self.n_elems):
            for y in range(self.n_elems):
                s = sum(
                    self.mu[self.bot][x]
                    for x in range(self.n_elems)
                    if self.sup[x][a] == y
                )
                assert s == 0, f"{self.name}: Weisner failed for a={a}, y={y}"
        # Rota's strict sign theorem
        for x in range(self.n_elems):
            signed = ((-1) ** self.rk[x]) * self.mu[self.bot][x]
            assert signed >= 1, f"{self.name}: Rota sign theorem failed at {x}"

    def whitney1_abs(self) -> list[int]:
        return [
            sum(
                abs(self.mu[self.bot][x])
                for x in range(self.n_elems)
                if self.rk[x] == k
            )
            for k in range(self.rank + 1)
        ]

    def whitney2(self) -> list[int]:
        return [
            sum(1 for x in range(self.n_elems) if self.rk[x] == k)
            for k in range(self.rank + 1)
        ]

    def maximal_chains(self) -> list[list[int]]:
        chains: list[list[int]] = []

        def dfs(cur: int, path: list[int]) -> None:
            if cur == self.top:
                chains.append(list(path))
                return
            for nxt in range(self.n_elems):
                if self.covers[cur][nxt]:
                    path.append(nxt)
                    dfs(nxt, path)
                    path.pop()

        dfs(self.bot, [self.bot])
        assert len(chains) >= 1
        return chains


def build_uniform(r: int, m: int, name: str | None = None) -> FinitePosetLattice:
    """Lattice of flats of the uniform matroid U_{r, m}."""
    ground = list(range(m))
    flats = [
        frozenset(s)
        for k in range(r)
        for s in itertools.combinations(ground, k)
    ]
    flats.append(frozenset(ground))
    return FinitePosetLattice(name or f"U_{{{r},{m}}}", flats)


def build_boolean(n: int) -> FinitePosetLattice:
    return build_uniform(n, n, f"B_{n}")


def build_partition_pi4() -> FinitePosetLattice:
    """Partition lattice Pi_4 represented as flats of the graphic matroid K_4 (6 edges)."""
    edges = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    # A subset of edges of K_4 is a flat iff it is transitively closed on {0,1,2,3}
    flats: list[frozenset[int]] = []
    for r in range(len(edges) + 1):
        for comb_idx in itertools.combinations(range(len(edges)), r):
            chosen = {edges[k] for k in comb_idx}
            # Check transitive closure
            adj = [[i == j for j in range(4)] for i in range(4)]
            for u, v in chosen:
                adj[u][v] = adj[v][u] = True
            for k in range(4):
                for i in range(4):
                    for j in range(4):
                        adj[i][j] = adj[i][j] or (adj[i][k] and adj[k][j])
            closed = {
                idx
                for idx, (u, v) in enumerate(edges)
                if adj[u][v]
            }
            if closed == set(comb_idx):
                flats.append(frozenset(comb_idx))
    assert len(flats) == 15  # Bell number B(4) = 15
    return FinitePosetLattice("Pi_4", flats)


def build_fano_pg22() -> FinitePosetLattice:
    """Lattice of flats of the Fano plane PG(2, 2) on {1..7}."""
    pts = list(range(1, 8))
    lines = [
        frozenset({1, 2, 3}),
        frozenset({1, 4, 5}),
        frozenset({1, 6, 7}),
        frozenset({2, 4, 6}),
        frozenset({2, 5, 7}),
        frozenset({3, 4, 7}),
        frozenset({3, 5, 6}),
    ]
    flats: list[frozenset[int]] = [frozenset()]
    flats.extend(frozenset({p}) for p in pts)
    flats.extend(lines)
    flats.append(frozenset(pts))
    return FinitePosetLattice("PG(2,2)", flats)


def build_product(L1: FinitePosetLattice, L2: FinitePosetLattice) -> FinitePosetLattice:
    """Direct product of two flat lattices via disjoint union of ground sets."""
    offset = max((max(f, default=-1) for f in L1.elems), default=-1) + 1
    flats = [
        f1 | frozenset(x + offset for x in f2)
        for f1 in L1.elems
        for f2 in L2.elems
    ]
    return FinitePosetLattice(f"{L1.name} x {L2.name}", flats)


def is_log_concave(seq: list[Fraction | int]) -> bool:
    r = len(seq) - 1
    return all(seq[k] * seq[k] >= seq[k - 1] * seq[k + 1] for k in range(1, r))


def is_global_eq(seq: list[Fraction | int]) -> bool:
    r = len(seq) - 1
    return all(seq[k] * seq[k] == seq[k - 1] * seq[k + 1] for k in range(1, r))


def main() -> int:
    suite: list[FinitePosetLattice] = [
        build_boolean(0),
        build_boolean(1),
        build_boolean(2),
        build_boolean(3),
        build_boolean(4),
        build_uniform(2, 3, "M_3"),
        build_uniform(2, 4, "M_4"),
        build_uniform(2, 5, "M_5"),
        build_uniform(3, 4, "U_{3,4}"),
        build_uniform(3, 5, "U_{3,5}"),
        build_uniform(4, 5, "U_{4,5}"),
        build_partition_pi4(),
        build_fano_pg22(),
        build_product(build_uniform(2, 3, "M_3"), build_boolean(1)),
    ]

    print("=" * 78)
    print("Verification of Conjecture 00000008539 across 14 Geometric Lattices")
    print("=" * 78)

    for L in suite:
        L.verify_incidence_algebra()
        L.verify_geometric_lattice()
        L.verify_weisner_and_rota()

        boolean_flag = L.is_boolean()
        abs_mu_top = abs(L.mu[L.bot][L.top])
        # Verify exact Boolean characterization: IsBoolean <=> |mu(0, 1)| == 1
        assert boolean_flag == (abs_mu_top == 1), (
            f"{L.name}: Boolean={boolean_flag} vs |mu(0,1)|={abs_mu_top}"
        )

        w1 = L.whitney1_abs()
        w2 = L.whitney2()
        assert w1[0] == 1, f"{L.name}: first term w_0^+ != 1"
        assert is_log_concave(w1), f"{L.name}: w_k^+ failed log-concavity"

        # Convention I check: global equality holds iff rank <= 1
        w1_glob_eq = is_global_eq(w1)
        assert w1_glob_eq == (L.rank <= 1), (
            f"{L.name}: unexpected global equality status for w_k^+"
        )

        # Convention II checks: chains, rank-averages, rank-min, rank-max
        chains = L.maximal_chains()
        chain_seqs = [[abs(L.mu[L.bot][x]) for x in ch] for ch in chains]
        avg_seq = [Fraction(w1[k], w2[k]) for k in range(L.rank + 1)]
        min_seq = [
            min(abs(L.mu[L.bot][x]) for x in range(L.n_elems) if L.rk[x] == k)
            for k in range(L.rank + 1)
        ]
        max_seq = [
            max(abs(L.mu[L.bot][x]) for x in range(L.n_elems) if L.rk[x] == k)
            for k in range(L.rank + 1)
        ]

        if boolean_flag:
            for cseq in chain_seqs:
                assert cseq == [1] * (L.rank + 1)
                assert is_log_concave(cseq) and is_global_eq(cseq)
            assert is_log_concave(avg_seq) and is_global_eq(avg_seq)
            assert is_log_concave(min_seq) and is_global_eq(min_seq)
            assert is_log_concave(max_seq) and is_global_eq(max_seq)
        else:
            for cseq in chain_seqs:
                assert not is_log_concave(cseq), (
                    f"{L.name}: non-Boolean chain unexpectedly log-concave: {cseq}"
                )
            assert not is_log_concave(avg_seq), f"{L.name}: avg unexpectedly log-concave"
            assert not is_log_concave(min_seq), f"{L.name}: min unexpectedly log-concave"
            assert not is_log_concave(max_seq), f"{L.name}: max unexpectedly log-concave"

        # Convention III check: binomial-normalized w_k^+ / C(rank, k)
        ulc_seq = [Fraction(w1[k], comb(L.rank, k)) for k in range(L.rank + 1)]
        ulc_ok = is_log_concave(ulc_seq)

        print(
            f"{L.name:12s} | rk={L.rank} | |L|={L.n_elems:2d} | Bool={str(boolean_flag):5s} "
            f"| w^+={str(w1):20s} | w^+_globEq={str(w1_glob_eq):5s} "
            f"| chain_LC={str(boolean_flag):5s} | ULC={str(ulc_ok):5s}"
        )

    # Explicit headline counterexample assertions matching Lean 4 theorems
    b2 = next(L for L in suite if L.name == "B_2")
    assert b2.is_boolean() and b2.whitney1_abs() == [1, 2, 1]
    assert not is_global_eq(b2.whitney1_abs())  # 2^2 = 4 != 1 * 1

    m3 = next(L for L in suite if L.name == "M_3")
    assert not m3.is_boolean() and m3.whitney1_abs() == [1, 3, 2]
    for ch in m3.maximal_chains():
        cseq = [abs(m3.mu[m3.bot][x]) for x in ch]
        assert cseq == [1, 1, 2] and not is_log_concave(cseq)  # 1^2 = 1 < 1 * 2

    u34 = next(L for L in suite if L.name == "U_{3,4}")
    assert u34.whitney1_abs() == [1, 4, 6, 3]
    u34_ulc = [Fraction(u34.whitney1_abs()[k], comb(3, k)) for k in range(4)]
    assert u34_ulc == [Fraction(1), Fraction(4, 3), Fraction(2), Fraction(3)]
    assert not is_log_concave(u34_ulc)  # (4/3)^2 = 16/9 < 2

    print("-" * 78)
    print("ALL CHECKS PASSED:")
    print("  [1] Incidence algebra two-sided inversion verified on all 14 geometric lattices.")
    print("  [2] Weisner's identity, Rota's sign theorem, and Boolean <=> |mu(0,1)|=1 verified.")
    print("  [3] Disproof under Convention I (w_k^+): B_2 gives (1, 2, 1), 2^2 = 4 != 1.")
    print("  [4] Disproof under Convention II (chain/avg/min/max |mu|): M_3 gives (1, 1, 2), 1^2 < 2.")
    print("  [5] Disproof under Convention III (ultra-log-concavity): U_{3,4} gives (4/3)^2 = 16/9 < 2.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
