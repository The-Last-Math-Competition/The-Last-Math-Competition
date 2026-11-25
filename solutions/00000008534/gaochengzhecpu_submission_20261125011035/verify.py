#!/usr/bin/env python3
"""
Independent computational verification for Conjecture 00000008534
(Whitney log-concavity, unimodularity, and flat strata of geometric lattices).

Exit code 0 iff all geometric lattice axioms, Mobius/Whitney computations,
total-unimodularity / binary-representability checks, and counterexample
assertions pass unconditionally.
"""

from __future__ import annotations
import itertools
import sys
from fractions import Fraction


class FiniteLattice:
    """Finite lattice constructed from a closed family of flat bitmasks."""

    def __init__(self, name: str, ground_size: int, flat_masks: list[int]) -> None:
        self.name = name
        self.ground_size = ground_size
        # Deduplicate and sort by popcount then value
        self.masks = sorted(set(flat_masks), key=lambda m: (m.bit_count(), m))
        self.size = len(self.masks)
        self.idx_of = {m: i for i, m in enumerate(self.masks)}
        assert 0 in self.idx_of, f"{name}: bottom mask 0 missing"
        full = (1 << ground_size) - 1
        assert full in self.idx_of, f"{name}: top mask {full} missing"
        self.bot = self.idx_of[0]
        self.top = self.idx_of[full]

        # Precompute le, meet, join
        self.le = [
            [(self.masks[i] & self.masks[j]) == self.masks[i] for j in range(self.size)]
            for i in range(self.size)
        ]
        self.meet = [[0] * self.size for _ in range(self.size)]
        self.join = [[0] * self.size for _ in range(self.size)]
        for i in range(self.size):
            for j in range(self.size):
                inter = self.masks[i] & self.masks[j]
                assert inter in self.idx_of, f"{name}: flats not closed under intersection"
                self.meet[i][j] = self.idx_of[inter]
                union = self.masks[i] | self.masks[j]
                supers = [m for m in self.masks if (m & union) == union]
                assert supers, f"{name}: no upper bound for join"
                least = supers[0]
                for s in supers:
                    assert (s & least) == least, f"{name}: no unique least upper bound"
                self.join[i][j] = self.idx_of[least]

        # Cover relation and Jordan-Dedekind rank via BFS from bottom
        self.covers = [[False] * self.size for _ in range(self.size)]
        for x in range(self.size):
            for y in range(self.size):
                if x != y and self.le[x][y]:
                    between = any(
                        z != x and z != y and self.le[x][z] and self.le[z][y]
                        for z in range(self.size)
                    )
                    self.covers[x][y] = not between

        self.rk = [-1] * self.size
        self.rk[self.bot] = 0
        queue = [self.bot]
        while queue:
            u = queue.pop(0)
            for v in range(self.size):
                if self.covers[u][v]:
                    if self.rk[v] == -1:
                        self.rk[v] = self.rk[u] + 1
                        queue.append(v)
                    else:
                        assert self.rk[v] == self.rk[u] + 1, f"{name}: grading failed"
        assert all(r >= 0 for r in self.rk), f"{name}: disconnected Hasse diagram"
        self.rank = self.rk[self.top]

    def verify_geometric_lattice_axioms(self) -> None:
        n = self.size
        # 1. Partial order
        for x in range(n):
            assert self.le[x][x]
            assert self.le[self.bot][x] and self.le[x][self.top]
        for x in range(n):
            for y in range(n):
                if self.le[x][y] and self.le[y][x]:
                    assert x == y
                if self.le[x][y] and x != y:
                    assert self.rk[x] < self.rk[y]
                if self.covers[x][y]:
                    assert self.rk[y] == self.rk[x] + 1
        for x in range(n):
            for y in range(n):
                for z in range(n):
                    if self.le[x][y] and self.le[y][z]:
                        assert self.le[x][z]
                    assert self.le[self.join[x][y]][z] == (self.le[x][z] and self.le[y][z])
                    assert self.le[z][self.meet[x][y]] == (self.le[z][x] and self.le[z][y])
        # 2. Upper semimodularity
        for x in range(n):
            for y in range(n):
                assert (
                    self.rk[self.join[x][y]] + self.rk[self.meet[x][y]]
                    <= self.rk[x] + self.rk[y]
                ), f"{self.name}: semimodularity failed at ({x}, {y})"
        # 3. Atomicity
        atoms = [a for a in range(n) if self.covers[self.bot][a]]
        assert atoms == [a for a in range(n) if self.rk[a] == 1]
        for x in range(n):
            for u in range(n):
                if all((not self.le[a][x]) or self.le[a][u] for a in atoms):
                    assert self.le[x][u], f"{self.name}: atomicity failed at ({x}, {u})"

    def is_modular(self) -> bool:
        return all(
            self.rk[self.join[x][y]] + self.rk[self.meet[x][y]]
            == self.rk[x] + self.rk[y]
            for x in range(self.size)
            for y in range(self.size)
        )

    def whitney_second(self) -> list[int]:
        return [sum(1 for x in range(self.size) if self.rk[x] == k) for k in range(self.rank + 1)]

    def mobius_from_bot(self) -> list[int]:
        mu = [0] * self.size
        order = sorted(range(self.size), key=lambda x: self.rk[x])
        for x in order:
            if x == self.bot:
                mu[x] = 1
            else:
                mu[x] = -sum(mu[y] for y in range(self.size) if y != x and self.le[y][x])
        # Verify defining Mobius identity
        assert mu[self.bot] == 1
        for x in range(self.size):
            if x != self.bot:
                assert sum(mu[y] for y in range(self.size) if self.le[y][x]) == 0
        return mu

    def whitney_first_signed(self) -> list[int]:
        mu = self.mobius_from_bot()
        return [
            sum(mu[x] for x in range(self.size) if self.rk[x] == k)
            for k in range(self.rank + 1)
        ]

    def whitney_first_unsigned(self) -> list[int]:
        return [abs(v) for v in self.whitney_first_signed()]


def uniform_lattice(r: int, n: int, name: str | None = None) -> FiniteLattice:
    masks = [0, (1 << n) - 1]
    for k in range(1, r):
        for comb in itertools.combinations(range(n), k):
            m = 0
            for idx in comb:
                m |= 1 << idx
            masks.append(m)
    return FiniteLattice(name or f"L(U_{{{r},{n}}})", n, masks)


def fano_lattice() -> FiniteLattice:
    pts = [v for v in itertools.product([0, 1], repeat=3) if any(v)]
    lines = []
    for i, j in itertools.combinations(range(7), 2):
        s = tuple((pts[i][t] ^ pts[j][t]) for t in range(3))
        k = pts.index(s)
        lines.append((1 << i) | (1 << j) | (1 << k))
    masks = [0, (1 << 7) - 1] + [1 << i for i in range(7)] + lines
    return FiniteLattice("PG(2,2)", 7, masks)


def det_int(mat: list[list[int]]) -> int:
    k = len(mat)
    if k == 0:
        return 1
    if k == 1:
        return mat[0][0]
    if k == 2:
        return mat[0][0] * mat[1][1] - mat[0][1] * mat[1][0]
    total = 0
    for j in range(k):
        minor = [[mat[r][c] for c in range(k) if c != j] for r in range(1, k)]
        sign = 1 if j % 2 == 0 else -1
        total += sign * mat[0][j] * det_int(minor)
    return total


def is_totally_unimodular(A: list[list[int]]) -> bool:
    m = len(A)
    n = len(A[0]) if m else 0
    for k in range(1, min(m, n) + 1):
        for rows in itertools.combinations(range(m), k):
            for cols in itertools.combinations(range(n), k):
                sub = [[A[r][c] for c in cols] for r in rows]
                if det_int(sub) not in (-1, 0, 1):
                    return False
    return True


def rank_over_q(cols_vecs: list[list[int]]) -> int:
    if not cols_vecs:
        return 0
    mat = [[Fraction(x) for x in v] for v in cols_vecs]
    R, C = len(mat), len(mat[0])
    r = 0
    for c in range(C):
        piv = next((i for i in range(r, R) if mat[i][c] != 0), None)
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        pv = mat[r][c]
        mat[r] = [x / pv for x in mat[r]]
        for i in range(R):
            if i != r and mat[i][c] != 0:
                f = mat[i][c]
                mat[i] = [mat[i][j] - f * mat[r][j] for j in range(C)]
        r += 1
    return r


def represents_lattice_over_q(L: FiniteLattice, A: list[list[int]]) -> bool:
    m = len(A)
    n = len(A[0]) if m else 0
    atoms = [a for a in range(L.size) if L.rk[a] == 1]
    if len(atoms) != n:
        return False
    for mask in range(1 << n):
        chosen_cols = [[A[r][j] for r in range(m)] for j in range(n) if (mask >> j) & 1]
        lin_rk = rank_over_q(chosen_cols)
        cur = L.bot
        for j in range(n):
            if (mask >> j) & 1:
                cur = L.join[cur][atoms[j]]
        if lin_rk != L.rk[cur]:
            return False
    return True


def lc_flats(seq: list[int]) -> list[int]:
    return [k for k in range(1, len(seq) - 1) if seq[k] * seq[k] == seq[k - 1] * seq[k + 1]]


def is_log_concave(seq: list[int]) -> bool:
    return all(seq[k] * seq[k] >= seq[k - 1] * seq[k + 1] for k in range(1, len(seq) - 1))


def is_strictly_log_concave(seq: list[int]) -> bool:
    return all(seq[k] * seq[k] > seq[k - 1] * seq[k + 1] for k in range(1, len(seq) - 1))


def plateau_flats(seq: list[int]) -> list[int]:
    return [k for k in range(len(seq) - 1) if seq[k] == seq[k + 1]]


def verify_exhaustive_m4_non_unimodular(M4: FiniteLattice) -> tuple[int, int]:
    """Exhaustively check all 2^8 GF(2) 2x4 matrices and all 3^8 {-1,0,1} 2x4 matrices."""
    gf2_checked = 0
    for entries in itertools.product((0, 1), repeat=8):
        gf2_checked += 1
        A = [list(entries[:4]), list(entries[4:])]
        all_pairs_odd = all(
            (A[0][i] * A[1][j] - A[0][j] * A[1][i]) % 2 != 0
            for i, j in itertools.combinations(range(4), 2)
        )
        assert not all_pairs_odd, "Found impossible GF(2) representation of U_{2,4}!"

    tu_checked = 0
    for entries in itertools.product((-1, 0, 1), repeat=8):
        tu_checked += 1
        A = [list(entries[:4]), list(entries[4:])]
        if is_totally_unimodular(A):
            assert not represents_lattice_over_q(M4, A), "Found impossible TU rep of M4!"

    return gf2_checked, tu_checked


def verify_u35_non_binary() -> int:
    """Verify no normalized [I_3 | v_3 | v_4] over GF(2) has all 10 triples independent."""
    checked = 0
    I3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    for v3 in itertools.product((0, 1), repeat=3):
        for v4 in itertools.product((0, 1), repeat=3):
            checked += 1
            cols = I3 + [list(v3), list(v4)]
            all_indep = True
            for i, j, k in itertools.combinations(range(5), 3):
                sub = [[cols[i][r], cols[j][r], cols[k][r]] for r in range(3)]
                if det_int(sub) % 2 == 0:
                    all_indep = False
                    break
            assert not all_indep, "Found impossible GF(2) representation of U_{3,5}!"
    return checked


def main() -> int:
    print("=== Conjecture 00000008534 Independent Verification ===\n")

    lattices = {
        "B1": uniform_lattice(1, 1, "B1 = L(U_{1,1})"),
        "B2": uniform_lattice(2, 2, "B2 = L(U_{2,2})"),
        "M3": uniform_lattice(2, 3, "M3 = L(U_{2,3})"),
        "M4": uniform_lattice(2, 4, "M4 = L(U_{2,4})"),
        "B3": uniform_lattice(3, 3, "B3 = L(U_{3,3})"),
        "LU34": uniform_lattice(3, 4, "L(U_{3,4})"),
        "LU35": uniform_lattice(3, 5, "L(U_{3,5})"),
        "F7": fano_lattice(),
    }

    for key, L in lattices.items():
        L.verify_geometric_lattice_axioms()

    # 1. Verify positive unimodular representations
    tu_reps = {
        "B1": [[1]],
        "B2": [[1, 0], [0, 1]],
        "M3": [[1, 0, 1], [0, 1, 1]],
        "B3": [[1, 0, 0], [0, 1, 0], [0, 0, 1]],
        "LU34": [[1, 0, 0, 1], [0, 1, 0, 1], [0, 0, 1, 1]],
    }
    for key, A in tu_reps.items():
        L = lattices[key]
        assert is_totally_unimodular(A), f"{key}: matrix not totally unimodular"
        assert represents_lattice_over_q(L, A), f"{key}: matrix does not represent {L.name}"

    # 2. Verify M4 and U_{3,5} non-unimodularity / non-binary property
    gf2_n, tu_n = verify_exhaustive_m4_non_unimodular(lattices["M4"])
    u35_n = verify_u35_non_binary()
    print(f"[PASS] Exhaustive M4 non-binary check ({gf2_n} GF(2) matrices) "
          f"and TU check ({tu_n} matrices in {{-1,0,1}}^{{2x4}}).")
    print(f"[PASS] Exhaustive normalized U_{{3,5}} non-binary check ({u35_n} column pairs).\n")

    # 3. Verify expected Whitney sequences and flat properties
    expected = {
        "B1": ([1, 1], [1, 1], True),
        "B2": ([1, 2, 1], [1, 2, 1], True),
        "M3": ([1, 3, 1], [1, 3, 2], True),
        "M4": ([1, 4, 1], [1, 4, 3], True),
        "B3": ([1, 3, 3, 1], [1, 3, 3, 1], True),
        "LU34": ([1, 4, 6, 1], [1, 4, 6, 3], False),
        "LU35": ([1, 5, 10, 1], [1, 5, 10, 6], False),
        "F7": ([1, 7, 7, 1], [1, 7, 14, 8], True),
    }

    print(f"{'Lattice':16s} | {'Mod':3s} | {'W(L)':15s} | {'|w(L)|':15s} | {'LC_flats(W/|w|)':15s} | {'Plateaus(W/|w|)'}")
    print("-" * 92)
    for key, (exp_W, exp_w, exp_mod) in expected.items():
        L = lattices[key]
        W = L.whitney_second()
        w = L.whitney_first_unsigned()
        mod = L.is_modular()
        assert W == exp_W, f"{key}: expected W={exp_W}, got {W}"
        assert w == exp_w, f"{key}: expected |w|={exp_w}, got {w}"
        assert mod == exp_mod, f"{key}: expected modular={exp_mod}, got {mod}"
        assert is_log_concave(W) and is_log_concave(w)
        assert is_strictly_log_concave(W) and is_strictly_log_concave(w)
        fW, fw = lc_flats(W), lc_flats(w)
        pW, pw = plateau_flats(W), plateau_flats(w)
        print(f"{L.name:16s} | {str(mod):3s} | {str(W):15s} | {str(w):15s} | "
              f"{str(fW)}/{str(fw):10s} | {pW}/{pw}")

    # 4. Assert core counterexample conclusions across all conventions
    M4 = lattices["M4"]
    assert lc_flats(M4.whitney_second()) == []
    assert lc_flats(M4.whitney_first_unsigned()) == []
    assert plateau_flats(M4.whitney_second()) == []
    assert plateau_flats(M4.whitney_first_unsigned()) == []

    LU35 = lattices["LU35"]
    assert not LU35.is_modular()
    assert lc_flats(LU35.whitney_second()) == []
    assert lc_flats(LU35.whitney_first_unsigned()) == []
    assert plateau_flats(LU35.whitney_second()) == []
    assert plateau_flats(LU35.whitney_first_unsigned()) == []

    B3 = lattices["B3"]
    assert plateau_flats(B3.whitney_second()) == [1]
    assert plateau_flats(B3.whitney_first_unsigned()) == [1]

    LU34 = lattices["LU34"]
    assert not LU34.is_modular()
    assert lc_flats(LU34.whitney_second()) == []
    assert plateau_flats(LU34.whitney_second()) == []

    print("\n[ALL CHECKS PASSED] Conjecture 00000008534 is disproved across all conventions.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
