#!/usr/bin/env python3
"""
Standalone exact-arithmetic verification suite for Conjecture 00000008533
(The LYM inequality and Mobius-function weightings on finite geometric lattices).

Verifies using Python's exact `fractions.Fraction` and integer bitmask arithmetic:
  1. Full geometric-lattice axioms (bounded lattice, Jordan-Dedekind grading,
     upper semimodularity, and atomisticity) and both left/right Mobius inversion
     identities on all concrete witness lattices (`B_3`, `L_10`, `L_34`, `L_46`, `L_922`).
  2. Positive Theorem (Lubell chain-probability LYM): exact validity (<= 1) and
     rank-level tightness (== 1) via exact max-flow / min-cut.
  3. Refutation of classical rank-uniform LYM (`1 / W_{rk(x)}`):
     `L_34 = L(U_{2,5} +_{e_0} U_{2,6})` (|L| = 34, rank 3) achieves `111/110 > 1`.
  4. Refutation of constant-tightness for global and proper-global `|mu|` normalizations:
     strictly `< 1` maximum antichain weight (`5/12 < 1` and `5/9 < 1` on `L_10`).
  5. Refutation of rank-normalized two-sided `|mu(0, x) mu(x, 1)|` LYM:
     `L_46 = L(U_{1,1} + U_{3,6})` (|L| = 46, rank 4) achieves `66/65 > 1`.
  6. Refutation of rank-normalized upper `|mu(x, 1)|` LYM:
     `L_922 = L(U_{3,8} +_{e_0} U_{3,8})` (|L| = 922, rank 5) achieves `23788/23725 > 1`.
  7. Refutation of optimality for rank-normalized lower `|mu(0, x)| / |w_{rk(x)}|`:
     on `L_10 = B_1 x M_3` (|L| = 10, rank 3), `min_{L^o} w_low = 1/5 < 2/9 < 1/4 = min_{L^o} w_unif`,
     failing Sperner maximin optimality, pointwise dominance, and L^1 uniqueness.
"""

from collections import deque
from fractions import Fraction
from itertools import combinations, product
from math import lcm
import sys


def build_direct_sum_coloop(r0: int, m: int):
    """Flats (as bitmasks on 1 + m elements; bit 0 is the coloop) of U_{1,1} + U_{r0, m}."""
    n_atoms = 1 + m
    R = 1 + r0
    flats_by_rk = [[] for _ in range(R + 1)]
    for b0 in (0, 1):
        for k in range(r0):
            for comb_idx in combinations(range(1, m + 1), k):
                mask = b0
                for idx in comb_idx:
                    mask |= 1 << idx
                flats_by_rk[b0 + k].append(mask)
        full_rest = ((1 << m) - 1) << 1
        flats_by_rk[b0 + r0].append(b0 | full_rest)

    def cl_fn(mask: int) -> int:
        b0 = mask & 1
        rest = mask >> 1
        if rest.bit_count() >= r0:
            return b0 | (((1 << m) - 1) << 1)
        return mask

    return n_atoms, flats_by_rk, cl_fn


def build_parallel_conn_uniform(r0: int, a: int, b: int):
    """Flats (as bitmasks on 1 + a + b elements; bit 0 is basepoint e_0) of U_{r0,a+1} +_{e_0} U_{r0,b+1}."""
    n_atoms = 1 + a + b
    R = 2 * r0 - 1
    flats_by_rk = [[] for _ in range(R + 1)]
    mask_A = ((1 << a) - 1) << 1
    mask_B = ((1 << b) - 1) << (1 + a)

    # Flats not containing e_0: |S_A| < r0 and |S_B| < r0
    subs_A_no0 = [
        (k, sum(1 << i for i in c))
        for k in range(r0)
        for c in combinations(range(1, 1 + a), k)
    ]
    subs_B_no0 = [
        (k, sum(1 << j for j in c))
        for k in range(r0)
        for c in combinations(range(1 + a, 1 + a + b), k)
    ]
    for (ka, mA), (kb, mB) in product(subs_A_no0, subs_B_no0):
        flats_by_rk[ka + kb].append(mA | mB)

    # Flats containing e_0: (|S_A| + 1 < r0 or S_A = A) and (|S_B| + 1 < r0 or S_B = B)
    subs_A_w0 = [
        (k + 1, sum(1 << i for i in c))
        for k in range(r0 - 1)
        for c in combinations(range(1, 1 + a), k)
    ] + [(r0, mask_A)]
    subs_B_w0 = [
        (k + 1, sum(1 << j for j in c))
        for k in range(r0 - 1)
        for c in combinations(range(1 + a, 1 + a + b), k)
    ] + [(r0, mask_B)]
    for (rA, mA), (rB, mB) in product(subs_A_w0, subs_B_w0):
        flats_by_rk[rA + rB - 1].append(1 | mA | mB)

    def cl_fn(mask: int) -> int:
        b0 = mask & 1
        part_A = mask & mask_A
        part_B = mask & mask_B
        ca = part_A.bit_count()
        cb = part_B.bit_count()
        has0 = (b0 == 1) or (ca >= r0) or (cb >= r0)
        if not has0:
            return mask
        out_A = mask_A if ca + 1 >= r0 else part_A
        out_B = mask_B if cb + 1 >= r0 else part_B
        return 1 | out_A | out_B

    return n_atoms, flats_by_rk, cl_fn


def verify_geometric_lattice(name: str, n_atoms: int, flats_by_rk, cl_fn):
    """Exhaustively verify all geometric-lattice axioms on bitmask flats."""
    R = len(flats_by_rk) - 1
    elems = []
    rk = []
    rk_of = {}
    for r, fls in enumerate(flats_by_rk):
        for f in fls:
            assert f not in rk_of, f"{name}: duplicate flat {f}"
            rk_of[f] = r
            elems.append(f)
            rk.append(r)
    N = len(elems)
    full_mask = (1 << n_atoms) - 1

    # 1. Bot, Top, Singletons (atoms), and Closure fixed points
    assert rk_of.get(0) == 0, f"{name}: missing empty flat at rank 0"
    assert rk_of.get(full_mask) == R, f"{name}: missing full flat at rank {R}"
    for i in range(n_atoms):
        assert rk_of.get(1 << i) == 1, f"{name}: singleton {i} not a rank-1 atom"
    for f in elems:
        assert cl_fn(f) == f, f"{name}: flat {f} not closed"

    # 2. Atomisticity: every flat is exact bitwise OR of the rank-1 atoms below it
    atoms = [1 << i for i in range(n_atoms)]
    for f in elems:
        joined = 0
        for a in atoms:
            if (a & f) == a:
                joined |= a
        assert joined == f, f"{name}: atomisticity failed at {f}"

    # 3. Gradedness (strict rank monotonicity and intermediate step existence)
    for idx_x, x in enumerate(elems):
        rx = rk[idx_x]
        for idx_y, y in enumerate(elems):
            if x != y and (x & y) == x:
                ry = rk[idx_y]
                assert rx < ry, f"{name}: rank not strictly monotone for {x} < {y}"
                if rx + 1 < ry:
                    diff = y & ~x
                    lsb = diff & -diff
                    z = cl_fn(x | lsb)
                    assert z in rk_of and rk_of[z] == rx + 1 and (x & z) == x and (z & y) == z, (
                        f"{name}: Jordan-Dedekind step failed between {x} and {y}"
                    )

    # 4. Intersection closure and upper semimodularity across ALL N*(N-1)/2 pairs
    for i in range(N):
        xi = elems[i]
        rxi = rk[i]
        for j in range(i + 1, N):
            xj = elems[j]
            meet_ij = xi & xj
            join_ij = cl_fn(xi | xj)
            assert meet_ij in rk_of, f"{name}: not closed under intersection"
            assert join_ij in rk_of, f"{name}: join not in flats"
            assert rk_of[meet_ij] + rk_of[join_ij] <= rxi + rk[j], (
                f"{name}: upper semimodularity failed on {xi}, {xj}"
            )

    print(f"[OK] GeometricLattice axioms verified on {name:28s} (|L|={N:3d}, rank={R}, atoms={n_atoms})")
    return elems, rk, rk_of


def compute_and_verify_mobius_full(name: str, elems, rk):
    """Compute full Mobius matrix mu(x, y) and verify BOTH left/right inversion & sign alternation."""
    N = len(elems)
    R = max(rk)
    leq = [[(elems[i] & elems[j]) == elems[i] for j in range(N)] for i in range(N)]
    mu = [[0] * N for _ in range(N)]
    for i in range(N):
        mu[i][i] = 1
    for diff in range(1, R + 1):
        for i in range(N):
            ri = rk[i]
            for j in range(N):
                if rk[j] - ri == diff and leq[i][j]:
                    mu[i][j] = -sum(mu[i][k] for k in range(N) if k != j and leq[i][k] and leq[k][j])

    # Verify left and right zeta-inversion and Rota strict sign alternation
    for i in range(N):
        for j in range(N):
            if not leq[i][j]:
                assert mu[i][j] == 0
            else:
                expected = 1 if i == j else 0
                left_sum = sum(mu[i][k] for k in range(N) if leq[i][k] and leq[k][j])
                right_sum = sum(mu[k][j] for k in range(N) if leq[i][k] and leq[k][j])
                assert left_sum == expected, f"{name}: left Mobius inversion failed"
                assert right_sum == expected, f"{name}: right Mobius inversion failed"
                sign = -1 if ((rk[j] - rk[i]) % 2 == 1) else 1
                assert sign * mu[i][j] >= 1, f"{name}: Rota sign alternation failed"
    print(f"[OK] Full Mobius left/right inversion & Rota sign alternation verified on {name}")
    return leq, mu


def compute_mobius_endpoints_fast(name: str, elems, rk):
    """Compute mu(bot, x) and mu(x, top) and verify endpoint zeta-inversion on large lattices."""
    N = len(elems)
    R = max(rk)
    mu0 = [0] * N
    mu0[0] = 1
    for r in range(1, R + 1):
        for j in range(N):
            if rk[j] == r:
                ej = elems[j]
                mu0[j] = -sum(mu0[i] for i in range(N) if rk[i] < r and (elems[i] & ej) == elems[i])

    mu1 = [0] * N
    mu1[N - 1] = 1
    for r in range(R - 1, -1, -1):
        for i in range(N):
            if rk[i] == r:
                ei = elems[i]
                mu1[i] = -sum(mu1[j] for j in range(N) if rk[j] > r and (ei & elems[j]) == ei)

    # Check inversion at endpoints for every element
    for j in range(N):
        ej = elems[j]
        s0 = sum(mu0[i] for i in range(N) if (elems[i] & ej) == elems[i])
        assert s0 == (1 if j == 0 else 0)
        s1 = sum(mu1[k] for k in range(N) if (ej & elems[k]) == ej)
        assert s1 == (1 if j == N - 1 else 0)
        assert ((-1) ** rk[j]) * mu0[j] >= 1
        assert ((-1) ** (R - rk[j])) * mu1[j] >= 1
    print(f"[OK] Endpoint Mobius recursions & Rota sign alternation verified on {name}")
    return mu0, mu1


def max_weight_antichain_exact(elems, weights, indices=None):
    """Exact rational maximum-weight antichain via Dinic min-cut on comparability graph."""
    nodes = list(range(len(elems))) if indices is None else list(indices)
    m = len(nodes)
    denom_lcm = 1
    for u in nodes:
        denom_lcm = lcm(denom_lcm, weights[u].denominator)
    iw = [int(weights[u] * denom_lcm) for u in nodes]
    S, T = 2 * m, 2 * m + 1
    INF = sum(iw) + 1
    adj = [[] for _ in range(2 * m + 2)]
    cap = {}

    def add_edge(a: int, b: int, c: int):
        adj[a].append(b)
        adj[b].append(a)
        cap[(a, b)] = cap.get((a, b), 0) + c
        cap[(b, a)] = cap.get((b, a), 0)

    for idx_u, w in enumerate(iw):
        if w > 0:
            add_edge(S, idx_u, w)
            add_edge(m + idx_u, T, w)
    for i, u in enumerate(nodes):
        eu = elems[u]
        for j, v in enumerate(nodes):
            if u != v and (eu & elems[v]) == eu:
                add_edge(i, m + j, INF)

    flow = 0
    while True:
        lvl = [-1] * (2 * m + 2)
        lvl[S] = 0
        q = deque([S])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if lvl[y] == -1 and cap[(x, y)] > 0:
                    lvl[y] = lvl[x] + 1
                    q.append(y)
        if lvl[T] == -1:
            break
        it = [0] * (2 * m + 2)

        def dfs(x: int, pushed: int) -> int:
            if pushed == 0 or x == T:
                return pushed
            while it[x] < len(adj[x]):
                y = adj[x][it[x]]
                it[x] += 1
                if lvl[y] == lvl[x] + 1 and cap[(x, y)] > 0:
                    tr = dfs(y, min(pushed, cap[(x, y)]))
                    if tr > 0:
                        cap[(x, y)] -= tr
                        cap[(y, x)] += tr
                        return tr
            return 0

        while True:
            pushed = dfs(S, INF)
            if pushed == 0:
                break
            flow += pushed

    vis = [False] * (2 * m + 2)
    q = deque([S])
    vis[S] = True
    while q:
        x = q.popleft()
        for y in adj[x]:
            if not vis[y] and cap[(x, y)] > 0:
                vis[y] = True
                q.append(y)
    ac = [nodes[i] for i in range(m) if vis[i] and not vis[m + i]]
    for i in range(len(ac)):
        for j in range(i + 1, len(ac)):
            assert (elems[ac[i]] & elems[ac[j]]) != elems[ac[i]]
            assert (elems[ac[j]] & elems[ac[i]]) != elems[ac[j]]
    val = sum((weights[u] for u in ac), Fraction(0))
    assert val == Fraction(sum(iw) - flow, denom_lcm)
    return val, ac


def compute_lubell_weights(elems, rk):
    """Exact count of maximal chains through each element via DP along Hasse covers."""
    N = len(elems)
    R = max(rk)
    down = [0] * N
    down[0] = 1
    for r in range(1, R + 1):
        for j in range(N):
            if rk[j] == r:
                ej = elems[j]
                down[j] = sum(
                    down[i] for i in range(N) if rk[i] == r - 1 and (elems[i] & ej) == elems[i]
                )
    up = [0] * N
    up[N - 1] = 1
    for r in range(R - 1, -1, -1):
        for i in range(N):
            if rk[i] == r:
                ei = elems[i]
                up[i] = sum(
                    up[j] for j in range(N) if rk[j] == r + 1 and (ei & elems[j]) == ei
                )
    thru = [down[i] * up[i] for i in range(N)]
    tot = thru[0]
    assert tot >= 1 and tot == thru[N - 1]
    return tot, [Fraction(thru[i], tot) for i in range(N)]


def main() -> int:
    print("=== Exact Verification Suite for Conjecture 00000008533 ===\n")

    # Build concrete witness geometric lattices
    e_B3, rk_B3, _ = verify_geometric_lattice("B_3 (Boolean rank 3)", *build_direct_sum_coloop(2, 2))
    e_10, rk_10, _ = verify_geometric_lattice("L_10 = B_1 x M_3", *build_direct_sum_coloop(2, 3))
    e_34, rk_34, _ = verify_geometric_lattice("L_34 = PC(U_{2,5}, U_{2,6})", *build_parallel_conn_uniform(2, 4, 5))
    e_46, rk_46, _ = verify_geometric_lattice("L_46 = U_{1,1} + U_{3,6}", *build_direct_sum_coloop(3, 6))
    e_922, rk_922, _ = verify_geometric_lattice("L_922 = PC(U_{3,8}, U_{3,8})", *build_parallel_conn_uniform(3, 7, 7))

    print()
    _, mu_B3 = compute_and_verify_mobius_full("B_3", e_B3, rk_B3)
    _, mu_10 = compute_and_verify_mobius_full("L_10", e_10, rk_10)
    _, mu_34 = compute_and_verify_mobius_full("L_34", e_34, rk_34)
    _, mu_46 = compute_and_verify_mobius_full("L_46", e_46, rk_46)
    mu0_922, mu1_922 = compute_mobius_endpoints_fast("L_922", e_922, rk_922)

    # 1. Verify Positive Theorem: Lubell's chain-probability LYM inequality & tightness
    print("\n--- 1. Positive Theorem: Lubell Chain-Probability LYM ---")
    for lname, elems, rk in [("B_3", e_B3, rk_B3), ("L_10", e_10, rk_10), ("L_34", e_34, rk_34), ("L_46", e_46, rk_46)]:
        tot_c, w_lub = compute_lubell_weights(elems, rk)
        R = max(rk)
        for k in range(R + 1):
            rk_sum = sum((w_lub[i] for i in range(len(elems)) if rk[i] == k), Fraction(0))
            assert rk_sum == Fraction(1, 1), f"{lname}: rank {k} Lubell sum != 1"
        max_lub, _ = max_weight_antichain_exact(elems, w_lub)
        assert max_lub == Fraction(1, 1), f"{lname}: max Lubell antichain != 1"
        print(f"[OK] {lname:6s}: |C(L)| = {tot_c:4d}, all rank sums == 1, exact max antichain weight == 1")

    # 2. Verify Classical Rank-Uniform LYM Counterexample on L_34
    print("\n--- 2. Classical Rank-Uniform LYM Refutation on L_34 ---")
    W_34 = [sum(1 for r in rk_34 if r == k) for k in range(4)]
    assert W_34 == [1, 10, 22, 1]
    w_unif_34 = [Fraction(1, W_34[rk_34[i]]) for i in range(len(e_34))]
    ac_34 = [
        i for i in range(len(e_34))
        if (rk_34[i] == 1 and (e_34[i] & 1) == 1) or (rk_34[i] == 2 and (e_34[i] & 1) == 0)
    ]
    assert len(ac_34) == 21
    for a in ac_34:
        for b in ac_34:
            if a != b:
                assert (e_34[a] & e_34[b]) != e_34[a]
    sum_ac_34 = sum((w_unif_34[i] for i in ac_34), Fraction(0))
    max_34, _ = max_weight_antichain_exact(e_34, w_unif_34)
    assert sum_ac_34 == Fraction(111, 110) and max_34 == Fraction(111, 110)
    print(f"[OK] L_34: W = {W_34}, |A_34| = 21, sum(1/W_rk) = {sum_ac_34} > 1")

    # 3. Verify Global & Proper-Global |mu| Normalizations Have Strictly Improvable Constant (< 1)
    print("\n--- 3. Global & Proper-Global |mu| Normalizations (Constant < 1) ---")
    for lname, elems, rk, mu in [("B_3", e_B3, rk_B3, mu_B3), ("L_10", e_10, rk_10, mu_10), ("L_46", e_46, rk_46, mu_46)]:
        N = len(elems)
        R = max(rk)
        mu0_abs = [abs(mu[0][i]) for i in range(N)]
        tot_all = sum(mu0_abs)
        w_glob = [Fraction(mu0_abs[i], tot_all) for i in range(N)]
        max_glob, _ = max_weight_antichain_exact(elems, w_glob)
        assert max_glob < 1, f"{lname}: global |mu| max should be < 1"

        prop_idx = [i for i in range(N) if 1 <= rk[i] < R]
        tot_prop = sum(mu0_abs[i] for i in prop_idx)
        w_prop = [Fraction(mu0_abs[i], tot_prop) for i in range(N)]
        max_prop, _ = max_weight_antichain_exact(elems, w_prop, indices=prop_idx)
        assert max_prop < 1, f"{lname}: proper-global |mu| max should be < 1"
        print(f"[OK] {lname:6s}: max global |mu| = {str(max_glob):6s} < 1, max proper-global |mu| = {str(max_prop):6s} < 1")

    # 4. Verify Rank-Normalized Two-Sided |mu(0, x) mu(x, 1)| Refutation on L_46
    print("\n--- 4. Rank-Normalized Two-Sided |mu(0, x) mu(x, 1)| Refutation on L_46 ---")
    N46 = len(e_46)
    mup_46 = [abs(mu_46[0][i] * mu_46[i][N46 - 1]) for i in range(N46)]
    rk_sums_46 = [sum(mup_46[i] for i in range(N46) if rk_46[i] == k) for k in range(5)]
    assert rk_sums_46 == [10, 34, 39, 25, 10]
    w_two_46 = [Fraction(mup_46[i], rk_sums_46[rk_46[i]]) for i in range(N46)]
    ac_46 = [
        i for i in range(N46)
        if (rk_46[i] == 2 and (e_46[i] & 1) == 1) or (rk_46[i] == 3 and (e_46[i] & 1) == 0)
    ]
    assert len(ac_46) == 7
    for a in ac_46:
        for b in ac_46:
            if a != b:
                assert (e_46[a] & e_46[b]) != e_46[a]
    sum_ac_46 = sum((w_two_46[i] for i in ac_46), Fraction(0))
    max_46, _ = max_weight_antichain_exact(e_46, w_two_46)
    assert sum_ac_46 == Fraction(66, 65) and max_46 == Fraction(66, 65)
    print(f"[OK] L_46: two-sided rank sums = {rk_sums_46}, |A_46| = 7, sum = {sum_ac_46} > 1")

    # 5. Verify Rank-Normalized Upper |mu(x, 1)| Refutation on L_922
    print("\n--- 5. Rank-Normalized Upper |mu(x, 1)| Refutation on L_922 ---")
    N922 = len(e_922)
    mu1_abs_922 = [abs(x) for x in mu1_922]
    up_sums_922 = [sum(mu1_abs_922[i] for i in range(N922) if rk_922[i] == k) for k in range(6)]
    assert up_sums_922[3] == 1825 and up_sums_922[4] == 455
    w_up_922 = [Fraction(mu1_abs_922[i], up_sums_922[rk_922[i]]) for i in range(N922)]
    ac_922 = [
        i for i in range(N922)
        if (rk_922[i] == 3 and (e_922[i] & 1) == 1) or (rk_922[i] == 4 and (e_922[i] & 1) == 0)
    ]
    assert len(ac_922) == 492
    for idx_a in range(len(ac_922)):
        ea = e_922[ac_922[idx_a]]
        for idx_b in range(idx_a + 1, len(ac_922)):
            eb = e_922[ac_922[idx_b]]
            assert (ea & eb) != ea and (eb & ea) != eb
    sum_ac_922 = sum((w_up_922[i] for i in ac_922), Fraction(0))
    assert sum_ac_922 == Fraction(23788, 23725) and sum_ac_922 > 1
    print(f"[OK] L_922: upper rank sums (rk 3,4) = ({up_sums_922[3]}, {up_sums_922[4]}), |A_922| = 492, sum = {sum_ac_922} > 1")

    # 6. Verify Suboptimality of Rank-Normalized Lower |mu(0, x)| / |w_rk| on L_10 = B_1 x M_3
    print("\n--- 6. Suboptimality of Rank-Normalized Lower |mu(0, x)| on L_10 = B_1 x M_3 ---")
    N10 = len(e_10)
    W_10 = [sum(1 for r in rk_10 if r == k) for k in range(4)]
    mu0_10 = [abs(mu_10[0][i]) for i in range(N10)]
    w1_10 = [sum(mu0_10[i] for i in range(N10) if rk_10[i] == k) for k in range(4)]
    assert W_10 == [1, 4, 4, 1] and w1_10 == [1, 4, 5, 2]

    w_unif_10 = [Fraction(1, W_10[rk_10[i]]) for i in range(N10)]
    w_low_10 = [Fraction(mu0_10[i], w1_10[rk_10[i]]) for i in range(N10)]
    _, w_lub_10 = compute_lubell_weights(e_10, rk_10)

    assert max_weight_antichain_exact(e_10, w_unif_10)[0] == 1
    assert max_weight_antichain_exact(e_10, w_lub_10)[0] == 1
    assert max_weight_antichain_exact(e_10, w_low_10)[0] == 1

    proper_10 = [i for i in range(N10) if 1 <= rk_10[i] <= 2]
    min_low = min(w_low_10[i] for i in proper_10)
    min_lub = min(w_lub_10[i] for i in proper_10)
    min_unif = min(w_unif_10[i] for i in proper_10)
    assert min_low == Fraction(1, 5) < min_lub == Fraction(2, 9) < min_unif == Fraction(1, 4)
    assert sum(w_low_10) == sum(w_lub_10) == sum(w_unif_10) == Fraction(4, 1)
    print(f"[OK] L_10: W = {W_10}, |w| = {w1_10}, min proper weights: w_low = {min_low} < w_chain = {min_lub} < w_unif = {min_unif}")
    print("\nALL VERIFICATION CHECKS PASSED SUCCESSFULLY.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
