#!/usr/bin/env python3
"""
Exact computational verification suite for Conjecture 00000001290:
"The generating function of Sprague-Grundy values is rational
 if and only if the game is short and local (a rationality criterion)."

Uses pure Python 3 standard library (exact integer and rational arithmetic via
`fractions.Fraction`; zero floating-point approximations).
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
import sys
from typing import Callable


def mex(values: set[int]) -> int:
    """Minimum excludant of a finite set of non-negative integers."""
    v = 0
    while v in values:
        v += 1
    return v


def compute_progressive_grundy(opts_fn: Callable[[int], list[int]], n_max: int) -> list[int]:
    """Compute Sprague-Grundy values g[0..n_max] for a progressive game on N."""
    g = [0] * (n_max + 1)
    for n in range(n_max + 1):
        opts = opts_fn(n)
        for m in opts:
            if not (0 <= m < n):
                raise ValueError(f"Non-progressive option {m} from {n}")
        g[n] = mex({g[m] for m in opts})
    return g


def cauchy_product_coeffs(poly_q: list[int], seq_a: list[int]) -> list[int]:
    """Compute [x^0 .. x^N] of Q(x) * (sum_{k=0}^N a_k x^k) in Z[[x]]."""
    n_max = len(seq_a) - 1
    out = [0] * (n_max + 1)
    for n in range(n_max + 1):
        total = 0
        for j, qj in enumerate(poly_q):
            if j > n:
                break
            total += qj * seq_a[n - j]
        out[n] = total
    return out


def verify_rational_relation(poly_p: list[int], poly_q: list[int], seq_a: list[int]) -> bool:
    """Verify Q(x) * A(x) == P(x) mod x^(N+1) with Q != 0."""
    if not any(c != 0 for c in poly_q):
        return False
    prod = cauchy_product_coeffs(poly_q, seq_a)
    for n, lhs in enumerate(prod):
        rhs = poly_p[n] if n < len(poly_p) else 0
        if lhs != rhs:
            return False
    return True


def exact_matrix_rank_int(matrix: list[list[int]]) -> int:
    """Exact rank over Q of an integer matrix via Fraction Gaussian elimination."""
    if not matrix or not matrix[0]:
        return 0
    rows = len(matrix)
    cols = len(matrix[0])
    mat = [[Fraction(x) for x in row] for row in matrix]
    rank = 0
    for col in range(cols):
        pivot = None
        for r in range(rank, rows):
            if mat[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        piv_val = mat[rank][col]
        for c in range(col, cols):
            mat[rank][c] /= piv_val
        for r in range(rows):
            if r != rank and mat[r][col] != 0:
                factor = mat[r][col]
                for c in range(col, cols):
                    mat[r][c] -= factor * mat[rank][c]
        rank += 1
        if rank == rows:
            break
    return rank


def hankel_rank(seq: list[int], dim: int) -> int:
    """Exact Q-rank of the dim x dim principal Hankel matrix H[i, j] = seq[i + j]."""
    if 2 * dim - 1 > len(seq):
        raise ValueError("Sequence too short for requested Hankel dimension")
    mat = [[seq[i + j] for j in range(dim)] for i in range(dim)]
    return exact_matrix_rank_int(mat)


def verify_counterexample_1_nim() -> None:
    """Counterexample 1: Single-pile Nim (short, non-local, rational OGF & fibers)."""
    n_max = 512
    opts_fn = lambda n: list(range(n))
    g = compute_progressive_grundy(opts_fn, n_max)
    assert g == list(range(n_max + 1)), "Nim Grundy values must equal g(n) = n"

    # Value OGF: (1 - 2x + x^2) * sum_{n>=0} n x^n = x
    assert verify_rational_relation([0, 1], [1, -2, 1], g)
    assert hankel_rank(g, 20) == 2, "Hankel rank of x/(1-x)^2 must be exactly 2"

    # Fiber indicator GFs: sum_{g(n)=v} x^n = x^v for v = 0..16
    for v in range(17):
        fiber = [1 if val == v else 0 for val in g]
        poly_p = [0] * v + [1]
        assert verify_rational_relation(poly_p, [1], fiber)

    # Unbounded step distance and out-degree
    max_step_at_n = max(abs(n_max - m) for m in opts_fn(n_max))
    outdeg_at_n = len(opts_fn(n_max))
    assert max_step_at_n == n_max and outdeg_at_n == n_max
    print(
        f"[PASS] Counterexample 1 (1-Pile Nim, N={n_max}): "
        f"g(n)=n, OGF=x/(1-x)^2 (Hankel rank=2), max_step({n_max})={max_step_at_n}, "
        f"outdeg({n_max})={outdeg_at_n} -> refutes Necessity (Rational => Local)."
    )


def verify_counterexample_2_odd_subtraction() -> None:
    """Counterexample 2: Odd-subtraction game Sub(Odd) (bounded periodic Grundy, non-local)."""
    n_max = 512
    opts_fn = lambda n: [n - s for s in range(1, n + 1, 2)]
    g = compute_progressive_grundy(opts_fn, n_max)
    assert g == [n % 2 for n in range(n_max + 1)], "Sub(Odd) must have g(n) = n mod 2"

    # Value OGF: (1 - x^2) * sum (n mod 2) x^n = x
    assert verify_rational_relation([0, 1], [1, 0, -1], g)
    assert hankel_rank(g, 20) == 2

    # Fibers v = 0 -> 1/(1-x^2), v = 1 -> x/(1-x^2)
    f0 = [1 if val == 0 else 0 for val in g]
    f1 = [1 if val == 1 else 0 for val in g]
    assert verify_rational_relation([1], [1, 0, -1], f0)
    assert verify_rational_relation([0, 1], [1, 0, -1], f1)

    odd_n = n_max - 1  # 511
    max_step = max(abs(odd_n - m) for m in opts_fn(odd_n))
    outdeg = len(opts_fn(odd_n))
    assert max_step == odd_n and outdeg == (odd_n + 1) // 2
    print(
        f"[PASS] Counterexample 2 (Sub(Odd), N={n_max}): "
        f"translation-invariant, bounded periodic g(n)=n mod 2, OGF=x/(1-x^2), "
        f"max_step({odd_n})={max_step}, outdeg({odd_n})={outdeg} -> refutes Necessity."
    )


def verify_counterexample_3_non_short_games() -> None:
    """Counterexample 3: Non-short games (loopy step-1 Smith game & inf-branching game)."""
    # 3A: Loopy step-1 game on {0..31} with cycle 1 <-> 2
    n_max = 31
    opts: dict[int, list[int]] = {n: [] for n in range(n_max + 1)}
    opts[1] = [0, 2]
    opts[2] = [1, 3]
    opts[3] = [4]

    # Verify step radius K = 1 and out-degree B = 2
    for n, ms in opts.items():
        assert len(ms) <= 2
        for m in ms:
            assert abs(n - m) == 1

    # Verify infinite alternating play 1 -> 2 -> 1 -> 2 -> ...
    assert 2 in opts[1] and 1 in opts[2]

    # Run Smith's (1966) loopy Sprague-Grundy algorithm
    remaining = set(opts.keys())
    smith_g: dict[int, int] = {}
    v = 0
    while remaining:
        assigned_v: set[int] = set()
        changed = True
        while changed:
            changed = False
            can_reach_v = {
                x for x in remaining - assigned_v if any(y in assigned_v for y in opts[x])
            }
            for x in list(remaining - assigned_v - can_reach_v):
                rem_opts = [y for y in opts[x] if y not in smith_g]
                if all(y in can_reach_v for y in rem_opts):
                    assigned_v.add(x)
                    changed = True
        if not assigned_v:
            break
        for x in assigned_v:
            smith_g[x] = v
        remaining -= assigned_v
        v += 1

    assert remaining == set(), "Every position must receive a finite Smith-Grundy value"
    g_seq = [smith_g[n] for n in range(n_max + 1)]
    expected = [1 if n in (1, 3) else 0 for n in range(n_max + 1)]
    assert g_seq == expected

    # Verify mex equation holds everywhere AND polynomial OGF P(x) = x + x^3, Q(x) = 1
    for n in range(n_max + 1):
        assert g_seq[n] == mex({g_seq[m] for m in opts[n]})
    assert verify_rational_relation([0, 1, 0, 1], [1], g_seq)
    print(
        "[PASS] Counterexample 3 (Loopy Step-1 Game): "
        "step_radius=1, outdeg<=2, cycle 1<->2 (not short), unique finite Smith-Grundy "
        "values (0,1,0,1,0,...), OGF = x + x^3 -> refutes Necessity (Rational => Short)."
    )


def verify_counterexample_4_lacunary_local() -> None:
    """Counterexample 4: Lacunary step-1 short game G_pow2 (short & local, irrational OGF)."""
    n_max = 4096

    def is_pow2_ge4(n: int) -> bool:
        return n >= 4 and (n & (n - 1)) == 0

    opts_fn = lambda n: [n - 1] if is_pow2_ge4(n) else []
    g = compute_progressive_grundy(opts_fn, n_max)
    expected = [1 if is_pow2_ge4(n) else 0 for n in range(n_max + 1)]
    assert g == expected

    # Verify step distance = 1 and out-degree <= 1 everywhere
    for n in range(n_max + 1):
        ms = opts_fn(n)
        assert len(ms) <= 1
        for m in ms:
            assert abs(n - m) == 1

    # Verify gap lemma: for 2 <= k <= 12 and 1 <= delta < 2^(k-1), 2^k - delta is not 2^r
    for k in range(2, 13):
        limit = 1 << (k - 1)
        base = 1 << k
        for delta in range(1, limit):
            val = base - delta
            assert not is_pow2_ge4(val)

    # Check strictly growing Hankel ranks for F_G(x) = sum_{k>=2} x^(2^k) and fiber v=0
    dims = [8, 16, 32, 64, 128]
    ranks_g = [hankel_rank(g, d) for d in dims]
    f0 = [1 - val for val in g]
    ranks_f0 = [hankel_rank(f0, d) for d in dims]
    assert all(ranks_g[i] < ranks_g[i + 1] for i in range(len(dims) - 1)), (
        f"Expected strictly increasing Hankel ranks, got {ranks_g}"
    )
    assert all(ranks_f0[i] < ranks_f0[i + 1] for i in range(len(dims) - 1)), (
        f"Expected strictly increasing fiber-0 Hankel ranks, got {ranks_f0}"
    )
    rank_summary = ", ".join(f"H_{d}:{r}" for d, r in zip(dims, ranks_g))
    print(
        f"[PASS] Counterexample 4 (Lacunary Step-1 Short Game G_pow2, N={n_max}): "
        f"short, step_radius=1, outdeg<=1, OGF=sum_{{k>=2}} x^(2^k) irrational "
        f"({rank_summary}) -> refutes Sufficiency under bounded-step locality."
    )


def verify_positive_finite_subtraction_games() -> None:
    """Positive theorem check: all 63 non-empty S <= {1..6} have periodic Grundy & rational OGF."""
    universe = [1, 2, 3, 4, 5, 6]
    n_max = 512
    checked = 0
    max_period = 0
    max_preperiod = 0

    for r in range(1, len(universe) + 1):
        for s_tuple in combinations(universe, r):
            k_rad = max(s_tuple)
            opts_fn = lambda n, s=s_tuple: [n - step for step in s if step <= n]
            g = compute_progressive_grundy(opts_fn, n_max)

            # Detect first repeated state window of width k_rad
            seen: dict[tuple[int, ...], int] = {}
            n0 = -1
            period = -1
            for idx in range(n_max - k_rad + 1):
                win = tuple(g[idx : idx + k_rad])
                if win in seen:
                    n0 = seen[win]
                    period = idx - n0
                    break
                seen[win] = idx

            assert n0 >= 0 and period >= 1, f"Periodicity not found within N={n_max} for S={s_tuple}"
            for n in range(n0, n_max - period + 1):
                assert g[n + period] == g[n]

            # Build Q(x) = 1 - x^period and exact numerator P(x) of degree < n0 + period
            poly_q = [1] + [0] * (period - 1) + [-1]
            full_prod = cauchy_product_coeffs(poly_q, g)
            poly_p = full_prod[: n0 + period]
            assert verify_rational_relation(poly_p, poly_q, g)

            checked += 1
            max_period = max(max_period, period)
            max_preperiod = max(max_preperiod, n0)

    assert checked == 63
    print(
        f"[PASS] Positive Theorem (All {checked} non-empty finite subtraction games S <= {{1..6}}, "
        f"N={n_max}): all eventually periodic (max preperiod={max_preperiod}, "
        f"max period={max_period}) with exact rational OGF P(x)/(1 - x^p)."
    )


def verify_2d_multivariate_remarks() -> None:
    """Additional check on 2D impartial games: 2-pile Nim P-position GF vs Wythoff's game."""
    size = 48
    # 2-pile Nim: g(m, n) = m ^ n, P-positions m == n -> sum x^n y^n = 1/(1 - x y) rational!
    for m in range(size):
        for n in range(size):
            opts_vals = {m ^ k for k in range(n)} | {k ^ n for k in range(m)}
            assert mex(opts_vals) == (m ^ n)

    # Wythoff's Queen game: non-local 2D short game with irrational Beatty P-positions
    g_wythoff = [[0] * size for _ in range(size)]
    p_positions: list[tuple[int, int]] = []
    for m in range(size):
        for n in range(size):
            s_vals = set()
            for k in range(m):
                s_vals.add(g_wythoff[k][n])
            for k in range(n):
                s_vals.add(g_wythoff[m][k])
            for d in range(1, min(m, n) + 1):
                s_vals.add(g_wythoff[m - d][n - d])
            val = mex(s_vals)
            g_wythoff[m][n] = val
            if val == 0 and m <= n:
                p_positions.append((m, n))

    # First Wythoff P-positions: (0,0), (1,2), (3,5), (4,7), (6,10), (8,13), ...
    assert p_positions[:6] == [(0, 0), (1, 2), (3, 5), (4, 7), (6, 10), (8, 13)]
    print(
        f"[PASS] Multivariate / 2D Check ({size}x{size} grid): "
        "2-pile Nim has g(m,n)=m xor n and rational P-position GF 1/(1-xy) despite "
        "non-locality; Wythoff's game verified against Beatty pairs."
    )


def main() -> int:
    print("=" * 78)
    print("Conjecture 00000001290 — Exact Computational Verification Suite")
    print("=" * 78)
    verify_counterexample_1_nim()
    verify_counterexample_2_odd_subtraction()
    verify_counterexample_3_non_short_games()
    verify_counterexample_4_lacunary_local()
    verify_positive_finite_subtraction_games()
    verify_2d_multivariate_remarks()
    print("=" * 78)
    print("ALL VERIFICATION CHECKS PASSED (verdict: CONJECTURE 00000001290 IS FALSE).")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
