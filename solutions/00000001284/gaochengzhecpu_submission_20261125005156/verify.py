#!/usr/bin/env python3
"""
Independent computational verification for Conjecture 00000001284:
  Nim-multiplication on N, Frobenius bijectivity of x |-> x (*) x,
  Interpretation A (nim-square density = 1), and
  Interpretation B (ordinary squares in the nim-square sequence have
  density Theta(N^{-1/2}) -> 0, refuting (log N)^{-1/2} decay).
"""

import math
import sys


def nim_mul_mex_table(limit: int) -> list[list[int]]:
    """Conway's recursive impartial-game mex definition of Nim-multiplication."""
    tbl = [[0] * limit for _ in range(limit)]
    for x in range(limit):
        for y in range(limit):
            excluded = set()
            for xp in range(x):
                for yp in range(y):
                    excluded.add(tbl[xp][y] ^ tbl[x][yp] ^ tbl[xp][yp])
            m = 0
            while m in excluded:
                m += 1
            tbl[x][y] = m
    return tbl


def nim_mul_k(k: int, x: int, y: int) -> int:
    """Quadratic finite-field tower multiplication on F_k = [0, 2^(2^k))."""
    if k == 0:
        return (x & 1) * (y & 1)
    shift = 1 << (k - 1)       # 2^(k-1)
    m_prev = 1 << shift        # M_{k-1} = 2^(2^(k-1))
    p_prev = m_prev >> 1       # P_{k-1} = M_{k-1} / 2
    mask = m_prev - 1
    x1, x0 = x >> shift, x & mask
    y1, y0 = y >> shift, y & mask
    p11 = nim_mul_k(k - 1, x1, y1)
    p10 = nim_mul_k(k - 1, x1, y0)
    p01 = nim_mul_k(k - 1, x0, y1)
    p00 = nim_mul_k(k - 1, x0, y0)
    high = p11 ^ p10 ^ p01
    low = p00 ^ nim_mul_k(k - 1, p_prev, p11)
    return (high << shift) | low


def tier(n: int) -> int:
    k = 0
    while n >= (1 << (1 << k)):
        k += 1
    return k


def nim_mul(x: int, y: int) -> int:
    k = max(tier(x), tier(y))
    return nim_mul_k(k, x, y)


def nim_inv_k(k: int, x: int) -> int:
    if k == 0:
        return x & 1
    shift = 1 << (k - 1)
    m_prev = 1 << shift
    p_prev = m_prev >> 1
    mask = m_prev - 1
    x1, x0 = x >> shift, x & mask
    norm = nim_mul_k(k - 1, x0, x0) ^ nim_mul_k(k - 1, x0, x1) ^ nim_mul_k(
        k - 1, p_prev, nim_mul_k(k - 1, x1, x1)
    )
    inv_n = nim_inv_k(k - 1, norm)
    return (nim_mul_k(k - 1, inv_n, x1) << shift) | nim_mul_k(k - 1, inv_n, x0 ^ x1)


def nim_sqrt_k(k: int, y: int) -> int:
    if k == 0:
        return y & 1
    shift = 1 << (k - 1)
    m_prev = 1 << shift
    p_prev = m_prev >> 1
    mask = m_prev - 1
    y1, y0 = y >> shift, y & mask
    s1 = nim_sqrt_k(k - 1, y1)
    s0 = nim_sqrt_k(k - 1, y0 ^ nim_mul_k(k - 1, p_prev, y1))
    return (s1 << shift) | s0


def nim_sq(x: int) -> int:
    k = tier(x)
    return nim_mul_k(k, x, x)


def nim_sqrt(y: int) -> int:
    k = tier(y)
    return nim_sqrt_k(k, y)


def main() -> int:
    print("=== Conjecture 00000001284 Independent Verification ===\n")

    # 1. Agreement between Conway's recursive mex and the quadratic field tower on [0, 64)^2
    mex_tbl = nim_mul_mex_table(64)
    for x in range(64):
        for y in range(64):
            got = nim_mul(x, y)
            assert got == mex_tbl[x][y], f"Mex/tower mismatch at ({x}, {y}): {got} != {mex_tbl[x][y]}"
    print("[PASS] Conway recursive mex == quadratic field tower on all 64 x 64 = 4,096 pairs.")

    # 2. Explicit 16x16 table and non-vacuity checks
    print("\n16 x 16 Nim-multiplication table on F_2 = [0, 16):")
    for x in range(16):
        row = " ".join(f"{mex_tbl[x][y]:2d}" for y in range(16))
        print(f"  {x:2d} | {row}")

    expected_samples = {
        (2, 2): 3,
        (3, 3): 2,
        (2, 3): 1,
        (4, 4): 6,
        (4, 15): 1,
        (8, 8): 13,
        (15, 15): 9,
    }
    for (a, b), val in expected_samples.items():
        assert nim_mul(a, b) == val, f"Sample {a} (*) {b} != {val}"
    first_16_sq = [nim_sq(x) for x in range(16)]
    assert first_16_sq == [0, 1, 3, 2, 6, 7, 5, 4, 13, 12, 14, 15, 11, 10, 8, 9]
    print(f"\n[PASS] Explicit samples and first 16 nim-squares verified: {first_16_sq}")

    # 3. Field axioms on F_2 = [0, 16) (full triples) and F_3 = [0, 256) (inverses & zero-divisors)
    for x in range(16):
        for y in range(16):
            for z in range(16):
                assert mex_tbl[mex_tbl[x][y]][z] == mex_tbl[x][mex_tbl[y][z]], "Associativity failed"
                assert mex_tbl[x][y ^ z] == (mex_tbl[x][y] ^ mex_tbl[x][z]), "Distributivity failed"
    for x in range(1, 256):
        inv_x = nim_inv_k(3, x)
        assert 0 < inv_x < 256, "Inverse out of F_3"
        assert nim_mul_k(3, x, inv_x) == 1, f"Inverse failed at x={x}"
    for k in range(4):
        mk = 1 << (1 << k)
        pk = mk >> 1
        assert nim_mul(mk, mk) == mk + pk, f"Fermat self-square failed at k={k}"
        for x in range(min(mk, 256)):
            assert nim_mul(mk, x) == mk * x, f"Fermat scalar rule failed at k={k}, x={x}"
            assert (nim_sq(x) ^ x) < pk, f"Artin-Schreier bound failed at k={k}, x={x}"
    print("[PASS] Field axioms, inverses on F_3 = [0, 256), Fermat 2-power rules, and Artin-Schreier bounds verified.")

    # 4. Constructive Frobenius inverse up to 2^16 and fast linear extension up to N_MAX = 2^20
    for x in range(65536):
        s = nim_mul_k(4, x, x)
        assert nim_sqrt_k(4, s) == x, f"nim_sqrt(nim_sq({x})) != {x}"
    print("[PASS] Constructive bijection (nimSq, nimSqrt) verified on all [0, 65536).")

    max_d = 20
    n_max = 1 << max_d  # 1,048,576
    basis = [nim_mul_k(5, 1 << j, 1 << j) for j in range(max_d)]
    sq_seq = [0] * n_max
    for j in range(max_d):
        step = 1 << j
        b = basis[j]
        for prev in range(step):
            sq_seq[step + prev] = sq_seq[prev] ^ b

    # Spot-check linear basis DP against recursive nim_sq
    for x in [0, 1, 7, 15, 16, 255, 256, 4096, 65535, 65536, 524287, 1048575]:
        assert sq_seq[x] == nim_sq(x)

    # Verify dyadic interval preservation x < 2^d <=> x (*) x < 2^d for all d <= 20
    for d in range(max_d + 1):
        limit = 1 << d
        seen = bytearray(limit)
        for x in range(limit):
            y = sq_seq[x]
            assert y < limit, f"Dyadic closure failed at d={d}, x={x}, y={y}"
            seen[y] = 1
        assert sum(seen) == limit, f"Surjectivity failed on [0, 2^{d})"
    print(f"[PASS] Dyadic bijection [0, 2^d) -> [0, 2^d) verified for all 0 <= d <= {max_d} (up to N = {n_max:,}).")

    # 5. Interpretation A: Nim-square density = 1 (unrestricted) and > 1/2 (restricted x < N)
    # Build inverse permutation on [0, 2^20)
    inv_sq = [0] * n_max
    for x, y in enumerate(sq_seq):
        inv_sq[y] = x
    # As N grows from 1 to n_max, track R_count(N) = |{y < N : inv_sq[y] < N}|
    r_cnt = 0
    for n in range(1, n_max + 1):
        # Going from N = n-1 to N = n:
        # 1) y = n - 1 enters the range y < N; check if inv_sq[n - 1] < n
        if inv_sq[n - 1] < n:
            r_cnt += 1
        # 2) x = n - 1 enters the witness range x < N; check if sq_seq[n - 1] < n - 1 (avoiding double count if sq_seq[n-1] == n-1)
        y_new = sq_seq[n - 1]
        if y_new < n - 1:
            r_cnt += 1
        assert 2 * r_cnt > n, f"Restricted nim-square bound failed at N={n}: r_cnt={r_cnt}"
        if (n & (n - 1)) == 0:
            assert r_cnt == n, f"Dyadic restricted nim-square count != N at N={n}"
    print(f"[PASS] Interpretation A verified across all 1 <= N <= {n_max:,}:")
    print("       Unrestricted nim-square density = 1 identically; restricted witness proportion > 1/2 for all N >= 1 and = 1 at all N = 2^d.")

    # 6. Interpretation B: Ordinary squares in s(x) = x (*) x across all 1 <= N <= 2^20
    is_ord_sq = bytearray(n_max)
    m = 0
    while m * m < n_max:
        is_ord_sq[m * m] = 1
        m += 1

    c_cnt = 0
    min_norm = (1e9, 0)
    max_norm = (0.0, 0)
    print("\nInterpretation B summary table (C(N) = |{0 <= x < N : x (*) x is an ordinary square}|):")
    print("       N |   C(N) |    D(N)=C/N |     N^{-1/2} | C(N)/sqrt(N) | (log2 N)^{-1/2} | D(N)/(log2 N)^{-1/2}")
    print("  -------+--------+-------------+--------------+--------------+-----------------+---------------------")

    checkpoints = set()
    for d in range(1, max_d + 1):
        checkpoints.add(1 << d)
        if d >= 3:
            checkpoints.add(3 << (d - 1))  # midpoint 1.5 * 2^d

    for n in range(1, n_max + 1):
        c_cnt += is_ord_sq[sq_seq[n - 1]]
        # Verify Lean all-N polynomial bounds: N < 2 * C(N)^2 and C(N)^2 < 8 * N
        assert n < 2 * c_cnt * c_cnt, f"Lower bound N < 2*C(N)^2 failed at N={n}"
        assert c_cnt * c_cnt < 8 * n, f"Upper bound C(N)^2 < 8*N failed at N={n}"

        norm = c_cnt / math.sqrt(n)
        if norm < min_norm[0]:
            min_norm = (norm, n)
        if norm > max_norm[0]:
            max_norm = (norm, n)

        # Check exact dyadic formula at powers of 2
        if (n & (n - 1)) == 0:
            expected_ceil = math.isqrt(n - 1) + 1
            assert c_cnt == expected_ceil, f"Dyadic formula failed at N={n}: {c_cnt} != {expected_ceil}"

        if n in checkpoints and (n in {2, 4, 8, 16, 64, 256, 1024, 4096, 16384, 65536, 262144, 786432, 1048576}):
            d_n = c_cnt / n
            inv_sqrt_n = 1.0 / math.sqrt(n)
            inv_sqrt_log = 1.0 / math.sqrt(math.log2(n))
            ratio_log = d_n / inv_sqrt_log
            print(
                f"  {n:7d} | {c_cnt:6d} | {d_n:11.6f} | {inv_sqrt_n:12.6f} | "
                f"{norm:12.6f} | {inv_sqrt_log:15.6f} | {ratio_log:19.6f}"
            )

    print(f"\n[PASS] Interpretation B verified across all 1 <= N <= {n_max:,}:")
    print(f"       Uniform polynomial bounds 1/sqrt(2) < C(N)/sqrt(N) < 2*sqrt(2) hold for all N (observed min={min_norm[0]:.6f} at N={min_norm[1]}, max={max_norm[0]:.6f} at N={max_norm[1]}).")
    print("       At N = 2^20 = 1,048,576: D(N) = 1/1024 = 0.000977 = N^{-1/2}, whereas (log2 N)^{-1/2} = 0.223607 (ratio = 0.004367 -> 0).")
    print("\nALL VERIFICATION CHECKS PASSED.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
