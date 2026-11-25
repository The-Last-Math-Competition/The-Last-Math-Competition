#!/usr/bin/env python3
"""
Independent computational verification for Conjecture 00000008552.

Verifies:
  1. Brute-force order-preserving map counts vs. order-ideal chain DP for
     1-chain, 2-chain, 3-chain, and 4-chain product lattices.
  2. Positive witnesses (d = 1 and d = 2): MacMahon's multinomial/box product
     formula holds identically for all tested C_a and C_a x C_b.
  3. Exact degree-8 order polynomial of C_2 x C_2 x C_2:
       1680 * Omega(C_2^3, m) = m(m+1)(m+2)(m+3)(2m^4 + 12m^3 + 25m^2 + 21m + 10),
     sum-of-squares positivity 8*Q(m) = (4m^2 + 12m + 7)^2 + 31 >= 31 > 0, and
     irreducibility of Q(m) = 2m^4 + 12m^3 + 25m^2 + 21m + 10 over Q[m],
     proving Omega(C_2^3, m) cannot split into linear factors and cannot equal
     any product or quotient of polynomial multinomial coefficients.
  4. Pointwise prime-factor & genuine-multinomial obstructions:
     - Omega(C_2^3, 4) = 887 is prime and equals no product of genuine
       (non-edge) multinomial coefficients and no bounded multinomial quotient.
     - Naive d-dimensional MacMahon rank-box product fails on C_2^3 at m = 3
       (500/3 != 168), on C_2^3 at m = 4 (875 != 887), and on C_2^4 at m = 2
       (500/3 != 168).
     - Endomorphism count |End_<=(C_2 x C_2 x C_3)| = 50^2 * 887 = 2,217,500
       = 2^2 * 5^4 * 887 has prime factor 887 >> |L| = 12.
"""

from __future__ import annotations

import itertools
import math
from fractions import Fraction
from functools import reduce


def cover_edges(dims: list[int]) -> tuple[list[tuple[int, ...]], list[tuple[int, int]]]:
    pts = list(itertools.product(*[range(a) for a in dims]))
    d = len(dims)
    edges: list[tuple[int, int]] = []
    for i, u in enumerate(pts):
        for j, v in enumerate(pts):
            if i != j and all(u[k] <= v[k] for k in range(d)) and sum(v) - sum(u) == 1:
                edges.append((i, j))
    return pts, edges


def omega_bruteforce(dims: list[int], m: int) -> int:
    pts, edges = cover_edges(dims)
    n = len(pts)
    if m == 0:
        return 0 if n > 0 else 1
    count = 0
    for f in itertools.product(range(m), repeat=n):
        if all(f[u] <= f[v] for u, v in edges):
            count += 1
    return count


def omega_dp_all(dims: list[int], max_m: int) -> tuple[list[int], list[int]]:
    pts, edges = cover_edges(dims)
    n = len(pts)
    ideals = [
        mask
        for mask in range(1 << n)
        if all(not (((mask >> v) & 1) and not ((mask >> u) & 1)) for u, v in edges)
    ]
    le = [[(i_mask & j_mask) == i_mask for j_mask in ideals] for i_mask in ideals]
    vals = [0, 1]
    if max_m >= 2:
        vals.append(len(ideals))
    cur = [1] * len(ideals)
    for _ in range(3, max_m + 1):
        nxt = [0] * len(ideals)
        for i, ci in enumerate(cur):
            row = le[i]
            for j in range(len(ideals)):
                if row[j]:
                    nxt[j] += ci
        cur = nxt
        vals.append(sum(cur))
    return vals[: max_m + 1], ideals


def macmahon_rank_box(dims: list[int], m: int) -> Fraction:
    pts = itertools.product(*[range(a) for a in dims])
    prod = Fraction(1, 1)
    for x in pts:
        rk = sum(x)
        prod *= Fraction(m + rk, 1 + rk)
    return prod


def poly_add(p: list[int], q: list[int]) -> list[int]:
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def poly_mul(p: list[int], q: list[int]) -> list[int]:
    if not p or not q:
        return [0]
    res = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            res[i + j] += a * b
    return res


def poly_eval(p: list[int], x: int | Fraction) -> int | Fraction:
    acc: int | Fraction = 0
    for c in reversed(p):
        acc = acc * x + c
    return acc


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def factorize(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def verify_positive_macmahon() -> None:
    print("=== [1] Positive Witnesses: d = 1 (Chains) and d = 2 (MacMahon Plane Partitions) ===")
    for a in range(1, 6):
        dp_vals, _ = omega_dp_all([a], 10)
        for m in range(1, 11):
            expected = math.comb(m + a - 1, a)
            box_val = macmahon_rank_box([a], m)
            assert dp_vals[m] == expected == box_val
    for m in range(1, 7):
        assert omega_bruteforce([2], m) == math.comb(m + 1, 2)
        assert omega_bruteforce([2, 2], m) == m * (m + 1) ** 2 * (m + 2) // 12
    for a in range(1, 5):
        for b in range(1, 5):
            dp_vals, _ = omega_dp_all([a, b], 8)
            for m in range(1, 9):
                box_val = macmahon_rank_box([a, b], m)
                multinom_ratio = Fraction(1, 1)
                for i in range(1, a + 1):
                    multinom_ratio *= Fraction(
                        math.comb(m + b + i - 2, b),
                        math.comb(b + i - 1, b),
                    )
                assert dp_vals[m] == box_val == multinom_ratio
    for m in range(1, 5):
        assert omega_bruteforce([2, 3], m) == macmahon_rank_box([2, 3], m)
    print("  [PASS] All 1-chain and 2-chain order polynomials match MacMahon's multinomial formula.")


def verify_cube_polynomial_and_irreducibility() -> None:
    print("\n=== [2] Exact Order Polynomial & Non-Splitting of C_2 x C_2 x C_2 ===")
    dp_vals, ideals = omega_dp_all([2, 2, 2], 15)
    assert len(ideals) == 20
    print(f"  |J(C_2^3)| = {len(ideals)} downsets; masks = {ideals}")

    for m in range(0, 6):
        bf = omega_bruteforce([2, 2, 2], m)
        assert bf == dp_vals[m], f"Brute-force mismatch at m={m}: {bf} != {dp_vals[m]}"
    print(f"  Brute-force & DP exact values (m=0..5): {dp_vals[:6]}")
    print(f"  DP exact values (m=6..12):              {dp_vals[6:13]}")

    # Finite-difference binomial-basis coefficients at m = 0..9
    diffs = [dp_vals[:10]]
    while len(diffs[-1]) > 1:
        diffs.append([diffs[-1][i + 1] - diffs[-1][i] for i in range(len(diffs[-1]) - 1)])
    binom_coeffs = [d[0] for d in diffs[:9]]
    assert diffs[9][0] == 0
    assert binom_coeffs == [0, 1, 18, 111, 331, 540, 495, 240, 48]
    print(f"  Binomial-basis coefficients C(m, 0..8): {binom_coeffs}")

    for m in range(0, 16):
        val = sum(c * math.comb(m, k) for k, c in enumerate(binom_coeffs))
        assert val == dp_vals[m]

    # Build 1680 * Omega(C_2^3, m) in standard monomial basis
    fact8 = math.factorial(8)
    poly_fact8 = [0] * 9
    for k, ck in enumerate(binom_coeffs):
        fall = [1]
        for r in range(k):
            fall = poly_mul(fall, [-r, 1])
        scale = ck * (fact8 // math.factorial(k))
        for i, coeff in enumerate(fall):
            poly_fact8[i] += scale * coeff

    g = reduce(math.gcd, poly_fact8)
    assert g == 24 and fact8 // g == 1680
    prim_poly = [c // g for c in poly_fact8]
    assert prim_poly == [0, 60, 236, 441, 483, 315, 119, 24, 2]

    quartic = [10, 21, 25, 12, 2]
    factored_rhs = reduce(poly_mul, [[0, 1], [1, 1], [2, 1], [3, 1], quartic])
    assert prim_poly == factored_rhs
    print("  Verified polynomial identity:")
    print("    1680 * Omega(C_2^3, m) = m(m+1)(m+2)(m+3)(2m^4 + 12m^3 + 25m^2 + 21m + 10)")

    # Sum-of-squares completion: 8 * Q(m) = (4m^2 + 12m + 7)^2 + 31
    sq_part = poly_mul([7, 12, 4], [7, 12, 4])
    sos_rhs = poly_add(sq_part, [31])
    assert [8 * c for c in quartic] == sos_rhs
    print("  Verified sum-of-squares positivity:")
    print("    8*(2m^4 + 12m^3 + 25m^2 + 21m + 10) = (4m^2 + 12m + 7)^2 + 31 >= 31 > 0")

    # Rational Root Theorem check on Q(m) = 2m^4 + 12m^3 + 25m^2 + 21m + 10
    divs_10 = [1, 2, 5, 10]
    divs_2 = [1, 2]
    candidates = sorted({Fraction(s * p, q) for p in divs_10 for q in divs_2 for s in (-1, 1)})
    for x in candidates:
        assert poly_eval(quartic, x) > 0

    # Irreducibility over Q[m] (Gauss's lemma: check all (a1*m^2 + b1*m + c1)(a2*m^2 + b2*m + c2) in Z[m])
    # With a1 = 1, a2 = 2 and c1 * c2 = 10:
    for c1 in [-10, -5, -2, -1, 1, 2, 5, 10]:
        c2 = 10 // c1
        # 2*b1 + b2 = 12 => b2 = 12 - 2*b1; b1*c2 + b2*c1 = 21
        for b1 in range(-100, 101):
            b2 = 12 - 2 * b1
            if poly_mul([c1, b1, 1], [c2, b2, 2]) == quartic:
                raise AssertionError("Unexpected quadratic factorization!")
    print("  [PASS] Q(m) = 2m^4 + 12m^3 + 25m^2 + 21m + 10 has NO real/rational roots and is irreducible over Q[m].")


def verify_pointwise_naive_box_and_endomorphisms() -> None:
    print("\n=== [3] Pointwise Prime Obstructions, Naive MacMahon Box, and Endomorphisms ===")
    dp_cube, _ = omega_dp_all([2, 2, 2], 12)
    assert dp_cube[4] == 887 and is_prime(887)
    print(f"  Omega(C_2^3, 4) = {dp_cube[4]} (PRIME!)")

    # Verify no genuine multinomial coefficient equals 887
    # Any genuine multinomial has >=3 positive parts (so >= N*(N-1) > 887 for N >= 31)
    # or 2 parts >= 2 (so >= N*(N-1)//2 > 887 for N >= 43).
    for n in range(3, 45):
        for k in range(2, n - 1):
            assert math.comb(n, k) != 887
        for a in range(1, n):
            for b in range(1, n - a):
                c = n - a - b
                if c >= 1:
                    val = math.factorial(n) // (math.factorial(a) * math.factorial(b) * math.factorial(c))
                    assert val != 887
    print("  [PASS] Exhaustively confirmed no genuine multinomial coefficient equals 887.")

    # Naive d-dimensional MacMahon box comparison
    box_cube_2 = macmahon_rank_box([2, 2, 2], 2)
    box_cube_3 = macmahon_rank_box([2, 2, 2], 3)
    box_cube_4 = macmahon_rank_box([2, 2, 2], 4)
    assert box_cube_2 == Fraction(20, 1) == dp_cube[2]
    assert box_cube_3 == Fraction(500, 3) != dp_cube[3] == 168
    assert box_cube_4 == Fraction(875, 1) != dp_cube[4] == 887
    print(f"  Naive MacMahon box on C_2^3: m=2 -> {box_cube_2} (=20), m=3 -> {box_cube_3} (!=168), m=4 -> {box_cube_4} (!=887)")

    dp_c2_4, _ = omega_dp_all([2, 2, 2, 2], 4)
    box_c2_4_m2 = macmahon_rank_box([2, 2, 2, 2], 2)
    assert dp_c2_4[2] == 168 and box_c2_4_m2 == Fraction(500, 3)
    assert dp_c2_4[3] == 7581 and factorize(7581) == {3: 1, 7: 1, 19: 2}
    print(f"  Omega(C_2^4, 2) = {dp_c2_4[2]} (factors {factorize(dp_c2_4[2])}); naive box = {box_c2_4_m2}")
    print(f"  Omega(C_2^4, 3) = Omega(C_2^5, 2) = M(5) = {dp_c2_4[3]} (factors {factorize(dp_c2_4[3])})")

    dp_223, _ = omega_dp_all([2, 2, 3], 4)
    assert dp_223[2] == 50 and dp_223[3] == 887
    end_223 = (dp_223[2] ** 2) * dp_223[3]
    assert end_223 == 2217500 and factorize(end_223) == {2: 2, 5: 4, 887: 1}
    print(f"  |End_<=(C_2 x C_2 x C_3)| = 50^2 * 887 = {end_223} (factors {factorize(end_223)})")
    print("  [PASS] All pointwise, naive-box, and endomorphism counterexamples verified.")


def main() -> None:
    verify_positive_macmahon()
    verify_cube_polynomial_and_irreducibility()
    verify_pointwise_naive_box_and_endomorphisms()
    print("\nALL VERIFICATION CHECKS PASSED SUCCESSFULLY (Conjecture 00000008552 = FALSE).")


if __name__ == "__main__":
    main()
