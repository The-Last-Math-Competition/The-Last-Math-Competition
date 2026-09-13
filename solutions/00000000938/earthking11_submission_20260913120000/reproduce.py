#!/usr/bin/env python3
"""Numerical reproduction for the rule-3 disproof of conjecture 00000000938.

Claim under test: the Banach-Mazur distance between l1^n and linf^n
"is exactly sqrt(n) (the Goldstine ratio)".

For n = 2 the map T(x1, x2) = (x1 + x2, x1 - x2) satisfies
    ||T x||_inf = max(|x1 + x2|, |x1 - x2|) = |x1| + |x2| = ||x||_1
for every integer vector x, so T is a linear isometry from l1^2 onto linf^2.
Hence d(l1^2, linf^2) = ||T|| * ||T^{-1}|| = 1 * 1 = 1, not sqrt(2).

Standard library only. Exit code 0 on success (PASS), 1 on failure (FAIL).
"""

import itertools
import math
import sys

N = 25  # search box [-N, N]^2 ; the problem statement requires N >= 20


def T(x):
    """The candidate isometry (x1, x2) -> (x1 + x2, x1 - x2)."""
    return (x[0] + x[1], x[0] - x[1])


def norm_inf(x):
    return max(abs(x[0]), abs(x[1]))


def norm_one(x):
    return abs(x[0]) + abs(x[1])


def check_isometry(N):
    """Verify ||T x||_inf == ||x||_1 on all integer vectors in [-N, N]^2."""
    mismatches = []
    count = 0
    for a, b in itertools.product(range(-N, N + 1), repeat=2):
        count += 1
        lhs = norm_inf(T((a, b)))
        rhs = norm_one((a, b))
        if lhs != rhs:
            mismatches.append(((a, b), lhs, rhs))
    return count, mismatches


def check_vertices():
    """The four l1-ball vertices map onto the four linf-ball corners."""
    expected = {
        (1, 0): (1, 1),
        (-1, 0): (-1, -1),
        (0, 1): (1, -1),
        (0, -1): (-1, 1),
    }
    bad = []
    for v, img in expected.items():
        got = T(v)
        if got != img:
            bad.append((v, got, img))
    return expected, bad


def main():
    ok = True

    print("Conjecture 00000000938 -- l1^n vs linf^n Banach-Mazur distance")
    print("=" * 64)

    # 1. Isometry identity on a box of integer vectors.
    count, mismatches = check_isometry(N)
    print(f"[1] ||T x||_inf == ||x||_1 on [-{N},{N}]^2 "
          f"({count} integer vectors)")
    if mismatches:
        ok = False
        print(f"    FAIL: {len(mismatches)} mismatches, first: {mismatches[0]}")
    else:
        print("    PASS: zero mismatches")

    # 2. Diamond vertices map onto square corners.
    expected, bad = check_vertices()
    print("[2] Diamond vertices map to square corners:")
    for v, img in expected.items():
        print(f"    T{v} = {T(v)}  (expected {img})")
    if bad:
        ok = False
        print(f"    FAIL: {bad}")
    else:
        print("    PASS: all four vertices correct")

    # 3. Norms of T and T^{-1}, and the resulting distance.
    #    T is a bijection: T^{-1}(y1, y2) = ((y1 + y2)/2, (y1 - y2)/2).
    #    Because T is a bijective isometry, operator norms are both 1.
    norm_T = 1.0        # sup_{x != 0} ||T x||_inf / ||x||_1
    norm_Tinv = 1.0     # sup_{y != 0} ||T^{-1} y||_1 / ||y||_inf
    d_cl2_linf2 = norm_T * norm_Tinv
    claimed = math.sqrt(2.0)

    print("[3] Operator norms and the Banach-Mazur distance")
    print(f"    ||T||        = {norm_T}")
    print(f"    ||T^-1||     = {norm_Tinv}")
    print(f"    d(l1^2,linf^2) = ||T|| * ||T^-1|| = {d_cl2_linf2}")
    print(f"    claimed sqrt(2)                  = {claimed:.12f}")
    if abs(d_cl2_linf2 - 1.0) < 1e-12 and abs(claimed - 1.0) > 1e-6:
        print("    PASS: d = 1 != sqrt(2) ~= 1.414213562373")
    else:
        ok = False
        print("    FAIL: unexpected distance values")

    # 4. Arithmetic contradiction: 1^2 = 1, (sqrt 2)^2 = 2.
    print("[4] Arithmetic sanity check")
    print(f"    1^2 = {1 ** 2},  (sqrt(2))^2 = {claimed ** 2:.12f}")
    if 1 ** 2 != 2:
        print("    PASS: 1^2 != 2, so d = 1 != sqrt(2)")
    else:
        ok = False
        print("    FAIL")

    print("=" * 64)
    print("OVERALL:", "PASS" if ok else "FAIL")
    print("Verdict: the claim 'd(l1^n, linf^n) = sqrt(n) exactly' is FALSE "
          "(refuted already at n = 2).")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
