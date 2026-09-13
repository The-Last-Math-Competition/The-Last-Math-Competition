#!/usr/bin/env python3
"""
Reproduction script for the rule-3 disproof of conjecture 00000000277.

Claim under test: the maximum multiplicity M of a Laplace eigenvalue on a
planar flat torus equals 6, attained only at an order-thirty-two lattice.

Refutation: on the square torus R^2 / Z^2 the eigenvalue 4*pi^2*N has
multiplicity r2(N) = #{(a,b) in Z^2 : a^2 + b^2 = N}.  Since
r2(5^k) = 4*(k+1) -> infinity, the multiplicity is unbounded and the
literal maximum is infinite, not 6.  Independently, a planar lattice
automorphism has order in {1,2,3,4,6} (crystallographic restriction), so no
lattice has automorphism group of order 32.

Standard library only.  Prints PASS/FAIL and exits 0.
"""

import math
import sys

# --------------------------------------------------------------------------
# Exact arithmetic
# --------------------------------------------------------------------------

def r2(N: int) -> int:
    """Number of ordered integer pairs (a, b) with a*a + b*b == N."""
    cnt = 0
    r = math.isqrt(N)
    for a in range(-r, r + 1):
        rem = N - a * a
        b = math.isqrt(rem)
        if b * b == rem:
            # b and -b both occur, except b == 0 which is a single value
            cnt += 1 if b == 0 else 2
    return cnt


def hex_rep(N: int) -> int:
    """Number of ordered integer pairs (a, b) with a*a + a*b + b*b == N.

    This is the multiplicity function for the hexagonal (triangular) torus,
    whose dual-lattice norm form is Q(a, b) = a^2 + a*b + b^2.
    """
    cnt = 0
    R = math.isqrt(N) + 1
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            if a * a + a * b + b * b == N:
                cnt += 1
    return cnt


def count_orders_with_integer_2cos(max_order: int) -> list:
    """Return orders n in [1, max_order] with 2*cos(2*pi/n) an integer.

    Crystallographic restriction: a rotation preserving a planar lattice has
    order n only when 2*cos(2*pi/n) is an integer (it is the trace of an
    integer matrix).  Numerically this is an integer only for n in
    {1,2,3,4,6}.
    """
    orders = []
    for n in range(1, max_order + 1):
        val = 2.0 * math.cos(2.0 * math.pi / n)
        if abs(val - round(val)) < 1e-9:
            orders.append(n)
    return orders


# --------------------------------------------------------------------------
# Checks
# --------------------------------------------------------------------------

def main() -> int:
    ok = True
    print("=" * 72)
    print("Reproduction: refutation of conjecture 00000000277")
    print("=" * 72)

    # 1. r2(5^k) = 4*(k+1): unbounded multiplicity on the square torus.
    print("\n[1] Square torus  R^2/Z^2 : multiplicity r2(5^k) = 4*(k+1)")
    square_ok = True
    for k, N in enumerate([1, 5, 25, 125, 625, 3125]):
        got = r2(N)
        want = 4 * (k + 1)
        flag = "ok" if got == want else "FAIL"
        if got != want:
            square_ok = False
            ok = False
        print(f"    k={k}  N={N:5d}  r2={got:3d}  expected 4*(k+1)={want:3d}  [{flag}]")

    # 2. Square torus first non-zero eigenvalue (N = 1) has multiplicity 4.
    print("\n[2] Square torus first non-zero eigenvalue (4*pi^2*1):")
    m_sq = r2(1)
    print(f"    multiplicity r2(1) = {m_sq}")
    if m_sq != 4:
        ok = False

    # 3. Hexagonal torus first non-zero eigenvalue (N = 1) has multiplicity 6.
    print("\n[3] Hexagonal torus first non-zero eigenvalue (4*pi^2*1):")
    m_hex = hex_rep(1)
    print(f"    multiplicity #{{(a,b): a^2+ab+b^2=1}} = {m_hex}")
    hex_ok = (m_hex == 6)
    if not hex_ok:
        ok = False
    print("    -> under the 'first non-zero eigenvalue' reading, 6 is correct")
    print("       (hexagonal lattice); this is the only sense in which 6 holds.")

    # 4. The decisive inequality 12 > 6.
    print("\n[4] Decisive inequality:")
    big = r2(25)
    print(f"    r2(25) = {big}   and   6 < {big}  ->  {6 < big}")
    if not (6 < big):
        ok = False
    print("    The square torus already has an eigenvalue 4*pi^2*25 of")
    print("    multiplicity 12 > 6, so the literal maximum is not 6; it is")
    print("    unbounded (see [1]).")

    # 5. Crystallographic restriction: no lattice automorphism of order 32.
    print("\n[5] Crystallographic restriction (planar lattice automorphisms):")
    orders = count_orders_with_integer_2cos(64)
    print(f"    orders n <= 64 with 2*cos(2*pi/n) integral: {orders}")
    print("    largest automorphism group of a planar lattice: dihedral of")
    print("    order 12 (hexagonal); 32 is not attainable.")
    if orders != [1, 2, 3, 4, 6] or 32 in orders:
        ok = False

    print("\n" + "=" * 72)
    print("RESULT:", "PASS" if ok else "FAIL")
    print("=" * 72)
    # Per instructions the script always exits 0; failure is reported by text.
    return 0


if __name__ == "__main__":
    sys.exit(main())
