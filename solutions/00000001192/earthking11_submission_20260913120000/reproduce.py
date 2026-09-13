#!/usr/bin/env python3
"""
Reproduction script for the disproof of conjecture 00000001192.

The conjecture asserts that c(n, q) -- the number of subgroups of GL_n(F_q)
whose order equals that of the commutator (derived) subgroup -- is an
integer-coefficient polynomial in q of degree n^2 - n whose leading coefficient
is

    LC(n) = ( prod_{p | n} p ) / ( n! * n^n ).

This script computes LC(n) exactly as a Fraction for n = 1, ..., 12, prints the
reduced numerator and denominator and whether LC(n) is an integer, and tests the
weaker "integer-valued" reading by checking whether d! * LC(n) is an integer for
d = n^2 - n.

Verdict: LC(n) is a non-integer rational for every n >= 2, and even d! * LC(n)
fails to be an integer at n = 2 (d = 2) and n = 3 (d = 6).  Hence no
integer-coefficient (nor integer-valued) polynomial of the stated degree can
have the stated leading coefficient.

Usage:  python3 reproduce.py
Exit status: 0 on PASS, 1 on FAIL.
"""

from fractions import Fraction
from math import factorial
import sys

MAX_N = 12


def prime_divisors(n: int) -> list:
    """Distinct primes dividing n, by trial division."""
    ps = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        ps.append(n)
    return ps


def radical(n: int) -> int:
    """prod_{p | n} p, the empty product for n = 1 being 1."""
    r = 1
    for p in prime_divisors(n):
        r *= p
    return r


def leading_coefficient(n: int) -> Fraction:
    """LC(n) = (prod_{p | n} p) / (n! * n^n), exactly."""
    den = factorial(n) * n ** n
    return Fraction(radical(n), den)


def main() -> int:
    print("=" * 78)
    print("Conjecture 00000001192: claimed leading coefficient LC(n)")
    print("LC(n) = (prod_{p|n} p) / (n! * n^n),  degree d = n^2 - n")
    print("=" * 78)
    print()
    print(f"{'n':>2}  {'d=n^2-n':>7}  {'LC(n)':>22}  {'int?':>5}  {'d!*LC(n) int?':>13}  {'d!*LC(n)':>22}")
    print("-" * 78)

    computed = {}
    checks = []

    for n in range(1, MAX_N + 1):
        lc = leading_coefficient(n)
        d = n * n - n
        scaled = factorial(d) * lc
        lc_is_int = (lc.denominator == 1)
        scaled_is_int = (scaled.denominator == 1)
        computed[n] = (lc, d, scaled)

        print(
            f"{n:>2}  {d:>7}  {str(lc.numerator) + '/' + str(lc.denominator):>22}"
            f"  {str(lc_is_int):>5}  {str(scaled_is_int):>13}"
            f"  {str(scaled.numerator) + '/' + str(scaled.denominator):>22}"
        )

    print()

    # --- Claimed values from the refutation ---------------------------------
    expected_lc = {
        2: Fraction(1, 4),
        3: Fraction(1, 54),
        4: Fraction(1, 3072),
        6: Fraction(1, 5598720),
    }
    for n, want in sorted(expected_lc.items()):
        got = computed[n][0]
        ok = (got == want)
        checks.append((f"LC({n}) = {want}", ok, got))
        print(f"[{'ok' if ok else 'FAIL'}] LC({n}) = {want}     (computed {got})")

    print()

    # --- Integer-coefficient reading: LC(n) itself must be an integer --------
    for n in range(2, MAX_N + 1):
        lc = computed[n][0]
        ok = (lc.denominator != 1)  # non-integer, so no integer-coefficient poly
        checks.append((f"LC({n}) is a non-integer", ok, lc))
    all_non_int = all(computed[n][0].denominator != 1 for n in range(2, MAX_N + 1))
    print(f"[{'ok' if all_non_int else 'FAIL'}] "
          f"LC(n) is a non-integer for every 2 <= n <= {MAX_N}")

    # --- Charitable integer-valued reading: d! * LC(n) ----------------------
    n2 = computed[2]
    ok2 = (n2[2] == Fraction(1, 2))
    checks.append(("2! * LC(2) = 1/2", ok2, n2[2]))
    print(f"[{'ok' if ok2 else 'FAIL'}] integer-valued test n=2: "
          f"d=2, d!*LC(2) = {n2[2]} (not an integer)")

    n3 = computed[3]
    ok3 = (n3[2] == Fraction(40, 3))
    checks.append(("6! * LC(3) = 40/3", ok3, n3[2]))
    print(f"[{'ok' if ok3 else 'FAIL'}] integer-valued test n=3: "
          f"d=6, d!*LC(3) = {n3[2]} (not an integer)")

    print()

    # --- The n = 2 integer-valued obstruction in divisibility form -----------
    # Integrality of 2! * LC(2) = 1/2 means existence of m with m * 2 = 1.
    ok_div = not any(m * 2 == 1 for m in range(1, 1000))
    checks.append(("no m with m*2 = 1", ok_div, None))
    print(f"[{'ok' if ok_div else 'FAIL'}] there is no natural m with m*2 = 1 "
          f"(so 1/2 is not an integer)")

    print()
    failed = [name for name, ok, _ in checks if not ok]
    if failed:
        print("FAIL: the following checks did not verify:")
        for name in failed:
            print("  -", name)
        return 1

    print("PASS: the stated leading coefficient is arithmetically impossible.")
    print("      LC(n) is a non-integer rational for every n >= 2, so no")
    print("      integer-coefficient polynomial of degree n^2 - n has it; and")
    print("      the weaker integer-valued reading fails at n = 2 and n = 3.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
