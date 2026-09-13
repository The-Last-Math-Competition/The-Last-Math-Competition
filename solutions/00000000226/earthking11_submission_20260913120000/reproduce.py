#!/usr/bin/env python3
"""Reproducibility script for the disproof of conjecture 00000000226.

The conjecture claims that (i) the proportion of Cullen numbers C_n = n*2^n + 1
whose least prime factor is 3 is an explicit rational and (ii) the analogous
proportions for Cullen and Woodall numbers W_n = n*2^n - 1 sum to 1
("complementary symmetry mod 3").

We show this is false:

  * C_n and W_n are ODD for every n >= 1, so "least prime factor 3" is the same
    as "divisible by 3";
  * 3 | C_n  <=>  n = 1 or 2 (mod 6);  proportion 2/6 = 1/3;
  * 3 | W_n  <=>  n = 4 or 5 (mod 6);  proportion 2/6 = 1/3;
  * the proportions sum to 1/3 + 1/3 = 2/3, not 1.

The script is standard-library only.  It verifies the two iff statements for
all 1 <= n <= 2000, prints the residue table for n mod 6 = 0..5, and asserts
that the exact proportions sum to 2/3 != 1.  It prints PASS/FAIL and exits 0
on success, 1 on failure.
"""

from fractions import Fraction

LIMIT = 2000


def cullen(n: int) -> int:
    """Cullen number C_n = n * 2^n + 1."""
    return n * (2 ** n) + 1


def woodall(n: int) -> int:
    """Woodall number W_n = n * 2^n - 1 (for n >= 1)."""
    return n * (2 ** n) - 1


def least_prime_factor(n: int):
    """Smallest prime factor of n >= 1, or None for n == 1.

    Only used on the small representatives in the residue-table section, so
    trial division is entirely adequate.
    """
    if n == 1:
        return None
    d = 2
    while d * d <= n:
        if n % d == 0:
            return d
        d += 1
    return n


def main() -> int:
    failures = []

    # ---------------------------------------------------------------- oddness
    # C_n and W_n are odd for every n >= 1, so 2 is never a factor and
    # "least prime factor 3" is equivalent to "divisible by 3".
    bad_parity = [n for n in range(1, LIMIT + 1)
                  if cullen(n) % 2 != 1 or woodall(n) % 2 != 1]
    if bad_parity:
        failures.append(f"parity check failed at n = {bad_parity[:5]}")

    # ------------------------------------------------- the two equivalences
    bad_cullen = []
    bad_woodall = []
    for n in range(1, LIMIT + 1):
        c_ok = (cullen(n) % 3 == 0) == (n % 6 in (1, 2))
        w_ok = (woodall(n) % 3 == 0) == (n % 6 in (4, 5))
        if not c_ok:
            bad_cullen.append(n)
        if not w_ok:
            bad_woodall.append(n)

    if bad_cullen:
        failures.append(f"3 | C_n iff n = 1,2 (mod 6) failed at {bad_cullen[:5]}")
    if bad_woodall:
        failures.append(
            f"3 | W_n iff n = 4,5 (mod 6) failed at {bad_woodall[:5]}")

    # ----------------------------------------------------- empirical counts
    # Over the complete residue system n = 1..6k the counts are exactly 1/3.
    residues_c = sorted({n % 6 for n in range(1, 6 * 100 + 1)
                         if cullen(n) % 3 == 0})
    residues_w = sorted({n % 6 for n in range(1, 6 * 100 + 1)
                         if woodall(n) % 3 == 0})

    # --------------------------------------------------- exact proportions
    prop_c = Fraction(2, 6)   # two residues out of six
    prop_w = Fraction(2, 6)
    prop_sum = prop_c + prop_w
    if prop_sum != Fraction(2, 3):
        failures.append(f"proportion sum {prop_sum} != 2/3")
    if prop_sum == 1:
        failures.append("proportion sum unexpectedly equals 1")

    # ----------------------------------------------------------- reporting
    print("conjecture 00000000226 -- Cullen/Woodall least-prime-factor-3")
    print(f"range checked: 1 <= n <= {LIMIT}")
    print()
    print("residues n mod 6 with 3 | C_n :", residues_c)
    print("residues n mod 6 with 3 | W_n :", residues_w)
    print()
    print("residue table (representatives n = 6..11, i.e. n mod 6 = 0..5):")
    print(f"{'n mod 6':>8} {'2^n mod 3':>10} {'C_n mod 3':>10} {'W_n mod 3':>10}")
    for n in range(6, 12):
        print(f"{n % 6:>8} {2 ** n % 3:>10} {cullen(n) % 3:>10} "
              f"{woodall(n) % 3:>10}")
    print()
    print("cross-check with least_prime_factor on the table row values:")
    for n in range(6, 12):
        lpf_c = least_prime_factor(cullen(n))
        lpf_w = least_prime_factor(woodall(n))
        print(f"  n = {n:>2}: C_n = {cullen(n):>8} (lpf {lpf_c:>6}), "
              f"W_n = {woodall(n):>8} (lpf {lpf_w:>6})")
    print()
    print(f"exact Cullen proportion : {prop_c} = {float(prop_c):.6f}")
    print(f"exact Woodall proportion: {prop_w} = {float(prop_w):.6f}")
    print(f"sum                     : {prop_sum} = {float(prop_sum):.6f}")
    print("1                       : 1.0")
    print()
    print("conclusion: the two proportions sum to 2/3, NOT 1; the asserted")
    print("'complementary symmetry mod 3' fails.  Verdict: conjecture FALSE.")
    print()

    if failures:
        for f in failures:
            print("FAIL:", f)
        print("FAIL")
        return 1

    print("PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
