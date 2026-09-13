#!/usr/bin/env python3
"""Reproduce the refutation of conjecture 00000000750.

Conjecture (reduced statement): for the mod p^k reduction of a 1-Lipschitz map
on Z_p, the Mahler coefficient sequence (a_n mod p^k) is eventually periodic
with *exact* period p^{k-1}(p-1), which cannot be shortened.

Counterexample: f(x) = x + 1.  Its Mahler coefficients are
    a_n = Delta^n f (0),
and since Delta(x+1) = 1 is the constant function, Delta^2 f = 0, so
    (a_n) = (1, 1, 0, 0, 0, ...).
Reduced mod p^k this is eventually constant 0, so its minimal eventual period
is 1 -- never p^{k-1}(p-1) for the listed (p, k).

This script:
  1. computes the first N Mahler coefficients of f(x) = x + 1 by finite
     differences;
  2. verifies they are (1, 1, 0, 0, ...);
  3. computes the exact (minimal) eventual period of (a_n mod p^k) and compares
     it with the conjectured value p^{k-1}(p-1).

Standard library only.  Prints PASS/FAIL and exits 0.
"""

import sys

N = 12  # number of Mahler coefficients to compute
PAIRS = [(2, 2), (2, 3), (3, 1), (3, 2), (5, 1), (5, 2)]


def forward_differences(values):
    """Leading entries of the successive forward differences of `values`."""
    out = []
    cur = list(values)
    out.append(cur[0])
    while len(cur) > 1:
        cur = [b - a for a, b in zip(cur, cur[1:])]
        out.append(cur[0])
    return out


def mahler_coeffs(f, n):
    """(Delta^i f)(0) for i = 0 .. n."""
    return forward_differences([f(x) for x in range(n + 1)])


def minimal_eventual_period(seq, max_period=None):
    """Smallest T >= 1 such that some tail of `seq` is T-periodic.

    A genuinely T-periodic tail must contain at least one full period
    (`n - T - start >= T`), which rules out vacuously short tails.
    If no tail is found we return None.
    """
    n = len(seq)
    if max_period is None:
        max_period = n
    for T in range(1, max_period + 1):
        for start in range(0, n - T):
            if n - T - start >= T and all(seq[i] == seq[i + T]
                                          for i in range(start, n - T)):
                return T
    return None


def main():
    f = lambda x: x + 1
    coeffs = mahler_coeffs(f, N)
    expected = [1, 1] + [0] * (N - 1)

    print("Mahler coefficients a_n = Delta^n f(0) of f(x) = x + 1:")
    print("  computed: {}".format(coeffs))
    print("  expected: {}".format(expected))
    coeffs_ok = coeffs == expected
    print("  => coefficients are (1, 1, 0, 0, ...): {}".format(coeffs_ok))

    print()
    print("Comparing exact eventual period of (a_n mod p^k) with the")
    print("conjectured period p^(k-1) * (p-1):")
    print("  {:<8} {:>10} {:>14} {:>14}".format("(p,k)", "mod p^k",
                                               "actual", "conjectured"))
    all_ok = coeffs_ok
    for (p, k) in PAIRS:
        m = p ** k
        reduced = [a % m for a in coeffs]
        actual = minimal_eventual_period(reduced)
        claimed = p ** (k - 1) * (p - 1)
        differs = actual != claimed
        all_ok = all_ok and actual == 1 and differs
        print("  {:<8} {:>10} {:>14} {:>14}".format(
            "({},{})".format(p, k), m, actual, claimed))

    print()
    if all_ok:
        print("PASS: the coefficient sequence is (1,1,0,0,...), its minimal "
              "eventual period")
        print("      is 1 for every listed (p,k), and this differs from the "
              "conjectured")
        print("      value p^(k-1)(p-1) in every case.  Conjecture "
              "00000000750 is REFUTED.")
        return 0
    print("FAIL: did not reproduce the refutation.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
