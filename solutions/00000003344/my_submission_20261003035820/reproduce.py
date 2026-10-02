#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000003344.

1. Brute-force binary necklaces (rotation classes) of lengths 2..8:
   counts 1, 2, 3, 6, 9, 30 match the Moebius formula
   N(n) = (1/n) sum_{d|n} mu(d) 2^(n/d).
2. The claimed 2^(n-1) counts (2, 4, 8) differ at n = 2, 3, 4.
Exit 0 iff all checks pass.
"""
import sys


def min_period(bits):
    """Smallest period of a bit string."""
    n = len(bits)
    for p in range(1, n + 1):
        if all(bits[i] == bits[i % p] for i in range(n)):
            return p
    return n


def primitive_necklaces(n):
    """Count binary necklaces of length n with minimal period exactly n
    (the period-n hyperbolic components)."""
    seen = set()
    for m in range(2 ** n):
        bits = format(m, f"0{n}b")
        if min_period(bits) == n:
            rots = {bits[i:] + bits[:i] for i in range(n)}
            seen.add(min(rots))
    return len(seen)


def mu(n):
    if n == 1:
        return 1
    f = {}
    m = n
    d = 2
    while d * d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1
            m //= d
        d += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    if any(e >= 2 for e in f.values()):
        return 0
    return (-1) ** len(f)


def mobius_count(n):
    return sum(mu(d) * 2 ** (n // d) for d in range(1, n + 1) if n % d == 0) // n


def main():
    for n in range(2, 9):
        brute = primitive_necklaces(n)
        formula = mobius_count(n)
        claimed = 2 ** (n - 1)
        print(f"n = {n}: primitive necklaces = {brute}, Moebius formula = "
              f"{formula}, claimed 2^(n-1) = {claimed}")
        assert brute == formula
    assert mobius_count(2) == 1 and mobius_count(2) != 2
    assert mobius_count(3) == 2 and mobius_count(3) != 4
    assert mobius_count(4) == 3 and mobius_count(4) != 8
    print("ALL CHECKS PASS — counts 1, 2, 3 vs claimed 2, 4, 8: refuted")
    return 0


if __name__ == "__main__":
    sys.exit(main())
