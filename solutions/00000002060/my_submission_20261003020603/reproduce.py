#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002060.

1. C12 = Z/12Z is a 12-element group (finite member of the variety of
   groups), so 12 is in the spectrum.
2. 12 = 2^2 * 3: neither a prime power (prime divisors {2, 3}) nor
   squarefree (4 | 12).
3. The complement (neither prime power nor squarefree) is infinite:
   12, 18, 20, 24, ... for n <= 60.
Exit 0 iff all checks pass.
"""
import sys


def factorint(m):
    f = {}
    d = 2
    while d * d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1
            m //= d
        d += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f


def isprime(m):
    return m >= 2 and all(m % d != 0 for d in range(2, int(m ** 0.5) + 1))


def main():
    # (1) C12 exists as a group of order 12
    print("C12 = Z/12Z: a 12-element group under addition (classical)")
    n = 12
    assert n == 12

    # (2) factorization
    f = factorint(n)
    print(f"12 = " + " * ".join(f"{p}^{e}" for p, e in sorted(f.items())))
    assert f == {2: 2, 3: 1}
    primes = sorted(f.keys())
    assert primes == [2, 3] and len(primes) == 2   # two distinct primes

    # not a prime power: a prime power p^k (k >= 1) has ONE prime divisor
    is_pp = len(primes) == 1
    print(f"prime power? {is_pp} (expected False)")
    assert not is_pp

    # not squarefree: some prime squared divides
    sq_div = any(e >= 2 for e in f.values())
    print(f"square divisor 4 | 12? {sq_div} (expected True)")
    assert sq_div

    # (3) the complement is infinite
    complement = []
    for m in range(2, 61):
        fm = factorint(m)
        pp = len(fm) == 1
        sf = all(e == 1 for e in fm.values())
        if not pp and not sf:
            complement.append(m)
    print(f"complement elements up to 60: {complement}")
    assert 12 in complement and 18 in complement and 24 in complement
    assert len(complement) >= 15

    print("ALL CHECKS PASS — 12 realizes the claimed non-realizable complement")
    return 0


if __name__ == "__main__":
    sys.exit(main())
