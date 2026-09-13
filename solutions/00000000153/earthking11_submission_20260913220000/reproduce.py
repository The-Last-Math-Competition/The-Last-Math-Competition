#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000000153.

Conjecture (as filed):
    "Minimal transitivity of prime orbits: in any minimal topological dynamical
    system (X, T), for every x in X the orbit closure {T^{p_n} x : n >= 1}
    equals X", where p_n is the n-th prime.

The conjecture is FALSE.  This script verifies, with the Python 3 standard
library only, the finite discrete witness

    X = Z/4 = {0, 1, 2, 3},   T(x) = (x + 1) mod 4,

for which

  * (X, T) is minimal: T is a single 4-cycle, so the full orbit of every x is
    all of X (hence the full-orbit closure is X for every x);
  * the prime-index orbit of every x is {T^p x : p prime} = X \\ {x}: it omits
    exactly one residue, namely x itself.  This is because no prime is
    divisible by 4 (the only even prime is 2, and 4 does not divide 2), so
    p mod 4 in {1, 2, 3} and T^p x != x for every prime p;
  * X carries the discrete topology, in which the closure of a set is the set
    itself, so the prime-index orbit closure omits x and is not all of X.

In particular at x = 0 the prime-index orbit is {p mod 4 : p prime} = {1, 2, 3},
whose closure is {1, 2, 3} != X.  The conjecture's conclusion fails in a
minimal system, so the conjecture is false as stated.

The script enumerates every prime p < 10**6, so the residue computation is a
large finite corroboration of the mathematical fact 4 does not divide p, which
holds for all primes.  It exits non-zero if any check fails.
"""

import sys
from itertools import product

# ----------------------------------------------------------------------------
# The system X = Z/4, T(x) = x + 1.
# ----------------------------------------------------------------------------

MOD = 4
X = list(range(MOD))            # X = {0, 1, 2, 3}


def T(x):
    """The shift on Z/4."""
    return (x + 1) % MOD


def iterate(x, n):
    """T^n x, computed by n-fold application of T."""
    for _ in range(n):
        x = T(x)
    return x


def full_orbit(x):
    """The full forward orbit {T^n x : n >= 0} as a set (finite: X is finite)."""
    seen = set()
    y = x
    while y not in seen:
        seen.add(y)
        y = T(y)
    return seen


def prime_orbit(x, primes):
    """The prime-index orbit {T^p x : p prime} as a set, for p in `primes`."""
    return {iterate(x, p % MOD) for p in primes}


# ----------------------------------------------------------------------------
# Primes below a bound, by sieve of Eratosthenes (standard library only).
# ----------------------------------------------------------------------------

BOUND = 10 ** 6


def primes_below(bound):
    """All primes p < bound, by sieve of Eratosthenes."""
    if bound < 3:
        return []
    sieve = bytearray([1]) * bound          # sieve[n] == 1 means "n is prime"
    sieve[0] = sieve[1] = 0
    n = 2
    while n * n < bound:
        if sieve[n]:
            sieve[n * n::n] = bytearray(len(range(n * n, bound, n)))
        n += 1
    return [n for n in range(bound) if sieve[n]]


# ----------------------------------------------------------------------------
# Checks.
# ----------------------------------------------------------------------------

def main():
    checks = []                     # list of (ok, name, detail)
    all_ok = [True]

    def check(name, ok, detail=""):
        ok = bool(ok)
        checks.append((ok, name, detail))
        all_ok[0] = all_ok[0] and ok
        return ok

    print("=" * 78)
    print("Disproof of conjecture 00000000153 -- reproduction")
    print("=" * 78)
    print()
    print(f"System: X = Z/4 = {X}, T(x) = (x + 1) mod 4, discrete topology.")
    print()

    # ------------------------------------------------------------------
    # 1. T is a 4-cycle on X.
    # ------------------------------------------------------------------
    for x in X:
        orb = [iterate(x, k) for k in range(MOD)]
        check(f"T is a 4-cycle from x = {x}",
              sorted(orb) == X and iterate(x, MOD) == x,
              f"orbit = {orb}, T^4({x}) = {iterate(x, MOD)}")

    # ------------------------------------------------------------------
    # 2. (X, T) is minimal: the full orbit of every x is all of X, so every
    #    full-orbit closure is X.
    # ------------------------------------------------------------------
    for x in X:
        check(f"minimality: full orbit of x = {x} equals X",
              full_orbit(x) == set(X),
              f"full orbit = {sorted(full_orbit(x))}")

    # ------------------------------------------------------------------
    # 3. No prime below BOUND is divisible by 4; the residue set mod 4 of the
    #    primes is {1, 2, 3} and 0 is never attained.
    # ------------------------------------------------------------------
    primes = primes_below(BOUND)
    check(f"primes below 10**6 enumerated",
          len(primes) > 0 and primes[0] == 2,
          f"count = {len(primes)}, first = {primes[:5]}, last = {primes[-1]}")

    divisible_by_4 = [p for p in primes if p % 4 == 0]
    check("no prime p < 10**6 is divisible by 4",
          divisible_by_4 == [],
          f"primes divisible by 4: {divisible_by_4}")

    residues = {p % 4 for p in primes}
    check("prime residues mod 4 are exactly {1, 2, 3}",
          residues == {1, 2, 3},
          f"residues = {sorted(residues)}")

    check("residue 0 mod 4 is never attained by a prime",
          0 not in residues,
          "0 not in {p mod 4 : p prime}")

    # The mathematical reason, independent of the bound: the only even prime
    # is 2, and 4 does not divide 2.
    check("arithmetic: the only even prime is 2 and 4 does not divide 2",
          primes[0] == 2 and 2 % 4 != 0 and 4 % 2 == 0,
          "p even and prime => p = 2; 4 | p => 2 | p => p = 2; but 4 does not divide 2")

    # ------------------------------------------------------------------
    # 4. The prime-index orbit of every x equals X \ {x}: it omits exactly one
    #    residue, so its closure (the set itself, in the discrete topology) is
    #    a proper subset of X.
    # ------------------------------------------------------------------
    for x in X:
        po = prime_orbit(x, primes)
        check(f"prime orbit of x = {x} omits exactly one residue (x itself)",
              po == set(X) - {x},
              f"prime orbit = {sorted(po)}, omitted = {sorted(set(X) - po)}")

    check("prime orbit of x = 0 is {1, 2, 3}",
          prime_orbit(0, primes) == {1, 2, 3},
          f"{{p mod 4 : p prime}} = {sorted(prime_orbit(0, primes))}")

    check("closure of the prime orbit of x = 0 is {1,2,3} != X",
          prime_orbit(0, primes) == {1, 2, 3} and prime_orbit(0, primes) != set(X),
          "discrete topology: closure = set itself = {1,2,3}; X = {0,1,2,3}")

    for x in X:
        po = prime_orbit(x, primes)
        check(f"closure of the prime orbit of x = {x} is a proper subset of X",
              po != set(X),
              f"closure = {sorted(po)} != X = {X}")

    # ------------------------------------------------------------------
    # 5. The refutation: a minimal system in which the conclusion fails.
    #    (Also: the "closure of the full orbit" reading would be trivially
    #    true here, since the full orbit already is X.)
    # ------------------------------------------------------------------
    minimal = all(full_orbit(x) == set(X) for x in X)
    fails = any(prime_orbit(x, primes) != set(X) for x in X)

    check("SYSTEM IS MINIMAL", minimal,
          "every full orbit equals X")
    check("CONJECTURE'S CONCLUSION FAILS (for x = 0, and in fact every x)",
          fails,
          "prime orbit closure omits x, so it is not X")
    check("under the 'closure of the FULL orbit' reading the claim is trivially true",
          all(full_orbit(x) == set(X) for x in X),
          "full orbit = X for every x; this collapses the claim, it does not rescue it")

    # ------------------------------------------------------------------
    # 6. Report.
    # ------------------------------------------------------------------
    print("-" * 78)
    print(f"Primes enumerated: {len(primes)} primes p < 10**6")
    print(f"  residue set {{p mod 4}} = {sorted(residues)}   (0 never attained)")
    print()
    print("x   full orbit      prime orbit     omitted   closure != X ?")
    for x in X:
        fo = sorted(full_orbit(x))
        po = sorted(prime_orbit(x, primes))
        omitted = sorted(set(X) - prime_orbit(x, primes))
        print(f"{x}   {str(fo):<15} {str(po):<15} {str(omitted):<9} "
              f"{prime_orbit(x, primes) != set(X)}")
    print()
    print("-" * 78)
    for ok, name, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"[{mark}] {name}")
        if detail:
            print(f"        {detail}")
    print("-" * 78)

    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000000153 is FALSE.")
        print("  (Fin 4, x -> x+1) is minimal, but the prime-index orbit of 0 is")
        print("  {1,2,3}, whose discrete closure {1,2,3} != Fin 4 = {0,1,2,3}.")
        print("-" * 78)
        return 0
    print("FAIL: at least one check did not verify.")
    print("-" * 78)
    return 1


if __name__ == "__main__":
    sys.exit(main())
