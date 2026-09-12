#!/usr/bin/env python3
"""
Reproduction script for the disproof of conjecture 00000001072.

Conjecture (quoted): Let G(n,k,q) denote the number of k-dimensional planes
of F_q^n. The prime-factor spectrum of
    G(n,k,q) = q^{(n-k)k} * [n choose k]_q
consists exactly of the primes <= q^n - 1; every prime factor divides some
q^i - 1 with i <= n, and conversely each such prime occurs for
suitable (n,k).

This script is fully self-contained (standard library only, no third-party
packages, no reliance on any artifact in this submission package).

It:
  1. computes G(n,k,q) from the Gaussian-binomial formula,
  2. INDEPENDENTLY cross-checks it by brute-force enumeration of all affine
     lines (k = 1) in F_q^n as frozensets of points,
  3. prints prime factorizations and the primes <= q^n - 1,
  4. asserts that both directional claims of the conjecture are violated.

Expected output facts (all recomputed here from scratch):
  G(2,1,2) = 6  = 2 * 3, spectrum {2, 3}; q^i-1 for i<=2 are 1, 3, so the
                prime 2 divides no q^i-1 with i <= n.  -> claim 1 FALSE
  G(2,1,3) = 12 = 2^2 * 3, spectrum {2, 3}; primes <= 3^2-1 = 8 are
                {2, 3, 5, 7}: 5 and 7 are <= 8 but divide no ... they simply
                do not occur.                              -> claim 2 FALSE
  G(3,1,2) = 28 = 2^2 * 7, spectrum {2, 7}; primes <= 2^3-1 = 7 are
                {2, 3, 5, 7}: 3 and 5 missing (supporting evidence).
"""

from itertools import product


def gaussian_binomial(n: int, k: int, q: int) -> int:
    """[n choose k]_q = prod_{i=1..k} (q^{n-k+i} - 1) / (q^i - 1)."""
    num = 1
    den = 1
    for i in range(1, k + 1):
        num *= q ** (n - k + i) - 1
        den *= q ** i - 1
    assert num % den == 0, "Gaussian binomial must be an integer"
    return num // den


def G(n: int, k: int, q: int) -> int:
    """G(n,k,q) = q^{(n-k)k} * [n choose k]_q  (the conjecture's formula)."""
    return q ** ((n - k) * k) * gaussian_binomial(n, k, q)


def count_affine_lines_bruteforce(n: int, q: int) -> int:
    """Brute-force count of affine 1-flats in F_q^n (k = 1).

    Each line is the set {v + t*d : t in F_q} for d != 0, canonicalized as a
    frozenset of points, so it is counted exactly once.  This is fully
    independent of the Gaussian-binomial formula.
    """
    zero = tuple([0] * n)
    pts = list(product(range(q), repeat=n))
    lines = set()
    for d in pts:
        if d == zero:
            continue
        for v in pts:
            lines.add(frozenset(
                tuple((v[i] + t * d[i]) % q for i in range(n)) for t in range(q)
            ))
    return len(lines)


def factorize(m: int) -> dict:
    """Prime factorization by trial division (m is small here)."""
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


def primes_up_to(m: int) -> set:
    """Sieve of Eratosthenes."""
    if m < 2:
        return set()
    sieve = [True] * (m + 1)
    sieve[0] = sieve[1] = False
    for d in range(2, int(m ** 0.5) + 1):
        if sieve[d]:
            for j in range(d * d, m + 1, d):
                sieve[j] = False
    return {i for i in range(2, m + 1) if sieve[i]}


def fmt_factors(f: dict) -> str:
    return " * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(f.items()))


def main() -> None:
    cases = [(2, 1, 2), (2, 1, 3), (3, 1, 2)]

    print("=== Values of G(n,k,q) = q^{(n-k)k} * [n choose k]_q ===")
    for n, k, q in cases:
        val = G(n, k, q)
        # k = 1 in all cases: cross-check against direct enumeration
        brute = count_affine_lines_bruteforce(n, q)
        status = "AGREES with brute-force enumeration" if val == brute else \
                 f"DISAGREES with brute-force enumeration ({brute})"
        print(f"G({n},{k},{q}) = {val:<4} ({fmt_factors(factorize(val)):<10}) "
              f"[direct enumeration of affine lines in F_{q}^{n}: {brute} -> {status}]")

    print()
    print("=== Refutation I at (n,k,q) = (2,1,2): "
          "'every prime factor divides some q^i - 1 with i <= n' ===")
    n, k, q = 2, 1, 2
    val = G(n, k, q)
    spectrum = set(factorize(val))
    qim1_union = set()
    for i in range(1, n + 1):
        m = q ** i - 1
        facs = set(factorize(m)) if m > 1 else set()
        qim1_union |= facs
        print(f"  q^{i} - 1 = {m:>2} ; prime factors: {sorted(facs) if facs else 'none (m = 1)'}")
    print(f"  G(2,1,2) = {val}, spectrum = {sorted(spectrum)}")
    print(f"  union of prime factors of q^i-1 (i <= {n}): {sorted(qim1_union)}")
    violators = spectrum - qim1_union
    print(f"  primes in the spectrum that divide NO q^i-1 (i <= {n}): {sorted(violators)}")

    assert (q ** 1 - 1) % 2 != 0, "2 | q^1-1 unexpectedly"
    assert (q ** 2 - 1) % 2 != 0, "2 | q^2-1 unexpectedly"
    assert val % 2 == 0, "2 does not divide G(2,1,2)=6 unexpectedly"
    assert violators == {2}, f"expected violator set {{2}}, got {violators}"
    print("  ASSERTION HOLDS: prime 2 divides G(2,1,2)=6 but divides neither")
    print("  2^1-1 = 1 nor 2^2-1 = 3. The claim is FALSE.")

    print()
    print("=== Refutation II at (n,k,q) = (2,1,3): "
          "'spectrum consists exactly of the primes <= q^n - 1' ===")
    n, k, q = 2, 1, 3
    val = G(n, k, q)
    spectrum = set(factorize(val))
    bound = primes_up_to(q ** n - 1)
    print(f"  G(2,1,3) = {val}, spectrum = {sorted(spectrum)}")
    print(f"  primes <= q^n - 1 = 3^2 - 1 = 8 : {sorted(bound)}")
    print(f"  missing from the spectrum: {sorted(bound - spectrum)}")
    assert bound == {2, 3, 5, 7}
    assert spectrum == {2, 3}
    assert 5 <= q ** n - 1 and val % 5 != 0
    assert 7 <= q ** n - 1 and val % 7 != 0
    assert spectrum != bound
    print("  ASSERTION HOLDS: 5 and 7 are <= 8 but do not divide G(2,1,3)=12.")
    print("  The spectrum is NOT 'exactly' the primes <= q^n - 1. The claim is FALSE.")

    print()
    print("=== Supporting evidence at (n,k,q) = (3,1,2) ===")
    n, k, q = 3, 1, 2
    val = G(n, k, q)
    spectrum = set(factorize(val))
    bound = primes_up_to(q ** n - 1)
    print(f"  G(3,1,2) = {val}, spectrum = {sorted(spectrum)}")
    print(f"  primes <= 2^3 - 1 = 7 : {sorted(bound)}; missing: {sorted(bound - spectrum)}")
    assert val == 28 and spectrum == {2, 7} and bound == {2, 3, 5, 7}
    assert bound - spectrum == {3, 5}

    print()
    print("ALL CHECKS PASSED: conjecture 00000001072 is REFUTED (verdict FALSE).")


if __name__ == "__main__":
    main()
