#!/usr/bin/env python3
"""Disproof of conjecture 00000000159.

For a prime p >= 11, a decomposition of K_p into cycles of pairwise distinct
prime lengths requires the lengths to sum to at least C(p, 2) = p * (p - 1) / 2
edges (exactly that in the edge-disjoint reading, at least that in the covering
reading).  But the greatest possible total of pairwise distinct prime cycle
lengths is the sum of all primes in [3, p].  This script shows that

    sum(primes in [3, p])  <  C(p, 2)

for every prime p in [11, 2000], and prints the first few rows plus the p = 11
witness.  Standard library only; runs in well under a second.
"""

from __future__ import annotations

import sys

LIMIT = 2000


def sieve(limit: int) -> list[bool]:
    """Return a boolean primality table for 0..limit."""
    is_prime = [True] * (limit + 1)
    if limit >= 0:
        is_prime[0] = False
    if limit >= 1:
        is_prime[1] = False
    n = 2
    while n * n <= limit:
        if is_prime[n]:
            for multiple in range(n * n, limit + 1, n):
                is_prime[multiple] = False
        n += 1
    return is_prime


def main() -> int:
    is_prime = sieve(LIMIT)

    primes = [p for p in range(2, LIMIT + 1) if is_prime[p]]
    primes_from_11 = [p for p in primes if p >= 11]

    # Running sum of primes in [3, p]: accumulate as p grows.
    sop = 0
    rows = []
    failures = 0
    for p in primes_from_11:
        if p == 11:
            sop = 3 + 5 + 7 + 11
        else:
            sop += p
        edges = p * (p - 1) // 2
        fails = sop < edges
        rows.append((p, edges, sop, fails))
        if fails:
            failures += 1

    print("Conjecture 00000000159 -- edge-count obstruction")
    print("=" * 60)
    print()
    print("First rows (required total C(p,2) vs maximal available total):")
    print(f"{'p':>5} | {'C(p,2)':>8} | {'sum primes in [3,p]':>20} | verdict")
    print("-" * 60)
    for p, edges, s, fails in rows:
        if p in (11, 13, 17, 19, 23):
            verdict = "IMPOSSIBLE" if fails else "possible"
            print(f"{p:>5} | {edges:>8} | {s:>20} | {verdict}")
    print()

    # Explicit p = 11 witness.
    print("The p = 11 witness:")
    available = [q for q in primes if 3 <= q <= 11]
    edges11 = 11 * 10 // 2
    total11 = sum(available)
    print(f"  available prime cycle lengths: {available}")
    print(f"  their total: {' + '.join(map(str, available))} = {total11}")
    print(f"  edges of K_11: C(11,2) = 11*10/2 = {edges11}")
    print(f"  {total11} < {edges11}, so no decomposition of K_11 exists.")
    print()

    # Assert the failure for every prime in [11, 2000].
    for p, edges, s, fails in rows:
        assert fails, f"bound unexpectedly improved at p={p}: {s} >= {edges}"
    assert failures == len(rows), "not all primes failed the bound"

    print(f"Checked {len(rows)} primes in [11, {LIMIT}]; "
          f"{failures} failures, 0 passes.")
    print()
    print("PASS: the counting obstruction refutes the conjecture for every")
    print("      prime p in [11, 2000], in particular at p = 11.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
