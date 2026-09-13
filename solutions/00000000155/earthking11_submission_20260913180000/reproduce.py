#!/usr/bin/env python3
"""Reproduction script for conjecture 00000000155.

Conjecture: "The only Bell primes are B_2 = 2 and B_3 = 5."

We use the 0-indexed convention of the conjecture file itself,
B_0 = 1, B_1 = 1, B_2 = 2, B_3 = 5, B_4 = 15, ...

The script computes Bell numbers B_0..B_N via the Bell triangle
(Aitken's array), tests primality by trial division, prints the indices
that yield primes, and prints PASS/FAIL.  It exits 0 either way.

Standard library only.
"""

import sys

N = 20


def bell_numbers(n):
    """Return the list [B_0, B_1, ..., B_n] via the Bell triangle."""
    # row is the current Bell-triangle row; row[0] is the Bell number.
    row = []
    bells = []
    for _ in range(n + 1):
        if not row:
            new_row = [1]
        else:
            new_row = [row[-1]]
            for x in row:
                new_row.append(new_row[-1] + x)
        row = new_row
        bells.append(row[0])
    return bells


def is_prime(m):
    if m < 2:
        return False
    if m == 2:
        return True
    if m % 2 == 0:
        return False
    d = 3
    while d * d <= m:
        if m % d == 0:
            return False
        d += 2
    return True


def main():
    bells = bell_numbers(N)

    print("Bell numbers B_0..B_%d (0-indexed, file convention):" % N)
    for i, b in enumerate(bells):
        print("  B_%-2d = %d%s" % (i, b, "   <-- prime" if is_prime(b) else ""))

    prime_indices = [i for i, b in enumerate(bells) if is_prime(b)]
    print()
    print("Indices 0..%d giving a prime Bell number: %s"
          % (N, prime_indices))
    print("Corresponding Bell primes: %s" % [bells[i] for i in prime_indices])

    # The conjecture asserts the only Bell primes are B_2 = 2 and B_3 = 5.
    conjectured = [2, 3]
    extras = [i for i in prime_indices if i not in conjectured]

    print()
    print("Conjectured prime indices: %s" % conjectured)
    print("Additional prime indices found: %s" % extras)

    ok = (
        bells[2] == 2
        and bells[3] == 5
        and is_prime(bells[7])          # B_7 = 877
        and is_prime(bells[13])         # B_13 = 27644437
        and bells[7] != bells[2]
        and bells[7] != bells[3]
    )

    if extras:
        print("PASS: conjecture REFUTED - Bell primes also occur at %s" % extras)
        print("      B_7 = %d and B_13 = %d are prime." % (bells[7], bells[13]))
    else:
        print("FAIL: no additional Bell primes found in range 0..%d" % N)

    if not ok:
        print("FAIL: unexpected Bell values/primality results")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
