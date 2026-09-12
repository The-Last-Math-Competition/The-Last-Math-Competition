#!/usr/bin/env python3
"""Reproduce the arithmetic core of the disproof of conjecture 00000001186.

This script:

  1. factors 60, 504 and 660 (trial division, standard library only);
  2. prints omega(n) (distinct prime divisors) and Omega(n) (with multiplicity);
  3. checks the three internal contradictions of the conjecture;
  4. reports whether the alternative "multiplicity" reading rescues anything;
  5. prints a PASS/FAIL summary and exits non-zero on FAIL.

It runs in well under a second and needs no third-party packages.
"""

from __future__ import annotations

from typing import List, Tuple


def factorize(n: int) -> List[Tuple[int, int]]:
    """Return the prime factorisation of n as a sorted list of (prime, exponent)."""
    if n < 2:
        return []
    factors: List[Tuple[int, int]] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            factors.append((d, e))
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append((n, 1))
    return factors


def omega(n: int) -> int:
    """Number of distinct prime divisors of n."""
    return len(factorize(n))


def big_omega(n: int) -> int:
    """Number of prime divisors of n counted with multiplicity."""
    return sum(e for _, e in factorize(n))


def fmt_factorization(n: int) -> str:
    fac = factorize(n)
    if not fac:
        return str(n)
    parts = [str(p) if e == 1 else f"{p}^{e}" for p, e in fac]
    return " * ".join(parts)


def main() -> int:
    print("=" * 68)
    print("Disproof of conjecture 00000001186 -- arithmetic reproduction")
    print("=" * 68)

    numbers = [60, 504, 660]
    print("\n[1] Factorisations")
    print(f"    {'n':>5} | {'factorisation':<24} | omega | Omega")
    print("    " + "-" * 50)
    for n in numbers:
        print(
            f"    {n:>5} | {fmt_factorization(n):<24} |"
            f" {omega(n):^5} | {big_omega(n):^5}"
        )

    w60, w504, w660 = omega(60), omega(504), omega(660)
    W60, W504, W660 = big_omega(60), big_omega(504), big_omega(660)

    checks = []  # (name, condition, explanation)

    # Contradiction 1: 504 has 3 distinct prime factors, so m(4) != 504.
    checks.append(
        (
            "Contradiction 1: omega(504) == 3 != 4, so m(4) != 504",
            w504 == 3 and w504 != 4,
            f"504 = {fmt_factorization(504)} has omega = {w504} distinct primes; "
            "a group of order 504 cannot have exactly 4 distinct prime factors.",
        )
    )

    # Contradiction 2: 660 has 4 distinct prime factors, so m(5) != 660.
    checks.append(
        (
            "Contradiction 2: omega(660) == 4 != 5, so m(5) != 660",
            w660 == 4 and w660 != 5,
            f"660 = {fmt_factorization(660)} has omega = {w660} distinct primes; "
            "a group of order 660 cannot have exactly 5 distinct prime factors.",
        )
    )

    # Contradiction 3: ratio 504/60 > 4 using the conjecture's own values.
    ratio = 504 / 60
    checks.append(
        (
            "Contradiction 3: 504/60 > 4 (ratio bound fails at k = 4)",
            ratio > 4,
            f"m(4)/m(3) = 504/60 = {ratio} > 4 contradicts m(k)/m(k-1) <= 4 "
            "with equality at k = 4.",
        )
    )

    # The multiplicity reading rescues nothing: base case m(3)=60 already fails.
    checks.append(
        (
            "Multiplicity reading fails: Omega(60) == 4 != 3, so m(3) = 60 fails",
            W60 == 4 and W60 != 3,
            f"60 = {fmt_factorization(60)} has Omega = {W60} counted with "
            "multiplicity, not 3; the first listed value is already inconsistent.",
        )
    )
    checks.append(
        (
            "Multiplicity reading fails: Omega(504) == 6 != 4, so m(4) = 504 fails",
            W504 == 6 and W504 != 4,
            f"504 has Omega = {W504} counted with multiplicity, not 4.",
        )
    )
    # Only 660 happens to match under the multiplicity reading; note it honestly.
    checks.append(
        (
            "Multiplicity reading: Omega(660) == 5 (only consistent value)",
            W660 == 5,
            "Omega(660) = 5 matches its index, but it is assigned to m(5) and "
            "cannot repair the base case or the ratio bound.",
        )
    )

    print("\n[2] Contradiction checks")
    all_ok = True
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")
        all_ok = all_ok and ok

    print("\n[3] Context: orders below 660 and their omega")
    below = [60, 168, 360, 504]
    max_omega_below = 0
    for n in below:
        w = omega(n)
        max_omega_below = max(max_omega_below, w)
        print(f"    order {n:>4} = {fmt_factorization(n):<22} omega = {w}")
    context_ok = max_omega_below <= 3
    print(
        f"    -> every listed nonabelian simple group order < 660 has omega <= 3: "
        f"{'ok' if context_ok else 'FAIL'}"
    )
    all_ok = all_ok and context_ok
    print(
        f"    standard-reading values: m(3) = 60, m(4) = 660 "
        f"(omega(660) = {w660}); stated m(4) = 504 is wrong, "
        "stated m(5) = 660 is a one-index mislabel."
    )

    print("\n" + "=" * 68)
    if all_ok:
        print("PASS: all three contradictions and both reading checks verified.")
        print("Conjecture 00000001186 is FALSE as stated.")
        print("=" * 68)
        return 0
    else:
        print("FAIL: at least one claimed contradiction did not verify.")
        print("=" * 68)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
