#!/usr/bin/env python3
"""Reproduce the arithmetic core of the disproof of conjecture 00000000443.

The conjecture asserts, for the degree-`n` homogeneous part `L_n` of the free Lie
algebra on two generators, that for all `n >= 2`

        dim L_n >= 2^(n-1) - 2^ceil(n/2),                  (I)

and that for prime `n` the gap between this bound and the exact value is exactly
half of `2^((n-1)/2)`.

This script:

  1. implements the Moebius function by hand (no sympy / no math.factorization);
  2. computes the exact Witt dimensions
        dim L_n = (1/n) * sum_{d | n} mu(d) * 2^(n/d)
     for n = 1..12;
  3. computes the claimed bound 2^(n-1) - 2^ceil(n/2);
  4. checks that inequality (I) fails at n = 4 and for every n in [4, 12];
  5. computes the actual prime gaps and the claimed value
        (1/2) * 2^((n-1)/2)
     and checks that the gap claim fails at n = 3, 7, 11;
  6. prints PASS/FAIL and exits non-zero on FAIL.

Pure Python 3 standard library only.
"""

from __future__ import annotations

from typing import List, Tuple


# ---------------------------------------------------------------------------
# Moebius function, implemented by hand (trial division)
# ---------------------------------------------------------------------------

def mobius(n: int) -> int:
    """Return the Moebius function mu(n) for n >= 1.

    mu(n) = 0 if n is not square-free,
            (-1)^k if n is a product of k distinct primes.
    """
    if n < 1:
        return 0
    if n == 1:
        return 1
    m = n
    mu = 1
    p = 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                # p^2 divides n
                return 0
            mu = -mu
        p += 1 if p == 2 else 2
    if m > 1:
        mu = -mu
    return mu


# ---------------------------------------------------------------------------
# Witt's formula and the claimed bound
# ---------------------------------------------------------------------------

def witt_dim(n: int) -> int:
    """dim L_n = (1/n) * sum_{d | n} mu(d) * 2^(n/d)."""
    if n < 1:
        raise ValueError("n must be positive")
    total = 0
    for d in range(1, n + 1):
        if n % d == 0:
            total += mobius(d) * 2 ** (n // d)
    assert total % n == 0, f"Witt sum {total} not divisible by n = {n}"
    return total // n


def claimed_bound(n: int) -> int:
    """The conjectured lower bound 2^(n-1) - 2^ceil(n/2)."""
    ceil_half = (n + 1) // 2  # ceil(n/2) for integer n
    return 2 ** (n - 1) - 2 ** ceil_half


def actual_gap(n: int) -> int:
    """The magnitude of the gap between the claimed bound and the exact value."""
    return abs(claimed_bound(n) - witt_dim(n))


def claimed_gap(n: int) -> int:
    """The conjectured gap (1/2) * 2^((n-1)/2).

    For odd n this is an integer; for even n, (n-1)/2 is not an integer and the
    expression is not an integer (for n = 2 it is 1/sqrt(2)), so this helper is
    only meaningful for odd n.
    """
    if (n - 1) % 2 != 0:
        raise ValueError("claimed_gap is only integral for odd n")
    return 2 ** ((n - 1) // 2) // 2


# ---------------------------------------------------------------------------
# Tables
# ---------------------------------------------------------------------------

def print_dim_table() -> None:
    print("\n[1] Exact dimensions dim L_n (Witt's formula), n = 1..12")
    print(f"    {'n':>3} | {'divisors':<14} | {'witt sum':>9} | {'dim L_n':>7}")
    print("    " + "-" * 45)
    for n in range(1, 13):
        ds = [d for d in range(1, n + 1) if n % d == 0]
        total = sum(mobius(d) * 2 ** (n // d) for d in ds)
        print(f"    {n:>3} | {str(ds):<14} | {total:>9} | {total // n:>7}")


def print_bound_table() -> None:
    print("\n[2] Claimed bound B(n) = 2^(n-1) - 2^ceil(n/2), n = 1..12")
    print(f"    {'n':>3} | {'dim L_n':>7} | {'B(n)':>6} | {'dim >= B ?':>10}")
    print("    " + "-" * 38)
    for n in range(1, 13):
        d, b = witt_dim(n), claimed_bound(n)
        print(f"    {n:>3} | {d:>7} | {b:>6} | {str(d >= b):>10}")


def print_gap_table() -> None:
    print("\n[3] Prime gaps: exact dim, claimed bound, actual |gap|, claimed gap")
    primes = [2, 3, 5, 7, 11]
    print(
        f"    {'p':>3} | {'dim L_p':>7} | {'B(p)':>6} | {'|gap|':>6} |"
        f" {'(1/2)2^((p-1)/2)':>17} | {'match':>5}"
    )
    print("    " + "-" * 60)
    for p in primes:
        d, b = witt_dim(p), claimed_bound(p)
        gap = abs(b - d)
        if (p - 1) % 2 == 0:
            cg = claimed_gap(p)
            match = str(gap == cg)
        else:
            cg = "not an integer"
            match = "n/a"
        print(f"    {p:>3} | {d:>7} | {b:>6} | {gap:>6} | {str(cg):>17} | {match:>5}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    print("=" * 72)
    print("Disproof of conjecture 00000000443 -- arithmetic reproduction")
    print("=" * 72)

    print_dim_table()
    print_bound_table()
    print_gap_table()

    checks: List[Tuple[str, bool, str]] = []

    # Failure (A): the inequality itself.
    d4, b4 = witt_dim(4), claimed_bound(4)
    checks.append(
        (
            "Failure A: dim L_4 < 2^3 - 2^2 (bound fails at n = 4)",
            d4 == 3 and b4 == 4 and d4 < b4,
            f"dim L_4 = {d4}, bound = {b4}, so {d4} < {b4}.",
        )
    )
    all_fail = all(witt_dim(n) < claimed_bound(n) for n in range(4, 13))
    bad = [n for n in range(4, 13) if not witt_dim(n) < claimed_bound(n)]
    checks.append(
        (
            "Failure A: dim L_n < B(n) for every n in [4, 12]",
            all_fail,
            "all strict inequalities hold." if all_fail
            else f"inequality unexpectedly holds at n = {bad}.",
        )
    )

    # Failure (B): the prime-gap formula.
    for p in (3, 7, 11):
        g, cg = actual_gap(p), claimed_gap(p)
        checks.append(
            (
                f"Failure B: gap claim fails at prime n = {p}",
                g != cg,
                f"actual |gap| = {g}, claimed = {cg}, so they differ.",
            )
        )

    # Honest note: the formula coincidentally holds at p = 5.
    g5, cg5 = actual_gap(5), claimed_gap(5)
    checks.append(
        (
            "Context: gap claim coincidentally holds at prime n = 5 (not a failure)",
            g5 == cg5,
            f"actual |gap| = {g5} = claimed = {cg5}.",
        )
    )

    # The clause cannot even be stated integrally at p = 2.
    checks.append(
        (
            "Context: at n = 2 the claimed gap (1/2)2^(1/2) is not an integer",
            True,
            "the formula presupposes (n-1)/2 integral, which fails at n = 2.",
        )
    )

    print("\n[4] Contradiction checks")
    all_ok = True
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")
        all_ok = all_ok and ok

    print("\n" + "=" * 72)
    if all_ok:
        print("PASS: (A) the inequality fails for all n >= 4 tested (n = 4..12);")
        print("      (B) the prime-gap formula fails at n = 3, 7, 11.")
        print("Conjecture 00000000443 is FALSE as stated.")
        print("=" * 72)
        return 0
    print("FAIL: at least one claimed contradiction did not verify.")
    print("=" * 72)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
