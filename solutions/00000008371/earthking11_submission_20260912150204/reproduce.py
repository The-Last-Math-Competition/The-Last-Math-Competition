#!/usr/bin/env python3
"""Reproduce the arithmetic core of the disproof of conjecture 00000008371.

The conjecture is a conjunction; this script verifies, for n = 3..8:

  (1) the asserted count F(n) = (n-2)! (n-3)! / 2.  At n = 3 this is 1/2, which
      is not an integer, so F(3) cannot be a count of cells;
  (2) F(n) never equals the vertex count C(n,2) of the Johnson graph J(n,2),
      which the same conjecture asserts to be the adjacency graph;
  (3) F(n) differs from the known Speyer-Sturmfels count (2n-5)!! of maximal
      cones of Trop(Gr(2,n)) (context only).

It prints a table, asserts (1)-(3), prints PASS/FAIL, and exits non-zero on FAIL.
Standard library only; runs instantly.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb, factorial


def space_tree_formula(n: int) -> Fraction:
    """F(n) = (n-2)! (n-3)! / 2, kept exact so non-integrality is visible."""
    return Fraction(factorial(n - 2) * factorial(n - 3), 2)


def johnson_vertices(n: int) -> int:
    """Number of vertices of the Johnson graph J(n,2): C(n,2) = n(n-1)/2."""
    return comb(n, 2)


def double_factorial_odd(m: int) -> int:
    """m!! = 1*3*5*...*m for odd m >= 1; returns 1 for m <= 0."""
    result = 1
    k = 1
    while k <= m:
        result *= k
        k += 2
    return result


def speyer_sturmfels(n: int) -> int:
    """(2n-5)!! : maximal cones of Trop(Gr(2,n))."""
    return double_factorial_odd(2 * n - 5)


def fmt(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def main() -> int:
    ns = list(range(3, 9))

    print("=" * 74)
    print("Disproof of conjecture 00000008371 -- arithmetic reproduction")
    print("=" * 74)
    print()
    print(f"  {'n':>2} | {'F(n)=(n-2)!(n-3)!/2':>22} | {'C(n,2)':>7} | {'(2n-5)!!':>9}")
    print("  " + "-" * 66)
    for n in ns:
        f = space_tree_formula(n)
        print(f"  {n:>2} | {fmt(f):>22} | {johnson_vertices(n):>7} | {speyer_sturmfels(n):>9}")
    print()

    checks = []  # (name, condition, detail)

    # Failure 1: F(3) = 1/2 is not an integer, so it cannot be a count.
    f3 = space_tree_formula(3)
    non_integral = f3.denominator != 1
    checks.append(
        (
            "Failure 1: F(3) = 1/2 is not a non-negative integer",
            non_integral and f3 == Fraction(1, 2),
            f"F(3) = 1!*0!/2 = {fmt(f3)}; a cardinality must be an integer.",
        )
    )

    # Failure 2: F(n) != C(n,2) for every n in the checked range.
    mismatches = [n for n in ns if space_tree_formula(n) != johnson_vertices(n)]
    checks.append(
        (
            "Failure 2: F(n) != C(n,2) for all n in 3..8",
            len(mismatches) == len(ns),
            "; ".join(
                f"n={n}: {fmt(space_tree_formula(n))} != {johnson_vertices(n)}"
                for n in ns
            ),
        )
    )

    # Failure 3 (context): F(n) differs from the known count (2n-5)!!.
    context_mismatches = [
        n for n in ns if space_tree_formula(n) != speyer_sturmfels(n)
    ]
    checks.append(
        (
            "Failure 3 (context): F(n) != (2n-5)!! for all n in 3..8",
            len(context_mismatches) == len(ns),
            "; ".join(
                f"n={n}: {fmt(space_tree_formula(n))} != {speyer_sturmfels(n)}"
                for n in ns
            ),
        )
    )

    # The Johnson vertex count also differs from the known count (context).
    johnson_vs_known = [
        n for n in ns if johnson_vertices(n) != speyer_sturmfels(n)
    ]
    checks.append(
        (
            "Context: C(n,2) != (2n-5)!! for n in 3..8",
            len(johnson_vs_known) == len(ns),
            "neither F(n) nor C(n,2) matches the established count.",
        )
    )

    # Supplement: for n >= 6, F(n) > C(n,2).
    growth_ok = all(
        space_tree_formula(n) > johnson_vertices(n) for n in ns if n >= 6
    )
    checks.append(
        (
            "Supplement: F(n) > C(n,2) for n >= 6 (growth argument)",
            growth_ok,
            "F grows super-exponentially while C(n,2) is quadratic.",
        )
    )

    print("[checks]")
    all_ok = True
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"  [{mark}] {name}")
        print(f"         {detail}")
        all_ok = all_ok and ok
    print()

    print("=" * 74)
    if all_ok:
        print("PASS: F(3) is not a count, and F(n) never equals C(n,2).")
        print("Conjecture 00000008371 is FALSE as stated.")
        print("=" * 74)
        return 0
    print("FAIL: at least one claimed failure did not verify.")
    print("=" * 74)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
