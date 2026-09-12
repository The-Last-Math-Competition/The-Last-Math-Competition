#!/usr/bin/env python3
"""Reproduce the arithmetic core of the disproof of conjecture 00000001097.

The conjecture claims that the mean root count of x^d + a*x + b over F_q equals
1 + (q - 1) / q^{gcd(d-1, q-1)} "as the main term", that it is exactly 1 when
gcd(d-1, q-1) = 1, and that its variance is 2 - 1/q.

This script, using only the Python 3 standard library:

  1. brute-forces the mean root count M(q, d) exactly, as a Fraction, for
     q in {5, 7, 11, 13} and d in {2, 3, 5};
  2. computes the claimed formula value 1 + (q - 1) / q^gcd(d-1, q-1);
  3. computes the exact second moment E[N^2] and the exact variance
     Var = E[N^2] - (E[N])^2;
  4. asserts, in every case, that the exact mean is 1, that the claimed value
     is not 1, that E[N^2] = 2 - 1/q, and that Var = 1 - 1/q;
  5. prints a PASS/FAIL summary and exits non-zero on FAIL.

It runs in well under a second and needs no third-party packages.
"""

from __future__ import annotations

from fractions import Fraction
from math import gcd
from typing import List, Tuple


def root_count(q: int, d: int, a: int, b: int) -> int:
    """Number of x in {0, ..., q-1} with x^d + a*x + b == 0 (mod q)."""
    return sum(1 for x in range(q) if (x ** d + a * x + b) % q == 0)


def mean_root_count(q: int, d: int) -> Fraction:
    """Exact mean of N(a,b) over uniform (a,b) in F_q^2, as a Fraction.

    Computed by brute force over all q^2 pairs (a,b) and all q values of x.
    """
    total = 0
    for a in range(q):
        for b in range(q):
            total += root_count(q, d, a, b)
    return Fraction(total, q * q)


def second_moment(q: int, d: int) -> Fraction:
    """Exact E[N^2] over uniform (a,b) in F_q^2, as a Fraction."""
    total = 0
    for a in range(q):
        for b in range(q):
            n = root_count(q, d, a, b)
            total += n * n
    return Fraction(total, q * q)


def claimed_value(q: int, d: int) -> Fraction:
    """The conjecture's claimed value 1 + (q - 1) / q^{gcd(d-1, q-1)}."""
    g = gcd(d - 1, q - 1)
    return Fraction(1) + Fraction(q - 1, q ** g)


def fmt(fr: Fraction) -> str:
    """Render a Fraction as 'p/q' (or 'p' when the denominator is 1)."""
    if fr.denominator == 1:
        return str(fr.numerator)
    return f"{fr.numerator}/{fr.denominator}"


def main() -> int:
    print("=" * 72)
    print("Disproof of conjecture 00000001097 -- arithmetic reproduction")
    print("=" * 72)

    qs = [5, 7, 11, 13]
    ds = [2, 3, 5]

    header = (
        f"{'q':>3} {'d':>2} {'g':>2} | {'true mean':>10} "
        f"{'claimed':>10} | {'E[N^2]':>10} {'variance':>10}"
    )
    print("\n[1] Exact brute-force values vs. the conjecture")
    print("    " + header)
    print("    " + "-" * len(header))

    checks: List[Tuple[str, bool, str]] = []
    all_ok = True

    for q in qs:
        for d in ds:
            g = gcd(d - 1, q - 1)
            mean = mean_root_count(q, d)
            claim = claimed_value(q, d)
            s2 = second_moment(q, d)
            var = s2 - mean * mean

            print(
                f"    {q:>3} {d:>2} {g:>2} | {fmt(mean):>10} "
                f"{fmt(claim):>10} | {fmt(s2):>10} {fmt(var):>10}"
            )

            tag = f"q={q}, d={d}"

            ok_mean = mean == 1
            checks.append(
                (
                    f"[{tag}] exact mean == 1",
                    ok_mean,
                    f"brute-force mean is {fmt(mean)}; the bijection "
                    "(x, a) -> b = -x^d - a*x forces it to be exactly 1.",
                )
            )

            ok_claim = claim != 1
            checks.append(
                (
                    f"[{tag}] claimed value != 1 (so it is not the mean)",
                    ok_claim,
                    f"claimed 1 + (q-1)/q^g = {fmt(claim)} > 1, while the true "
                    f"mean is {fmt(mean)}.",
                )
            )

            ok_s2 = s2 == 2 - Fraction(1, q)
            checks.append(
                (
                    f"[{tag}] E[N^2] == 2 - 1/q",
                    ok_s2,
                    f"E[N^2] = {fmt(s2)}, 2 - 1/q = {fmt(2 - Fraction(1, q))}.",
                )
            )

            ok_var = var == 1 - Fraction(1, q)
            checks.append(
                (
                    f"[{tag}] Var == 1 - 1/q (not 2 - 1/q)",
                    ok_var,
                    f"Var = {fmt(var)}, 1 - 1/q = {fmt(1 - Fraction(1, q))}, "
                    f"claimed variance 2 - 1/q = {fmt(2 - Fraction(1, q))}.",
                )
            )

            all_ok = all_ok and ok_mean and ok_claim and ok_s2 and ok_var

    print("\n[2] Internal contradiction at q = 5, d = 2")
    q0, d0 = 5, 2
    g0 = gcd(d0 - 1, q0 - 1)
    m0 = mean_root_count(q0, d0)
    c0 = claimed_value(q0, d0)
    print(f"    gcd(d-1, q-1) = gcd({d0 - 1}, {q0 - 1}) = {g0}")
    print(f"    conjecture asserts both: mean = {fmt(c0)} and mean = 1 (exactly)")
    print(f"    exact brute-force mean: {fmt(m0)}")
    contradiction_ok = (g0 == 1) and (c0 != 1) and (m0 == 1)
    print(
        "    -> {0}: {1} != 1 is a flat contradiction inside the conjecture.".format(
            "ok" if contradiction_ok else "FAIL", fmt(c0)
        )
    )
    checks.append(
        (
            f"[q={q0}, d={d0}] g = 1 while claimed {fmt(c0)} != 1",
            contradiction_ok,
            "the two clauses 'mean = 1+(q-1)/q^g' and 'mean exactly 1 when "
            "g = 1' cannot both hold.",
        )
    )
    all_ok = all_ok and contradiction_ok

    print("\n[3] The claimed 'main term' is the second moment when g = 1")
    g1_examples = [(q, d) for q in qs for d in ds if gcd(d - 1, q - 1) == 1]
    for q, d in g1_examples:
        claim = claimed_value(q, d)
        s2 = second_moment(q, d)
        same = claim == s2
        print(
            f"    q={q:>2}, d={d}: claimed {fmt(claim)} == E[N^2] {fmt(s2)}: "
            f"{'ok' if same else 'FAIL'}"
        )
        all_ok = all_ok and same
    print(
        "    -> for g = 1 the conjecture's 'main term' equals the second moment "
        "2 - 1/q, not the mean."
    )

    print("\n[4] Check summary")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + "=" * 72)
    if all_ok:
        print("PASS: mean == 1 and claimed != 1 in every case;")
        print("      E[N^2] == 2 - 1/q and Var == 1 - 1/q in every case.")
        print("Conjecture 00000001097 is FALSE as stated.")
        print("=" * 72)
        return 0
    else:
        print("FAIL: at least one claimed fact did not verify.")
        print("=" * 72)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
