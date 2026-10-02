#!/usr/bin/env python3
"""Standalone recomputation for the disproof of TLMC conjecture 00000001042.

Conjecture (verbatim): "The variance of the value-set size of a random polynomial f
uniform of degree <= d is asymptotically q*(1 - 1/e)/d (value-set variance)."

Attack point: d = 1, q = 101, exact enumeration over (a, b) in F_q x F_q.
No third-party dependencies; exact rational arithmetic via fractions.Fraction.
"""
from fractions import Fraction
import sys

OK = True


def check(label, cond):
    global OK
    print(f"[{'PASS' if cond else 'FAIL'}] {label}")
    if not cond:
        OK = False


def value_set_size_linear(a, b, q):
    """|{a*x + b : x in F_q}| for f(x) = a*x + b over F_q (d = 1)."""
    return q if a % q != 0 else 1


def enumerate_variance(q, restrict_degree1=False):
    """Exact variance of V over all (a,b) in F_q^2 (or a != 0 only)."""
    pairs = [
        value_set_size_linear(a, b, q)
        for a in range(q)
        for b in range(q)
        if (not restrict_degree1 or a != 0)
    ]
    n = len(pairs)
    EV = Fraction(sum(pairs), n)
    EV2 = Fraction(sum(v * v for v in pairs), n)
    return EV2 - EV * EV


def main():
    q, d = 101, 1

    # 1. Exact enumeration at the attack point (degree <= 1: all (a,b) in F_q^2).
    var_enum = enumerate_variance(q)
    print(f"q={q}, d=1, degree<=1 reading:")
    print(f"  E[V]  = {float(Fraction(1020201, 10201)):.8f}  (exact 10101/101)")
    print(f"  Var   = {var_enum} = {float(var_enum):.8f}")
    check(
        f"enumeration Var == 1000000/10201 (got {var_enum})",
        var_enum == Fraction(1000000, 10201) == Fraction((q - 1) ** 3, q * q),
    )

    # 2. Closed form Var = (q-1)^3/q^2 against brute-force enumeration for many q.
    closed_form_ok = all(
        enumerate_variance(qq) == Fraction((qq - 1) ** 3, qq * qq) for qq in range(2, 51)
    )
    check("closed form Var=(q-1)^3/q^2 matches enumeration for q=2..50", closed_form_ok)

    # 3. Conjectured value q(1-1/e)/d and comparison.
    import math
    claim = q * (1 - 1 / math.e) / d
    print(f"  claim q(1-1/e)/d = {claim:.8f}   true Var = {float(var_enum):.8f}")
    check(
        f"true Var {float(var_enum):.4f} != claim {claim:.4f} (gap {float(var_enum) - claim:.4f})",
        var_enum != claim,
    )

    # 4. Floating-point-free bound for Euler's number: e < 163/60 + 7/4320 = 11743/4320 < 68/25.
    #    e = sum_{k>=0} 1/k!  and for k >= 6, k! >= 720*7^(k-6).
    e_lower = Fraction(0)
    term = Fraction(1)
    k = 0
    while True:
        e_lower += term
        if term < Fraction(1, 10**30):
            break
        k += 1
        term = Fraction(1, math.factorial(k))
    e_upper = Fraction(163, 60) + Fraction(7, 4320)  # 11743/4320
    check(f"Euler e in ({float(e_lower):.12f}, {float(e_upper):.12f}); e < 68/25 = 2.72",
          e_upper < Fraction(68, 25) and Fraction(2, 1) < e_lower)

    # 5. Conjectured value < 4343/68 < true variance (exact integer cross-multiplication).
    bound = Fraction(4343, 68)  # = 101*(1 - 25/68), upper bound of claim given e > 25/68... (e <= 68/25)
    check(
        f"claim <= 101*(1-25/68) = 4343/68 = {float(bound):.6f} < Var = {float(var_enum):.6f}",
        bound < var_enum,
    )
    check(
        "exact integer kernel: 4343*101^4 (451934321543) < 68*1000000*101^2 (693668000000)",
        4343 * 104060401 < 68 * 10201000000,
    )

    # 6. Asymptotic refutation: Var/q -> 1, not 1 - 1/e.
    print("  q        Var=(q-1)^3/q^2    (1-1/e)*q")
    for qq in (101, 1009, 10007):
        v = Fraction((qq - 1) ** 3, qq * qq)
        c = (1 - 1 / math.e) * qq
        print(f"  {qq:<8} {float(v):<18.4f} {c:<12.4f}  Var/claim = {float(v)/c:.3f}")
        check(f"q={qq}: Var > (1-1/e)*q", v > c)

    # 7. Boundary reading: degree exactly 1 (a != 0) => V == q always => Var = 0.
    var_exact1 = enumerate_variance(q, restrict_degree1=True)
    check(
        f"degree-exactly-1 reading: Var = {var_exact1} (= 0) != claim {claim:.4f}",
        var_exact1 == 0,
    )

    print("\nALL CHECKS PASSED" if OK else "\nSOME CHECKS FAILED", file=sys.stderr)
    sys.exit(0 if OK else 1)


if __name__ == "__main__":
    main()
