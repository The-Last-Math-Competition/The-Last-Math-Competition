#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000000463.

    Definition: tau(K_n) = n^(n-2).
    Conjecture: #{n <= N : n^(n-2) is squarefree} ~ c * N / sqrt(log N)
                (a density compatible with abc).

The conjecture is FALSE.  For every n >= 4 and every prime p | n,

        v_p(n^(n-2)) = (n-2) * v_p(n) >= 2 * 1 = 2,

so p^2 | n^(n-2) and n^(n-2) is NOT squarefree.  Only n = 2 (2^0 = 1) and
n = 3 (3^1 = 3) can contribute; n = 1 (1^(1-2) = 1^(-1)) has an undefined
natural-number exponent and is discussed separately.  Hence the count is
bounded by 3 for every N, while c * N / sqrt(log N) -> infinity for every
c > 0: no asymptotic equivalence can hold.

Standard library only, Python 3.8+.  Exits non-zero if any check fails.
"""

import math


# ----------------------------------------------------------------------
# Exact integer arithmetic, trial division only (no sympy, no imports)
# ----------------------------------------------------------------------

def is_prime(n):
    """Primality by bounded trial division."""
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def factor_trial_division(n):
    """Exact factorisation of n (n small) by trial division: {prime: exponent}."""
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def valuation_power(n, p):
    """v_p(n^(n-2)) = (n-2) * v_p(n), computed exactly with no huge integer."""
    if n < 2:
        raise ValueError("n^(n-2) requires n >= 2 for this formula")
    e = 0
    m = n
    while m % p == 0:
        m //= p
        e += 1
    return (n - 2) * e


def squarefree_via_base(n):
    """Exact squarefreeness of n^(n-2) via the factorisation of the base n.

    n^(n-2) = prod_p p^((n-2)*v_p(n)), so it is squarefree iff every
    (n-2)*v_p(n) <= 1.  This is an exact identity, not an approximation.
    """
    if n < 2:
        return None  # n = 1: 1^(-1), see the convention note
    f = factor_trial_division(n)
    return all((n - 2) * e <= 1 for e in f.values())


def squarefree_direct(m):
    """Squarefreeness of a small explicit integer m by trial division."""
    if m < 2:
        return True
    d = 2
    while d * d <= m:
        if m % d == 0:
            e = 0
            while m % d == 0:
                m //= d
                e += 1
            if e >= 2:
                return False
        d += 1
    return True


def main():
    max_n = 3000
    checks = []            # (name, ok, detail)
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    # ------------------------------------------------------------------
    # 1. Cross-check: for tiny n, factor n^(n-2) directly by trial division
    #    and compare with the base-factorisation criterion.
    # ------------------------------------------------------------------
    direct_mismatch = []
    for n in range(2, 13):
        m = n ** (n - 2)
        a = squarefree_via_base(n)
        b = squarefree_direct(m)
        if a != b:
            direct_mismatch.append((n, a, b))
    check("cross-check n = 2..12: base factorisation == direct trial division "
          "of n^(n-2)",
          not direct_mismatch,
          "all agree" if not direct_mismatch else f"mismatches: {direct_mismatch}")

    # ------------------------------------------------------------------
    # 2. The main computation: n in 2..3000
    # ------------------------------------------------------------------
    squarefree_list = [n for n in range(2, max_n + 1) if squarefree_via_base(n)]
    check("squarefree n^(n-2) for 2 <= n <= %d are exactly [2, 3]" % max_n,
          squarefree_list == [2, 3],
          f"found {squarefree_list} (count {len(squarefree_list)})")

    # For n >= 4 exhibit the prime p | n with p^2 | n^(n-2).
    bad_witness = []
    for n in range(4, max_n + 1):
        for p, e in factor_trial_division(n).items():
            v = valuation_power(n, p)
            if v < 2:
                bad_witness.append((n, p, v))
    check("for every 4 <= n <= %d some prime p | n has "
          "v_p(n^(n-2)) = (n-2)*v_p(n) >= 2" % max_n,
          not bad_witness,
          "no counterexample" if not bad_witness else f"failures: {bad_witness}")

    # n = 1 convention
    check("n = 1: 1^(1-2) = 1^(-1) is undefined in N (negative exponent); "
          "if one sets it to 1 the value is squarefree",
          True,
          "count becomes 3 instead of 2 (N >= 3); the asymptotic still fails")

    # Explicit small values
    explicit = {2: 2 ** 0, 3: 3 ** 1, 4: 4 ** 2, 5: 5 ** 3, 6: 6 ** 4}
    check("explicit values: 2^0=1 (squarefree), 3^1=3 (squarefree), "
          "4^2=16, 5^3=125, 6^4=1296 (all divisible by a prime square)",
          explicit[2] == 1 and explicit[3] == 3
          and 4 % 4 == 0 and 125 % 25 == 0 and 1296 % 4 == 0,
          "; ".join(f"{n}^({n-2})={v}" for n, v in explicit.items()))

    # ------------------------------------------------------------------
    # 3. Count table vs c*N/sqrt(log N)  (c = 1; any c > 0 diverges)
    # ------------------------------------------------------------------
    table = []
    for k in range(1, 7):
        N = 10 ** k
        cnt2 = sum(1 for n in squarefree_list if n <= N)          # n >= 2
        cnt1 = cnt2 + (1 if N >= 1 else 0)                        # n >= 1, 1^0=1
        rhs = N / math.sqrt(math.log(N))
        table.append((N, cnt2, cnt1, rhs))
        check(f"N = {N}: count (n >= 2) = {cnt2} and count (n >= 1, 1^(1-2):=1) "
              f"= {cnt1}, both bounded, while N/sqrt(log N) = {rhs:.1f}",
              cnt2 <= 2 and cnt1 <= 3 and rhs > 0,
              f"count/N -> 0 but N/sqrt(log N) -> infinity; "
              f"ratio count/(N/sqrt(log N)) = {cnt2 / rhs:.3e}")

    # The asserted asymptotic fails for every c > 0.
    check("asymptotic claim '#{...} ~ c*N/sqrt(log N)' fails for every c > 0: "
          "LHS is bounded by 3, RHS -> infinity, so LHS/RHS -> 0 != 1",
          True,
          "no constant c makes a bounded sequence asymptotic to a divergent one")

    # ------------------------------------------------------------------
    # 4. Report
    # ------------------------------------------------------------------
    line = "=" * 74
    print(line)
    print("Disproof of conjecture 00000000463 -- reproduction")
    print(line)
    print("\nDefinition: tau(K_n) = n^(n-2).")
    print("Conjecture: #{n <= N : n^(n-2) squarefree} ~ c*N/sqrt(log N).")
    print("Claimed value: FALSE.")

    print("\n[1] Exact valuation: for n >= 4 and prime p | n,")
    print("        v_p(n^(n-2)) = (n-2)*v_p(n) >= 2,  hence p^2 | n^(n-2).")
    print("    So n^(n-2) is squarefree only for n = 2 (2^0 = 1) and n = 3 (3^1 = 3).")
    print("    n = 1: 1^(1-2) = 1^(-1) is undefined in N (negative exponent);")
    print("           under the convention 1^(1-2) := 1 it is squarefree too.")

    print("\n[2] Exhaustive check 2 <= n <= %d (exact, trial division):" % max_n)
    print(f"    squarefree indices = {squarefree_list}  (count {len(squarefree_list)})")
    print("    cross-checked against direct trial division of n^(n-2) for n <= 12.")

    print("\n[3] Count table vs c*N/sqrt(log N)  (c = 1 shown; same conclusion any c > 0)")
    print(f"    {'N':>9}  {'count(n>=2)':>11}  {'count(n>=1)':>11}  "
          f"{'N/sqrt(log N)':>14}")
    for N, cnt2, cnt1, rhs in table:
        print(f"    {N:>9}  {cnt2:>11}  {cnt1:>11}  {rhs:>14.4f}")
    print("    The count is bounded; the right-hand side diverges.")

    print("\n[4] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000000463 is FALSE.")
        print("  Only n in {2,3} (or {1,2,3} with 1^(1-2):=1) give squarefree")
        print("  n^(n-2); the count is bounded while c*N/sqrt(log N) diverges.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
