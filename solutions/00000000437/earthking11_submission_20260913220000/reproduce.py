#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000000437.

    Definition: the n-th graded dimension of the Lie-primitive space of the
        shuffle algebra Sh(V) for dim V = 2.
    Conjecture: it equals  L_n = (1/n) * sum_{d | n} mu(d) * 2^(n/d)
        (Witt's formula), and its parity is determined explicitly by whether
        n is a power of 2.

The Witt formula itself is a true classical theorem (L_n counts the binary
Lyndon words of length n, equivalently the monic irreducible polynomials of
degree n over F_2).  The PARITY CLAUSE is FALSE.  This script verifies:

  * the values  L_n = (1/n) * sum_{d | n} mu(d) * 2^(n/d)  for all n <= 60,
    computed from a factorisation-based Moebius function;
  * the asserted base values  L_1 = 2, L_2 = 1, L_6 = 9;
  * the sharpest witness: n = 1 and n = 2 are BOTH powers of two, yet
    L_1 = 2 is even while L_2 = 1 is odd, so parity is not determined by
    "n is a power of 2";
  * the fallback witness: n = 2 and n = 8 are both powers of two with
    different parities (L_2 = 1 odd, L_8 = 30 even), valid even if one
    declines to call 1 a power of two;
  * the "iff" violation at n = 6: L_6 = 9 is odd while 6 is not a power of two;
  * the TRUE repaired characterisation: writing n = 2^a * m with m odd,
    L_n is odd  <=>  a in {1, 2} and m is squarefree -- checked for all
    n <= 60.

Standard library only.  Python 3.8+.  Exits non-zero if any check fails.
"""


def mobius(n):
    """Moebius function, implemented by trial-division factorisation.

    mu(1) = 1; mu(n) = 0 if n is not squarefree; mu(n) = (-1)^k if n is a
    product of k distinct primes.
    """
    if n < 1:
        raise ValueError("mobius is defined on n >= 1")
    if n == 1:
        return 1
    result = 1
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:          # p^2 | n  => not squarefree
                return 0
            result = -result        # one more distinct prime
        p += 1
    if m > 1:                       # one remaining distinct prime
        result = -result
    return result


def divisors(n):
    """Positive divisors of n, ascending."""
    return [d for d in range(1, n + 1) if n % d == 0]


def witt(n):
    """Witt's formula L_n = (1/n) * sum_{d | n} mu(d) * 2^(n/d)."""
    total = sum(mobius(d) * 2 ** (n // d) for d in divisors(n))
    assert total % n == 0, (n, total)
    return total // n


def is_pow2(n):
    """True iff n = 2^k for some k >= 0 (so is_pow2(1) is True)."""
    return n >= 1 and (n & (n - 1)) == 0


def v2(n):
    """2-adic valuation: the exponent a in n = 2^a * m with m odd."""
    a = 0
    while n % 2 == 0:
        n //= 2
        a += 1
    return a


def odd_part(n):
    """The odd part m in n = 2^a * m."""
    while n % 2 == 0:
        n //= 2
    return n


def squarefree(n):
    """True iff n has no repeated prime factor."""
    d = 2
    while d * d <= n:
        if n % (d * d) == 0:
            return False
        d += 1
    return True


def main():
    checks = []
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    # -- the value table, n = 1 .. 60 ------------------------------------
    NMAX = 60
    values = {n: witt(n) for n in range(1, NMAX + 1)}

    # -- base values demanded verbatim by the problem statement ----------
    check("L_1 = 2", values[1] == 2, f"L_1 = {values[1]}")
    check("L_2 = 1", values[2] == 1, f"L_2 = {values[2]}")
    check("L_6 = 9", values[6] == 9, f"L_6 = {values[6]}")
    assert values[1] == 2 and values[2] == 1 and values[6] == 9

    # -- the first twelve values quoted in the write-up ------------------
    first_twelve = [2, 1, 2, 3, 6, 9, 18, 30, 56, 99, 186, 335]
    check("L_1..L_12 = 2,1,2,3,6,9,18,30,56,99,186,335",
          [values[n] for n in range(1, 13)] == first_twelve,
          f"L_1..L_12 = {[values[n] for n in range(1, 13)]}")

    # -- the sharpest witness: 1 and 2 both powers of two, parities differ
    check("1 and 2 are both powers of two",
          is_pow2(1) and is_pow2(2),
          f"is_pow2(1) = {is_pow2(1)}, is_pow2(2) = {is_pow2(2)}")
    check("L_1 = 2 is even and L_2 = 1 is odd (parities differ)",
          (values[1] % 2 == 0) and (values[2] % 2 == 1)
          and (values[1] % 2 != values[2] % 2),
          f"L_1 % 2 = {values[1] % 2}, L_2 % 2 = {values[2] % 2}")

    # -- the fallback witness: 2 and 8 both powers of two, parities differ
    check("2 and 8 are both powers of two with different parities",
          is_pow2(2) and is_pow2(8)
          and (values[2] % 2 != values[8] % 2),
          f"is_pow2(2) = {is_pow2(2)}, is_pow2(8) = {is_pow2(8)}, "
          f"L_2 % 2 = {values[2] % 2}, L_8 % 2 = {values[8] % 2}")

    # -- the "iff" reading fails at n = 6 --------------------------------
    check("6 is not a power of two, yet L_6 = 9 is odd (iff fails)",
          (not is_pow2(6)) and (values[6] % 2 == 1),
          f"is_pow2(6) = {is_pow2(6)}, L_6 % 2 = {values[6] % 2}")

    # -- powers of two are not parity-constant ---------------------------
    pow2s = [n for n in range(1, NMAX + 1) if is_pow2(n)]
    parities = sorted({values[n] % 2 for n in pow2s})
    check("parity is not constant on powers of two (n <= 60)",
          len(parities) >= 2,
          f"powers of two <= {NMAX}: {pow2s}; "
          f"their parities: {sorted({values[n] % 2 for n in pow2s})}")

    # -- the repaired characterisation, checked for all n <= 60 ----------
    def repaired_odd(n):
        """a in {1,2} and odd part squarefree, for n = 2^a * m."""
        return (v2(n) in (1, 2)) and squarefree(odd_part(n))

    mismatches = [n for n in range(2, NMAX + 1)
                  if (values[n] % 2 == 1) != repaired_odd(n)]
    check("repaired characterisation holds for all 2 <= n <= 60: "
          "L_n odd <=> (v2(n) in {1,2} and odd part squarefree)",
          not mismatches,
          "all n agree" if not mismatches
          else f"mismatches: {mismatches}")

    # -- n = 1,2,6,8 details used by the write-up ------------------------
    assert values[1] == 2 and is_pow2(1)
    assert values[2] == 1 and is_pow2(2)
    assert values[6] == 9 and not is_pow2(6)
    assert values[8] == 30 and is_pow2(8)
    assert values[1] % 2 != values[2] % 2
    assert values[2] % 2 != values[8] % 2

    # -- report ----------------------------------------------------------
    line = "=" * 76
    print(line)
    print("Disproof of conjecture 00000000437 -- reproduction")
    print(line)
    print("\nL_n = (1/n) * sum_{d | n} mu(d) * 2^(n/d)   for n = 1..%d" % NMAX)
    print("(mu computed by factorisation; Witt's formula itself is TRUE --")
    print(" only the parity clause of the conjecture is false.)\n")
    print(f"  {'n':>3}  {'L_n':>22}  {'parity':<6}  {'power of 2?':<11}")
    print("  " + "-" * 50)
    for n in range(1, NMAX + 1):
        parity = "odd" if values[n] % 2 else "even"
        print(f"  {n:>3}  {values[n]:>22}  {parity:<6}  "
              f"{str(is_pow2(n)):<11}")

    print("\nThe parity clause fails:")
    print("  * n = 1 and n = 2 are BOTH powers of two, but")
    print(f"      L_1 = {values[1]} (even, {values[1] % 2})   and   "
          f"L_2 = {values[2]} (odd, {values[2] % 2})  -- parities differ.")
    print("    So parity is not a function of 'n is a power of 2'.")
    print("  * fallback (does not count 1 as a power of two):")
    print(f"      n = 2 (L_2 = {values[2]}, odd) and n = 8 (L_8 = {values[8]}, "
          f"even) are powers of two with different parities.")
    print(f"  * the 'iff' reading fails at n = 6: L_6 = {values[6]} is odd, "
          "but 6 is not a power of two.")
    print("\nTrue repaired characterisation (verified for all n <= %d):" % NMAX)
    print("  write n = 2^a * m with m odd;  L_n is odd  <=>  "
          "a in {1,2} and m is squarefree.")

    print("\nChecks:")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"  [{mark}] {name}")
        print(f"         {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000000437 is FALSE.")
        print("  Sharpest witness: is_pow2(1) = is_pow2(2) = True but "
              f"L_1 % 2 = {values[1] % 2} != {values[2] % 2} = L_2 % 2.")
        print("  Fallback:         powers of two 2 and 8 have parities "
              f"{values[2] % 2} and {values[8] % 2}.")
        print(f"  Iff violation:    L_6 = {values[6]} is odd, 6 = 2*3 is not "
              "a power of two.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
