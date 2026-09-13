#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000002048.

    Definition: the 3-fold sum of F_p is the coverage of
        {x + y + z : x, y, z in A}.
    Conjecture: for |A| > (p - 1)/3, the 3-fold sum covers F_p \\ {0}
    (the threshold is exact); the threshold is optimal (attained critically by
    the cubic-residue set at the threshold).

The conjecture is FALSE.  This script verifies two things by brute force.

  * Witness: p = 5, A = {0, 1}.  Here |A| = 2 > 4/3 = (5 - 1)/3, but
        3A = {0, 1, 2, 3}  misses  4 in F_5 \\ {0}.
    So the main claim fails at the smallest non-trivial prime.

  * General family: for every prime p = 2 (mod 3), the set
        A = {0, 1, ..., (p - 2)/3}
    has |A| = (p + 1)/3 > (p - 1)/3, and 3A = {0, 1, ..., p - 2} misses p - 1.
    Verified here for all primes p <= 100.  (Cauchy-Davenport gives only
    |3A| >= min(p, 3|A| - 2) = p - 1 at this size, so it does not force
    coverage.)

Standard library only.  Python 3.8+.  Exits non-zero if any check fails.
"""

from itertools import product


def is_prime(n):
    """Bounded trial-division primality test."""
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def sum3(p, A):
    """The 3-fold sum {x + y + z mod p : x, y, z in A}, as a sorted list."""
    residues = {(x + y + z) % p for x, y, z in product(A, repeat=3)}
    return sorted(residues)


def covers_nonzero(p, A):
    """True iff the 3-fold sum contains every nonzero residue of F_p."""
    S = set(sum3(p, A))
    return all(s in S for s in range(1, p))


def general_family(p):
    """A = {0, 1, ..., (p - 2) // 3}, the extremal family for p = 2 (mod 3)."""
    return list(range((p - 2) // 3 + 1))


def main():
    checks = []          # (name, ok, detail)
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    # ------------------------------------------------------------------
    # 1. The witness: p = 5, A = {0, 1}
    # ------------------------------------------------------------------
    p0 = 5
    A0 = [0, 1]
    S0 = sum3(p0, A0)
    nonzero0 = [s for s in range(1, p0)]

    check("witness: |A| = 2",
          len(A0) == 2,
          f"A = {A0}, |A| = {len(A0)}")
    check("witness: |A| > (p - 1)/3, i.e. 2 > 4/3",
          len(A0) > (p0 - 1) / 3,
          f"|A| = {len(A0)} > {(p0 - 1) / 3:.6f} = (5 - 1)/3; "
          f"cross-multiplied 3*{len(A0)} = {3 * len(A0)} > {p0 - 1} = p - 1")
    check("witness: 3A = {0, 1, 2, 3} exactly",
          S0 == [0, 1, 2, 3],
          f"3A = {S0}")
    check("witness: 4 is NOT in 3A (the required assertion)",
          4 not in S0,
          f"4 in 3A is {4 in S0}; 3A = {S0}")
    check("witness: 4 is a nonzero element of F_5",
          4 % p0 != 0,
          "4 mod 5 = 4 != 0")
    check("witness: 3A does NOT cover F_5 \\ {0}",
          not all(s in set(S0) for s in nonzero0),
          f"F_5 \\ {{0}} = {nonzero0}; missing "
          f"{[s for s in nonzero0 if s not in set(S0)]}")

    # The two assertions demanded verbatim by the problem statement.
    assert len(A0) == 2
    assert 2 > (5 - 1) / 3
    assert 4 not in S0
    assert not covers_nonzero(p0, A0)

    # ------------------------------------------------------------------
    # 2. The general family, all primes p <= 100
    # ------------------------------------------------------------------
    bound = 100
    family_primes = [q for q in range(2, bound + 1)
                     if is_prime(q) and q % 3 == 2]

    failing = []
    table = []
    for q in family_primes:
        A = general_family(q)
        T = sum3(q, A)
        size_ok = 3 * len(A) > q - 1          # |A| > (q - 1)/3
        exact = T == list(range(q - 1))        # 3A = {0, ..., q - 2}
        misses = (q - 1) not in T
        not_cover = not covers_nonzero(q, A)
        ok = size_ok and exact and misses and not_cover
        if not ok:
            failing.append((q, A, T))
        table.append((q, len(A), T))

    check(f"general family: {len(family_primes)} primes p <= {bound} with p = 2 (mod 3)",
          len(family_primes) == 13,
          f"p = {family_primes}")
    check("general family: every such p satisfies 3|A| > p - 1 and "
          "3A = {0,...,p-2}, missing p-1",
          not failing,
          "all pass" if not failing else f"failures: {failing}")

    # Explicit assertions for the three primes the write-up tabulates.
    for q in (5, 11, 17):
        A = general_family(q)
        T = sum3(q, A)
        assert 3 * len(A) > q - 1, q
        assert T == list(range(q - 1)), q
        assert (q - 1) not in T, q
        assert not covers_nonzero(q, A), q

    # ------------------------------------------------------------------
    # 3. Report
    # ------------------------------------------------------------------
    line = "=" * 72
    print(line)
    print("Disproof of conjecture 00000002048 -- reproduction")
    print(line)

    print("\n[1] Witness  p = 5,  A = {0, 1}")
    print(f"    |A| = {len(A0)} > (p - 1)/3 = {(p0 - 1) / 3:.6f}")
    print(f"    3A  = {S0}")
    print(f"    F_5 \\ {{0}} = {nonzero0}, missing "
          f"{[s for s in nonzero0 if s not in set(S0)]}")
    print("    => the conjecture's main claim fails already at p = 5.")

    print("\n[2] General family  A = {0, ..., (p-2)/3},  p = 2 (mod 3),  p <= 100")
    print(f"    {'p':>4}  {'|A|':>4}  {'3|A|':>5}  {'p-1':>4}  "
          f"{'3A':<24}  missing")
    for q in family_primes:
        A = general_family(q)
        T = sum3(q, A)
        print(f"    {q:>4}  {len(A):>4}  {3 * len(A):>5}  {q - 1:>4}  "
              f"{str(T):<24}  {q - 1}")

    print("\n[3] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000002048 is FALSE.")
        print(f"  witness p = 5, A = {{0,1}}: |A| = 2 > 4/3 but 4 not in 3A;")
        print(f"  general family refutes all {len(family_primes)} primes "
              f"p <= {bound} with p = 2 (mod 3).")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
