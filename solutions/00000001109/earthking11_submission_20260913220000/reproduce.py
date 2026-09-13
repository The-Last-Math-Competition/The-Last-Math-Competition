#!/usr/bin/env python3
"""Reproduce the refutation of conjecture 00000001109.

    Definition: the exponents of a Coxeter system (the roots of its
                characteristic polynomial).
    Conjecture: the exponent set of a non-crystallographic Coxeter group
                contains, besides (h, 1), some exponent of multiplicity >= 2
                (universality of multiplicity structure).

VERDICT: FALSE -- under the UNIVERSAL reading over irreducible finite
non-crystallographic Coxeter groups.

For a finite Coxeter group the exponents are the degrees minus one, and the
Coxeter number h is the largest DEGREE, so h is not itself an exponent.  Every
IRREDUCIBLE finite Coxeter group has pairwise distinct degrees, hence pairwise
distinct exponents, hence every exponent has multiplicity exactly 1.  The
complete list of irreducible finite non-crystallographic types is

    H3, H4, and I2(m) for m >= 5

(I2(3) = A2, I2(4) = B2, I2(6) = G2 are crystallographic and I2(2) = A1 x A1 is
reducible).  This script encodes their exponent lists, computes the
multiplicities, and asserts that every exponent has multiplicity 1.

HONEST SCOPE NOTE (asserted at the end, so the boundary is visible in code):
under an EXISTENTIAL reading that admits REDUCIBLE groups the conjecture is
TRUE.  The reducible group A1 x H3 is non-crystallographic with exponent
multiset {1, 1, 5, 9}, so exponent 1 has multiplicity 2.

Standard library only.  Python 3.8+.  Exits non-zero if any check fails.
"""

from collections import Counter


# ---------------------------------------------------------------------------
# 1. Exponent tables for the irreducible finite non-crystallographic types.
#    exponents = degrees - 1; h = max degree.
# ---------------------------------------------------------------------------

def exps_h3():
    """H3: degrees 2, 6, 10 -> exponents 1, 5, 9; h = 10."""
    degrees = [2, 6, 10]
    return degrees, [d - 1 for d in degrees], max(degrees)


def exps_h4():
    """H4: degrees 2, 12, 20, 30 -> exponents 1, 11, 19, 29; h = 30."""
    degrees = [2, 12, 20, 30]
    return degrees, [d - 1 for d in degrees], max(degrees)


def exps_i2(m):
    """I2(m): degrees 2, m -> exponents 1, m - 1; h = m."""
    degrees = [2, m]
    return degrees, [d - 1 for d in degrees], max(degrees)


def multiplicities(exponents):
    """Return {exponent: multiplicity} for an exponent list."""
    return dict(Counter(exponents))


def all_multiplicity_one(exponents):
    """True iff every exponent occurs exactly once."""
    return all(n == 1 for n in multiplicities(exponents).values())


def exps_a1():
    """A1: degree 2 -> exponent 1."""
    degrees = [2]
    return degrees, [d - 1 for d in degrees], max(degrees)


def reducible_a1_h3_exponents():
    """A1 x H3: direct products ADD exponents, so 1 (from A1) meets 1 (from H3)."""
    _, a1, _ = exps_a1()
    _, h3, _ = exps_h3()
    return a1 + h3


def main():
    checks = []          # (name, ok, detail)
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    # ------------------------------------------------------------------
    # 2. The irreducible types: tables and multiplicity one.
    # ------------------------------------------------------------------
    table = []           # (name, degrees, h, exponents)

    degrees, exps, h = exps_h3()
    table.append(("H3", degrees, h, exps))
    degrees, exps, h = exps_h4()
    table.append(("H4", degrees, h, exps))
    for m in range(5, 13):                     # I2(5) .. I2(12)
        degrees, exps, h = exps_i2(m)
        table.append((f"I2({m})", degrees, h, exps))

    expected = {
        "H3": [1, 5, 9],
        "H4": [1, 11, 19, 29],
        "I2(5)": [1, 4],
        "I2(6)": [1, 5],
        "I2(7)": [1, 6],
        "I2(8)": [1, 7],
        "I2(9)": [1, 8],
        "I2(10)": [1, 9],
        "I2(11)": [1, 10],
        "I2(12)": [1, 11],
    }

    for name, degrees, h, exps in table:
        check(f"{name}: exponent table",
              exps == expected[name],
              f"degrees {degrees}, h = {h}, exponents {exps}")

    for name, degrees, h, exps in table:
        ms = multiplicities(exps)
        check(f"{name}: every exponent has multiplicity 1",
              all_multiplicity_one(exps),
              f"multiplicities {ms}")

    # 1 != m - 1 exactly when m != 2; in particular for all m >= 5.
    for m in range(5, 13):
        _, _, _ = exps_i2(m)
        check(f"I2({m}): 1 != m - 1 (distinct exponents)",
              1 != m - 1,
              f"1 vs m - 1 = {m - 1}")

    # ------------------------------------------------------------------
    # 3. The (h, 1) reading: h is a degree, not an exponent.
    # ------------------------------------------------------------------
    for name, degrees, h, exps in table:
        check(f"{name}: h = {h} is NOT an exponent",
              h not in exps,
              f"h = {h}, max exponent = {max(exps)}")

    # Adjoining h to the exponent list does not create a repeat either.
    _, h3e, h3h = exps_h3()
    _, h4e, h4h = exps_h4()
    check("H3: exponents plus h = {1,5,9,10} stay all-distinct",
          all_multiplicity_one(h3e + [h3h]),
          f"{h3e + [h3h]}")
    check("H4: exponents plus h = {1,11,19,29,30} stay all-distinct",
          all_multiplicity_one(h4e + [h4h]),
          f"{h4e + [h4h]}")

    # ------------------------------------------------------------------
    # 4. HONEST SCOPE BOUNDARY: reducible A1 x H3 DOES have a repeat.
    # ------------------------------------------------------------------
    a1h3 = reducible_a1_h3_exponents()
    a1h3_ms = multiplicities(a1h3)
    check("SCOPE: reducible A1 x H3 exponent multiset is {1,1,5,9}",
          sorted(a1h3) == [1, 1, 5, 9],
          f"A1 x H3 exponents = {a1h3}")
    check("SCOPE: in A1 x H3 the exponent 1 has multiplicity 2",
          a1h3_ms.get(1) == 2,
          f"multiplicities {a1h3_ms}")
    check("SCOPE: reducible A1 x H3 violates the 'multiplicity 1' claim",
          not all_multiplicity_one(a1h3),
          "so an EXISTENTIAL reading of the conjecture is TRUE")

    # Hard assertions demanded by the write-up.
    assert exps_h3()[1] == [1, 5, 9]
    assert exps_h4()[1] == [1, 11, 19, 29]
    assert all_multiplicity_one(exps_h3()[1])
    assert all_multiplicity_one(exps_h4()[1])
    for m in range(5, 13):
        assert all_multiplicity_one(exps_i2(m)[1]), m
    assert multiplicities(a1h3).get(1) == 2

    # ------------------------------------------------------------------
    # 5. Report.
    # ------------------------------------------------------------------
    line = "=" * 72
    print(line)
    print("Refutation of conjecture 00000001109 -- reproduction")
    print(line)

    print("\n[1] Irreducible finite non-crystallographic types")
    print(f"    {'type':<8} {'degrees':<20} {'h':>4}  {'exponents':<16} "
          f"{'multiplicities'}")
    for name, degrees, h, exps in table:
        print(f"    {name:<8} {str(degrees):<20} {h:>4}  {str(exps):<16} "
              f"{multiplicities(exps)}")
    print("    => every exponent has multiplicity 1; no exponent has "
          "multiplicity >= 2.")

    print("\n[2] The (h, 1) reading: h is the largest DEGREE, not an exponent")
    for name, degrees, h, exps in table:
        print(f"    {name:<8} h = {h:<4} exponents {exps}  "
              f"h in exponents? {h in exps}")
    print(f"    H3 + h = {h3e + [h3h]}  (still all-distinct)")
    print(f"    H4 + h = {h4e + [h4h]}  (still all-distinct)")

    print("\n[3] SCOPE BOUNDARY: reducible A1 x H3")
    print(f"    A1 x H3 exponents = {a1h3}  "
          f"multiplicities = {a1h3_ms}")
    print("    => exponent 1 has multiplicity 2: under an EXISTENTIAL")
    print("       reading admitting reducible groups the conjecture is TRUE.")
    print("       The refutation uses the UNIVERSAL reading over irreducible")
    print("       types, which the conjecture's wording ('universality of")
    print("       multiplicity structure') indicates.")

    print("\n[4] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000001109 is FALSE")
        print("      under the universal reading over irreducible finite")
        print("      non-crystallographic Coxeter groups (H3, H4, I2(m), m>=5):")
        print("      all exponents are pairwise distinct (multiplicity 1).")
        print("      Scope: reducible A1 x H3 has exponent 1 of multiplicity 2.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
