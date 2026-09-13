#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001044.

    Definition: the value set of the Dickson polynomial D_n(x, a) is its image
        over F_q.
    Conjecture: when gcd(n, q^2 - 1) = d > 1 (the non-permutation case), the
        minimum size of the complement of the value set is (q - 1)/d, attained
        at a = 0 (the monomial x^n); every other a gives a strictly larger value
        set.

The conjecture is FALSE.  This script verifies, by brute force over F_q for
every choice of a:

  * Primary witness (q, n) = (3, 2).  Here
        d = gcd(2, 3^2 - 1) = gcd(2, 8) = 2 > 1,   (q - 1)/d = 2/2 = 1,
    and the value sets of a = 0, 1, 2 are {0,1}, {1,2}, {0,2} -- each of size
    2, so the complement has size 1 for every a.  Hence
      - a = 0 is NOT the unique minimiser, and
      - the other a do NOT give a strictly larger value set (they tie a = 0),
    which is the exact negation of the conjecture's second clause.

  * Same phenomenon at (q, n) = (5, 2): all five a give complement 2, and at
    (q, n) = (7, 2): all seven a give complement 3.  In both cases the claimed
    value (q - 1)/d is correct as a *minimum*, but it is not attained
    uniquely at a = 0.

  * Opposite direction at (q, n) = (7, 3): d = gcd(3, 48) = 3, (q - 1)/d = 2,
    but a = 0 gives the LARGEST complement (4) and every nonzero a gives 2.
    This is the exact reverse of the conjecture's "attained at a = 0".

  * Extra breakages of the formula: (5, 3) has d = 3 > 1 and a = 0 permuting
    F_5 (complement 0, while (q - 1)/d = 4/3 is not an integer); (5, 4) has
    d = 4 and (q - 1)/d = 1, but the true minimum complement is 2, attained
    at a = 2, 3, so the claimed value 1 is never attained.

Dickson polynomials use D_0 = 2, D_1 = x, D_k = x D_{k-1} - a D_{k-2}, so
D_2(x, a) = x^2 - 2a and D_3(x, a) = x^3 - 3 a x.

Standard library only.  Python 3.8+.  Exits non-zero if any check fails.
"""

from math import gcd


def dickson_values(q, n, a):
    """[D_n(x, a) mod q for x in F_q], by the Dickson recursion over residues."""
    values = []
    for x in range(q):
        if n == 0:
            values.append(2 % q)
        elif n == 1:
            values.append(x % q)
        else:
            d_prev, d_cur = 2 % q, x % q          # D_0, D_1
            for _ in range(2, n + 1):
                d_prev, d_cur = d_cur, (x * d_cur - a * d_prev) % q
            values.append(d_cur)
    return values


def value_set(q, n, a):
    """The image of D_n(., a) over F_q, as a sorted list of residues."""
    return sorted(set(dickson_values(q, n, a)))


def comp_size(q, n, a):
    """Size of the complement of the value set inside F_q."""
    return q - len(value_set(q, n, a))


def comp_table(q, n):
    """Complement sizes for every a in F_q, as a list indexed by a."""
    return [comp_size(q, n, a) for a in range(q)]


def dickson_d(q, n):
    """d = gcd(n, q^2 - 1), the conjecture's d."""
    return gcd(n, q * q - 1)


def main():
    checks = []          # (name, ok, detail)
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    # ------------------------------------------------------------------
    # 1. Primary witness: (q, n) = (3, 2)
    # ------------------------------------------------------------------
    q0, n0 = 3, 2
    d0 = dickson_d(q0, n0)
    table0 = comp_table(q0, n0)
    claim0 = (q0 - 1) / d0 if (q0 - 1) % d0 == 0 else None

    check("primary witness (3,2): hypothesis d > 1 holds",
          d0 > 1,
          f"d = gcd({n0}, {q0}^2 - 1) = gcd({n0}, {q0 * q0 - 1}) = {d0} > 1")
    check("primary witness (3,2): (q - 1)/d = 2/2 = 1",
          claim0 == 1,
          f"(q - 1)/d = ({q0} - 1)/{d0} = {claim0}")
    check("primary witness (3,2): a = 0 attains complement 1",
          table0[0] == 1,
          f"value set of a = 0 is {value_set(q0, n0, 0)}, complement {table0[0]}")
    check("primary witness (3,2): ALL a give complement 1 (a = 0 not unique)",
          table0 == [1, 1, 1],
          "complement(a) for a = 0,1,2 is " + str(table0) + "; "
          "value sets are "
          + ", ".join(f"a={a}:{value_set(q0, n0, a)}" for a in range(q0)))
    check("primary witness (3,2): other a do NOT give a strictly larger value set",
          all(comp_size(q0, n0, a) == comp_size(q0, n0, 0) for a in range(1, q0)),
          "comp_size(a=1) = comp_size(a=2) = comp_size(a=0) = 1, so the value "
          "sets all have size 2 (not strictly larger)")
    check("primary witness (3,2): minimum complement 1 is attained by >1 a",
          sum(1 for a in range(q0) if comp_size(q0, n0, a) == 1) > 1,
          f"attained by a = {[a for a in range(q0) if comp_size(q0, n0, a) == 1]}")

    # The two structural assertions demanded by the conjecture, negated.
    assert d0 > 1
    assert claim0 == 1
    assert table0 == [1, 1, 1]
    assert table0[0] == claim0

    # ------------------------------------------------------------------
    # 2. The same tie at (5, 2) and (7, 2)
    # ------------------------------------------------------------------
    for (q, n, expected, dv, claim) in [(5, 2, 2, 2, 2), (7, 2, 3, 2, 3)]:
        d = dickson_d(q, n)
        table = comp_table(q, n)
        check(f"tie at ({q},{n}): d = {d} > 1 and (q - 1)/d = {claim}",
              d == dv and d > 1 and (q - 1) // d == claim and (q - 1) % d == 0,
              f"d = gcd({n}, {q * q - 1}) = {d}, (q - 1)/d = ({q} - 1)/{d} = {claim}")
        check(f"tie at ({q},{n}): every a has complement {expected}",
              table == [expected] * q,
              "complement(a) for a = 0..%d is %s" % (q - 1, table))
        check(f"tie at ({q},{n}): a = 0 is not the unique minimiser",
              sum(1 for c in table if c == expected) > 1,
              "the minimum %d is attained by every one of the %d values of a"
              % (expected, q))
        assert table == [expected] * q

    # ------------------------------------------------------------------
    # 3. The reversal at (7, 3)
    # ------------------------------------------------------------------
    q1, n1 = 7, 3
    d1 = dickson_d(q1, n1)
    table1 = comp_table(q1, n1)
    check("reversal (7,3): d = gcd(3,48) = 3 > 1 and (q - 1)/d = 2",
          d1 == 3 and (q1 - 1) % d1 == 0 and (q1 - 1) // d1 == 2,
          f"d = {d1}, (q - 1)/d = ({q1} - 1)/{d1} = {(q1 - 1) // d1}")
    check("reversal (7,3): a = 0 gives complement 4 (the cubes {0,1,6})",
          table1[0] == 4 and value_set(q1, n1, 0) == [0, 1, 6],
          f"value set of a = 0 is {value_set(q1, n1, 0)}, complement {table1[0]}")
    check("reversal (7,3): every nonzero a gives complement 2, strictly beating a = 0",
          all(table1[a] == 2 for a in range(1, q1)) and table1[0] > 2,
          "complement(a) for a = 0..6 is " + str(table1) + "; a = 0 is the WORST, "
          "the exact reverse of the conjecture")
    check("reversal (7,3): a = 0 maximises the complement",
          all(table1[a] <= table1[0] for a in range(q1)),
          f"max complement = {max(table1)} at a = "
          f"{[a for a in range(q1) if table1[a] == max(table1)]}")
    check("reversal (7,3): a = 0 exceeds the conjectured minimum (q - 1)/d = 2",
          table1[0] > (q1 - 1) // d1,
          f"comp(a=0) = {table1[0]} > {(q1 - 1) // d1} = (q - 1)/d")
    assert table1[0] == 4 and table1[0] > table1[1] == 2

    # ------------------------------------------------------------------
    # 4. Extra breakages of the formula
    # ------------------------------------------------------------------
    # (5,3): d = 3 > 1, yet (q - 1)/d = 4/3 is not an integer and a = 0 permutes.
    qa, na = 5, 3
    da = dickson_d(qa, na)
    check("(5,3): d = gcd(3,24) = 3 > 1 but d does NOT divide q - 1",
          da == 3 and (qa - 1) % da != 0,
          f"d = {da}; (q - 1) mod d = ({qa} - 1) mod {da} = {(qa - 1) % da} != 0, "
          f"so (q - 1)/d = {qa - 1}/{da} is not an integer")
    check("(5,3): a = 0 permutes F_5, complement 0",
          comp_size(qa, na, 0) == 0 and value_set(qa, na, 0) == [0, 1, 2, 3, 4],
          f"value set of a = 0 is {value_set(qa, na, 0)}, complement "
          f"{comp_size(qa, na, 0)}")

    # (5,4): d = 4, (q - 1)/d = 1, but the true minimum is 2 at a = 2, 3.
    qb, nb = 5, 4
    db = dickson_d(qb, nb)
    tableb = comp_table(qb, nb)
    check("(5,4): d = gcd(4,24) = 4 and (q - 1)/d = 1",
          db == 4 and (qb - 1) // db == 1,
          f"d = {db}, (q - 1)/d = ({qb} - 1)/{db} = {(qb - 1) // db}")
    check("(5,4): the claimed value 1 is never attained; true minimum is 2",
          min(tableb) == 2 and 1 not in tableb,
          "complement(a) for a = 0..4 is " + str(tableb)
          + "; min = 2, and complement 1 occurs for no a")

    # ------------------------------------------------------------------
    # 5. Report
    # ------------------------------------------------------------------
    line = "=" * 74
    print(line)
    print("Disproof of conjecture 00000001044 -- reproduction")
    print(line)

    print("\n[1] Primary witness  (q, n) = (3, 2)")
    print(f"    d = gcd(n, q^2 - 1) = gcd(2, 8) = {d0} > 1    "
          f"(q - 1)/d = {claim0}")
    for a in range(q0):
        print(f"    a = {a}: value set {value_set(q0, n0, a)}, "
              f"|image| = {len(value_set(q0, n0, a))}, "
              f"complement = {comp_size(q0, n0, a)}")
    print("    => all three a give complement 1: a = 0 is NOT the unique")
    print("       minimiser, and the other a do NOT give a strictly larger")
    print("       value set.  The conjecture is FALSE already here.")

    print("\n[2] Same tie at (5, 2) and (7, 2)")
    for (q, n) in ((5, 2), (7, 2)):
        d = dickson_d(q, n)
        table = comp_table(q, n)
        print(f"    (q, n) = ({q}, {n}): d = gcd({n}, {q * q - 1}) = {d}, "
              f"(q - 1)/d = {(q - 1) // d}")
        print(f"        complement(a) for a = 0..{q - 1}: {table}")

    print("\n[3] Reversal at (7, 3)")
    print(f"    d = gcd(3, 48) = {d1}, (q - 1)/d = {(q1 - 1) // d1}")
    print(f"    complement(a) for a = 0..6: {table1}")
    print("    => a = 0 gives the LARGEST complement (4); every nonzero a")
    print("       gives 2.  The conjecture has the direction backwards.")

    print("\n[4] Extra breakages of the formula")
    print(f"    (5,3): d = {da}, d divides q - 1? {(qa - 1) % da == 0}; "
          f"a = 0 complement = {comp_size(qa, na, 0)} (permutation)")
    print(f"    (5,4): d = {db}, (q - 1)/d = {(qb - 1) // db}; "
          f"complement(a) for a = 0..4 = {tableb} (min 2, not 1)")

    print("\n[5] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000001044 is FALSE.")
        print("  (3,2): d = gcd(2,8) = 2 > 1, (q-1)/d = 1, but a = 0,1,2 all give")
        print("         complement 1 -- a = 0 is not unique and the other a do")
        print("         not give a strictly larger value set.")
        print("  (5,2) / (7,2): every a ties a = 0 (complements 2 / 3).")
        print("  (7,3): a = 0 gives the LARGEST complement (4), nonzero a give 2.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
