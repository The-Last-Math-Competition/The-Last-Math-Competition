#!/usr/bin/env python3
"""Reproduce the DISPROOF of conjecture 00000001203.

    Definition: An addition-subtraction game is a subtraction game whose legal
    moves are the fixed values in a set S; the SG period is the least positive
    period of g(n).
    Conjecture: If S subset {1,...,k}, then the period of g divides 2^k - 1 if
    and only if S is nonempty and does not contain k; when k in S the period is
    exactly k + 1.

The conjecture is FALSE.  The SG sequence of a subtraction game with move set S
is computed here by the mex recursion

    g(n) = mex { g(n - s) : s in S, s <= n } ,   g(0) = 0,

and its least positive period is found by direct search over the first
``terms`` values.

Primary witness:  S = {1, 3} with k = 3.
    g = 0, 1, 0, 1, 0, 1, ...  (g(n) = n mod 2), hence the least period is 2.
    Since k = 3 is in S, the conjecture demands period exactly k + 1 = 4.
    But max(S) = 3 equals the ambient bound k = 3, so this witness is immune
    to the ambiguity of how k is read (ambient bound vs. max of S).

Secondary witness:  S = {2} with k = 2, least period 4, whereas k in S demands
    period exactly k + 1 = 3.

Clause-1 witness:  S = {1, 2}, least period 3, and 3 divides 2^2 - 1 = 3.
    Under the charitable reading k = max(S) = 2 the conjecture requires the
    period NOT to divide 2^k - 1, which fails; under the literal ambient-bound
    reading with k = 3 the set {1,2} is a proper subset of {1,2,3}, the right
    hand side "3 not in S" is true, and the conjecture wrongly requires
    3 | 2^3 - 1 = 7.  (No reading survives.)

Standard library only. Python 3.8+. Exits non-zero if any check fails.
"""

from itertools import combinations

# --------------------------------------------------------------------------
# SG machinery
# --------------------------------------------------------------------------


def mex(values):
    """Minimal excludant of an iterable of non-negative integers."""
    seen = set(values)
    m = 0
    while m in seen:
        m += 1
    return m


def sg_sequence(S, terms):
    """First ``terms`` SG values of the subtraction game with moves S."""
    g = []
    for n in range(terms):
        moves = [g[n - s] for s in S if s <= n]
        g.append(mex(moves))
    return g


def least_period(seq):
    """Least p >= 1 with seq[i] == seq[i-p] for all i >= p, or None.

    Subtraction-game SG sequences are ultimately periodic; for the move sets
    considered here they are periodic from n = 0, and the search over a long
    prefix (>= 300 terms) returns the true least period.
    """
    N = len(seq)
    for p in range(1, N // 3 + 1):
        if all(seq[i] == seq[i - p] for i in range(p, N)):
            return p
    return None


def nonempty_subsets(k):
    """All nonempty subsets of {1, ..., k}, as sorted tuples."""
    elems = list(range(1, k + 1))
    for r in range(1, k + 1):
        for combo in combinations(elems, r):
            yield combo


# --------------------------------------------------------------------------
# Conjecture predicates (the two readings of the parameter k)
# --------------------------------------------------------------------------


def divides(a, b):
    """True iff a divides b."""
    return b % a == 0


def clause1_holds(period, S, k):
    """The iff: period | 2^k - 1  <=>  (S nonempty and k not in S)."""
    lhs = divides(period, 2 ** k - 1)
    rhs = (len(S) > 0) and (k not in S)
    return lhs == rhs


def clause2_holds(period, S, k):
    """The 'when k in S the period is exactly k + 1' clause."""
    if k in S:
        return period == k + 1
    return True


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------


def main():
    TERMS = 600
    checks = []
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    line = "=" * 78
    print(line)
    print("Disproof of conjecture 00000001203 -- reproduction")
    print(line)

    # ------------------------------------------------------------------
    # 1. Primary witness: S = {1, 3}, k = 3, claimed period 4
    # ------------------------------------------------------------------
    S_primary = (1, 3)
    k_primary = 3
    g_primary = sg_sequence(S_primary, TERMS)
    per_primary = least_period(g_primary)

    print("\n[1] PRIMARY WITNESS  S = {1, 3},  k = 3  (max(S) = k, so readings agree)")
    print(f"    first terms: {g_primary[:12]} ...")
    print(f"    least period: {per_primary}   (conjecture, since 3 in S, claims k+1 = 4)")

    closed_form_ok = all(g_primary[n] == n % 2 for n in range(TERMS))
    check("primary: g(n) = n mod 2 for the first %d terms" % TERMS,
          closed_form_ok,
          "verified" if closed_form_ok else "closed form mismatch")
    check("primary: least period of S = {1,3} is 2",
          per_primary == 2,
          f"least period = {per_primary}")
    check("primary: the conjecture claims period k+1 = 4 because 3 in S",
          k_primary in S_primary,
          f"3 in S = {set(S_primary)}")
    check("primary: 2 != 4, so the second clause is violated (both readings)",
          per_primary != k_primary + 1,
          f"actual {per_primary} vs claimed {k_primary + 1}")
    # Under the charitable reading k = max(S) the number k is again 3.
    check("primary: interpretation-free, because max(S) = 3 = ambient k",
          max(S_primary) == k_primary,
          f"max(S) = {max(S_primary)}, ambient k = {k_primary}")

    # ------------------------------------------------------------------
    # 2. Secondary witness: S = {2}, k = 2, claimed period 3
    # ------------------------------------------------------------------
    S_secondary = (2,)
    k_secondary = 2
    g_secondary = sg_sequence(S_secondary, TERMS)
    per_secondary = least_period(g_secondary)

    print("\n[2] SECONDARY WITNESS  S = {2},  k = 2")
    print(f"    first terms: {g_secondary[:12]} ...")
    print(f"    least period: {per_secondary}   (conjecture, since 2 in S, claims k+1 = 3)")
    check("secondary: least period of S = {2} is 4",
          per_secondary == 4,
          f"least period = {per_secondary}")
    check("secondary: 4 != 3 = k+1, violating the second clause",
          per_secondary != k_secondary + 1,
          f"actual {per_secondary} vs claimed {k_secondary + 1}")

    # ------------------------------------------------------------------
    # 3. Clause-1 witness: S = {1, 2}
    # ------------------------------------------------------------------
    S_clause1 = (1, 2)
    g_clause1 = sg_sequence(S_clause1, TERMS)
    per_clause1 = least_period(g_clause1)

    print("\n[3] CLAUSE-1 WITNESS  S = {1, 2},  least period 3")
    print(f"    first terms: {g_clause1[:12]} ...")
    print(f"    least period: {per_clause1}   and 3 divides 2^2 - 1 = 3")
    print("    charitable reading k = max(S) = 2: the iff requires the period")
    print("    NOT to divide 2^2 - 1 = 3, but 3 | 3 -> clause 1 fails.")
    print("    ambient reading k = 3 (S = {1,2} is a PROPER subset of {1,2,3}):")
    print("    the iff requires 3 | 2^3 - 1 = 7 (since 3 not in S) but 3 does not")
    print("    divide 7 -> clause 1 fails again.")
    check("clause1: least period of S = {1,2} is 3",
          per_clause1 == 3,
          f"least period = {per_clause1}")
    check("clause1: 3 divides 2^2 - 1 = 3 (charitable reading k = max(S) = 2 violated)",
          divides(per_clause1, 2 ** 2 - 1),
          f"3 | {2 ** 2 - 1} = {divides(per_clause1, 2 ** 2 - 1)}")
    check("clause1: under ambient k = 3, 3 does not divide 2^3 - 1 = 7",
          not divides(per_clause1, 2 ** 3 - 1),
          f"3 | {2 ** 3 - 1} = {divides(per_clause1, 2 ** 3 - 1)}")

    # ------------------------------------------------------------------
    # 4. Full tables for k = 2, 3, 4 over all nonempty S subset {1,...,k}
    # ------------------------------------------------------------------
    print("\n[4] LEAST PERIODS FOR ALL NONEMPTY S, AND VIOLATIONS UNDER BOTH READINGS")
    tables = {}
    for K in (2, 3, 4):
        rows = []
        for S in nonempty_subsets(K):
            g = sg_sequence(S, TERMS)
            per = least_period(g)
            proper = (len(S) != K)  # S is a proper subset of {1,...,K}
            # Ambient-bound reading: k = K.
            amb_ok = clause1_holds(per, S, K) and clause2_holds(per, S, K)
            # Charitable reading: k = max(S).
            kc = max(S)
            char_ok = clause1_holds(per, S, kc) and clause2_holds(per, S, kc)
            rows.append((S, per, proper, K, amb_ok, kc, char_ok))
        tables[K] = rows

        print(f"\n    k = {K}:  {'S':<12} {'period':>6}  {'proper?':>7}  "
              f"{'ambient k=%d' % K:>14}  {'charitable k=max(S)':>20}")
        for S, per, proper, kk, amb_ok, kc, char_ok in rows:
            print(f"    {'':<4}  {str(set(S)):<12} {per:>6}  "
                  f"{str(proper):>7}  {('holds' if amb_ok else 'VIOLATED'):>14}  "
                  f"{('holds' if char_ok else 'VIOLATED'):>20}  (k={kc})")

    # The primary and secondary witnesses must show up as violations.
    def find(K, S):
        for row in tables[K]:
            if row[0] == S:
                return row
        raise AssertionError((K, S))

    r_prim = find(3, S_primary)
    check("table: S = {1,3}, k = 3 is VIOLATED under both readings",
          (not r_prim[4]) and (not r_prim[6]),
          f"ambient={'VIOLATED' if not r_prim[4] else 'holds'}, "
          f"charitable={'VIOLATED' if not r_prim[6] else 'holds'}")
    r_sec = find(2, S_secondary)
    check("table: S = {2}, k = 2 is VIOLATED under both readings",
          (not r_sec[4]) and (not r_sec[6]),
          f"ambient={'VIOLATED' if not r_sec[4] else 'holds'}, "
          f"charitable={'VIOLATED' if not r_sec[6] else 'holds'}")
    r_c1 = find(2, S_clause1)
    check("table: S = {1,2}, k = 2 is VIOLATED under both readings",
          (not r_c1[4]) and (not r_c1[6]),
          f"ambient={'VIOLATED' if not r_c1[4] else 'holds'}, "
          f"charitable={'VIOLATED' if not r_c1[6] else 'holds'}")

    # Under the ambient reading, S = {1,2} as a PROPER subset of {1,2,3} also fails.
    r_c1_amb3 = find(3, S_clause1)
    check("table: ambient k = 3, S = {1,2} (proper) is VIOLATED",
          not r_c1_amb3[4],
          "clause 1 fails: 3 not in S but 3 does not divide 2^3 - 1 = 7")

    # There must exist violations in every k = 2,3,4 table (conjecture is FALSE).
    for K in (2, 3, 4):
        any_amb = any(not row[4] for row in tables[K])
        any_char = any(not row[6] for row in tables[K])
        check(f"table k = {K}: at least one violating S exists under both readings",
              any_amb and any_char,
              f"ambient violations: {sum(1 for r in tables[K] if not r[4])}, "
              f"charitable violations: {sum(1 for r in tables[K] if not r[6])}")

    # ------------------------------------------------------------------
    # 5. Report
    # ------------------------------------------------------------------
    print("\n[5] CHECKS")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000001203 is FALSE.")
        print("  primary:    S = {1,3}, k = 3, least period 2 != k+1 = 4 (both readings);")
        print("  secondary:  S = {2},   k = 2, least period 4 != k+1 = 3;")
        print("  clause 1:   S = {1,2}, least period 3, 3 | 2^2 - 1 = 3, so no")
        print("              reading of k survives.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
