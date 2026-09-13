#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000003837.

    Definition: the star involution * denotes the crystal involution reversing
        all simple arrow directions, always existing in finite type.
    Conjecture: the number of fixed points of * in B(lambda) is always odd, and
        when lambda = -w0 lambda the number of fixed points is at least 3.

The conjecture is FALSE.  This script verifies, with the Python standard
library only, the following elementary refutation.

  * Elementary parity lemma.  For any involution of a finite set, the non-fixed
    points pair up in 2-cycles, so #fixed = |set| (mod 2).  In particular
    #fixed is even whenever the set has even cardinality.

  * Type A1, lambda = omega_1.  B(omega_1) is the two-element sl2 crystal with
    weights +1, -1 and a single arrow.  The only involution reversing that
    arrow is the swap, which has 0 fixed points.  So #fixed = 0 is EVEN,
    contradicting "always odd", and 0 < 3, contradicting "at least 3".
    In type A1 the longest element w0 = s1 acts by -1 on weights, so -w0 = id
    and lambda = -w0 lambda holds for EVERY lambda, in particular omega_1.

  * Stronger statement:  for B(k omega_1), a chain with weights
    k, k-2, ..., -k, the arrow-reversing involution is j -> k - j, whose fixed
    points are exactly the weight-0 elements.  There is one such element when k
    is even and none when k is odd, so the fixed-point count is 1 for even k and
    0 for odd k.  Hence over all of type A1 the maximum is 1, and the
    "at least 3" clause fails for EVERY lambda in type A1, not merely as a
    parity artefact.

  * Convention robustness.  Every involution of a two-element set has 0 or 2
    fixed points, both even; and the arrow-reversing involution of B(omega_1)
    is unique.  So no redefinition of the star can rescue the claim.

Prints PASS and exits 0 exactly when every check holds; otherwise prints FAIL
and exits non-zero.  Python 3.8+.
"""

CHECK_FAILURES = []


def check(name, ok, detail=""):
    """Record one check; print it immediately."""
    ok = bool(ok)
    mark = "ok  " if ok else "FAIL"
    print(f"    [{mark}] {name}")
    if detail:
        print(f"           {detail}")
    if not ok:
        CHECK_FAILURES.append(name)
    return ok


# ----------------------------------------------------------------------
# The crystal B(k omega_1) of type A1
# ----------------------------------------------------------------------

def crystal(k):
    """Return (elements, weight, f, e) for the chain B(k omega_1).

    Elements are positions 0, 1, ..., k.  The weight of position j is k - 2j,
    so the weights are k, k-2, ..., -k.  `f` is the lowering operator
    (j -> j+1, undefined at the top k) and `e` the raising operator
    (j -> j-1, undefined at the bottom 0); arrows are undefined at the ends and
    represented by None.
    """
    elements = list(range(k + 1))

    def weight(j):
        return k - 2 * j

    def f(j):
        return j + 1 if j < k else None

    def e(j):
        return j - 1 if j > 0 else None

    return elements, weight, f, e


def star(k, j):
    """The arrow-reversing involution of B(k omega_1): j -> k - j."""
    return k - j


def star_opt(k, x):
    """`star` extended to None (undefined arrows stay undefined)."""
    return None if x is None else star(k, x)


def fixed_count(k):
    """Number of j in B(k omega_1) with star(j) = j."""
    return sum(1 for j in range(k + 1) if star(k, j) == j)


# ----------------------------------------------------------------------
# main
# ----------------------------------------------------------------------

def main():
    line = "=" * 72
    print(line)
    print("Disproof of conjecture 00000003837 -- reproduction")
    print(line)

    # ------------------------------------------------------------------
    # 1. The parity lemma, in the sharpest possible instance
    # ------------------------------------------------------------------
    print("\n[1] Elementary parity lemma")
    print("    For any involution of a finite set, non-fixed points pair up in")
    print("    2-cycles, so #fixed == |set| (mod 2).")

    # Brute force over all functions on a 2-element set: involutions only.
    two_set = [0, 1]
    functions = [
        {0: a, 1: b} for a in two_set for b in two_set
    ]
    involutions = [
        s for s in functions if all(s[s[x]] == x for x in two_set)
    ]
    counts = sorted(
        sum(1 for x in two_set if s[x] == x) for s in involutions
    )
    check("every involution of a 2-element set has an EVEN fixed count",
          all(c % 2 == 0 for c in counts),
          f"the {len(involutions)} involutions have fixed counts {counts} "
          f"(each equal to 0 or 2)")

    # ------------------------------------------------------------------
    # 2. The counterexample: lambda = omega_1 (k = 1)
    # ------------------------------------------------------------------
    print("\n[2] Type A1, lambda = omega_1  (k = 1)")
    els, wt, f, e = crystal(1)
    star_is_involution = all(star(1, star(1, j)) == j for j in els)
    reverses_f = all(f(star(1, j)) == star_opt(1, e(j)) for j in els)
    reverses_e = all(e(star(1, j)) == star_opt(1, f(j)) for j in els)
    negates_weight = all(wt(star(1, j)) == -wt(j) for j in els)

    check("B(omega_1) has exactly 2 elements",
          len(els) == 2, f"elements = {els}, weights = {[wt(j) for j in els]}")
    check("the star j -> 1-j is an involution",
          star_is_involution, "star(star(j)) = j for all j")
    check("it reverses the unique arrow (f and e exchanged)",
          reverses_f and reverses_e,
          "f(star j) = star(e j) and e(star j) = star(f j) for all j")
    check("it negates weights (the type-A1 star condition)",
          negates_weight, f"weights become {[wt(star(1, j)) for j in els]}")

    fc1 = fixed_count(1)
    check("the arrow-reversing involution is the swap, with 0 fixed points",
          fc1 == 0, f"fixed points of j -> 1-j: {fc1}")

    # Uniqueness of the arrow-reversing involution of B(omega_1).
    # A candidate s : {0,1} -> {0,1} reverses the arrow iff, for every j,
    #     f(s(j)) = s(e(j))     (lifting None through s as undefined).
    reversing = []
    for s in functions:
        if not all(s[s[x]] == x for x in two_set):
            continue  # must be an involution

        def apply_s(x, s=s):
            return None if x is None else s[x]

        if all(f(apply_s(j)) == apply_s(e(j)) for j in two_set):
            reversing.append(s)
    check("the arrow-reversing involution of B(omega_1) is UNIQUE (the swap)",
          len(reversing) == 1 and reversing[0] == {0: 1, 1: 0},
          f"arrow-reversing involutions: {reversing}")

    check("=> #fixed = 0 is EVEN, contradicting 'always odd'",
          fc1 % 2 == 0, f"{fc1} % 2 = {fc1 % 2}")
    check("=> #fixed = 0 < 3, contradicting 'at least 3'",
          fc1 < 3, f"{fc1} < 3")

    # lambda = -w0 lambda in type A1: w0 = s1 acts by -1, so -w0 = id.
    lam = 1
    check("lambda = -w0 lambda holds for lambda = omega_1 in type A1",
          -(-lam) == lam,
          "w0 acts on weights by -1, hence -w0 = id and -w0 lambda = lambda")

    # ------------------------------------------------------------------
    # 3. The family B(k omega_1), k = 1, ..., 10
    # ------------------------------------------------------------------
    print("\n[3] The family B(k omega_1), k = 1, ..., 10")
    print(f"    {'k':>2}  {'|B(kw1)|':>8}  {'weights':<40}  "
          f"{'#fixed':>6}  {'parity':>6}  {'>=3?':>5}")
    table = {}
    for k in range(1, 11):
        els_k, wt_k, f_k, e_k = crystal(k)
        fc = fixed_count(k)
        table[k] = fc
        parity = "even" if fc % 2 == 0 else "odd"
        print(f"    {k:>2}  {len(els_k):>8}  {str([wt_k(j) for j in els_k]):<40}  "
              f"{fc:>6}  {parity:>6}  {str(fc >= 3):>5}")

    # The star is a genuine arrow-reversing involution for every k.
    all_ok_arrow = True
    for k in range(1, 11):
        _, _, f_k, e_k = crystal(k)
        for j in range(k + 1):
            if star(k, star(k, j)) != j:
                all_ok_arrow = False
            if f_k(star(k, j)) != star_opt(k, e_k(j)):
                all_ok_arrow = False
            if e_k(star(k, j)) != star_opt(k, f_k(j)):
                all_ok_arrow = False
    check("for every k = 1..10, j -> k-j is an arrow-reversing involution",
          all_ok_arrow)

    # Parity lemma: #fixed == |B(k omega_1)| = k+1 (mod 2).
    parity_ok = all(table[k] % 2 == (k + 1) % 2 for k in range(1, 11))
    check("#fixed == |B(k omega_1)| (mod 2) for every k = 1..10 "
          "(the parity lemma)",
          parity_ok,
          "; ".join(f"k={k}: {table[k]} vs {k+1}" for k in range(1, 11)))

    # Closed form: 1 for even k, 0 for odd k.
    closed_form = all(
        table[k] == (1 if k % 2 == 0 else 0) for k in range(1, 11)
    )
    check("closed form: #fixed = 1 for even k and 0 for odd k",
          closed_form,
          "fixed points are exactly the weight-0 elements; one exists iff k is even")

    # The two assertions demanded by the problem statement.
    odd_evens = all(table[k] % 2 == 0 for k in range(1, 11) if k % 2 == 1)
    check("for every ODD k = 1..10 the count is EVEN", odd_evens,
          "odd k: " + ", ".join(f"k={k}->{table[k]}" for k in range(1, 11, 2)))
    check("in particular k = 1 gives #fixed = 0", table[1] == 0,
          f"#fixed(B(omega_1)) = {table[1]}")
    check("0 < 3", 0 < 3, "0 is strictly less than 3")

    # "at least 3" fails for every lambda in type A1 (max over all k is 1).
    max_fc = max(table.values())
    check("'at least 3' fails for EVERY lambda in type A1: max over k = 1..10 "
          "is 1 < 3", max_fc < 3, f"max #fixed = {max_fc} < 3")

    # lambda = 2 omega_1 is the odd-cardinality case k=2: 3 elements, 1 fixed
    # point, so the failure is not merely a parity artefact.
    check("lambda = 2 omega_1: |B| = 3 and #fixed = 1 < 3 "
          "(failure is not a parity artefact)",
          len(crystal(2)[0]) == 3 and table[2] == 1,
          f"|B(2w1)| = {len(crystal(2)[0])}, #fixed = {table[2]}")

    # lambda = -w0 lambda holds for every k in type A1.
    all_w0 = all(-(-k) == k for k in range(1, 11))
    check("lambda = -w0 lambda holds for every lambda = k omega_1 (k = 1..10)",
          all_w0, "in type A1, w0 = s1 acts by -1, so -w0 = id")

    # ------------------------------------------------------------------
    # 4. Convention robustness
    # ------------------------------------------------------------------
    print("\n[4] Convention robustness")
    check("ANY involution of the 2-element set has 0 or 2 fixed points "
          "(both even), so no redefinition of * rescues parity",
          counts == [0, 2],
          f"the {len(involutions)} involutions have counts {counts} "
          f"(0 or 2 for each)")
    check("ANY involution of the 2-element set has < 3 fixed points, "
          "so no redefinition of * rescues '>= 3'",
          max(counts) < 3, f"max = {max(counts)} < 3")

    # ------------------------------------------------------------------
    # 5. Assertions (hard failures)
    # ------------------------------------------------------------------
    assert fixed_count(1) == 0, "k=1 must give 0 fixed points"
    assert all(fixed_count(k) % 2 == 0 for k in range(1, 11) if k % 2 == 1), \
        "the count must be even for every odd k"
    assert 0 < 3
    assert max(table.values()) < 3, "the '>= 3' clause fails for all k"
    assert len(reversing) == 1, "the arrow-reversing involution is unique"
    assert all(c % 2 == 0 for c in counts), "every involution count is even"

    # ------------------------------------------------------------------
    # 6. Report
    # ------------------------------------------------------------------
    print("\n[5] Summary")
    print("    lambda = omega_1: B(omega_1) = {weights +1, -1}, one arrow;")
    print("    the only arrow-reversing involution is the swap, #fixed = 0.")
    print("    0 is even (contradicts 'always odd') and 0 < 3 (contradicts")
    print("    'at least 3'), although lambda = -w0 lambda holds in type A1.")
    print("    For B(k omega_1): #fixed = 1 (k even), 0 (k odd), so the maximum")
    print("    over all of type A1 is 1, and 'at least 3' fails for EVERY lambda.")

    print("\n" + line)
    if not CHECK_FAILURES:
        print("PASS: all checks verified; conjecture 00000003837 is FALSE.")
        print("  Counterexample: type A1, lambda = omega_1; the star involution")
        print("  has 0 fixed points (even, and < 3), while lambda = -w0 lambda.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify:")
    for name in CHECK_FAILURES:
        print(f"  - {name}")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
