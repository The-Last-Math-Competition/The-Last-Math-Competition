#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001260.

    Definition: the factor complexity p(n) of a primitive substitution counts
        the distinct factors of length n.
    Conjecture: the optimal upper bound is p(n) <= n + 2 within the purely
        substitutive class, attained by three-letter substitution families
        beyond the Tribonacci word; p(n) = n + 1 occurs only for Sturmian
        words.

The conjecture is FALSE, read literally as a universal upper bound over the
purely substitutive class (no alphabet restriction, constant-length
substitutions not excluded).

  * Thue-Morse word: fixed point of the primitive substitution
        0 -> 01, 1 -> 10        (incidence matrix [[1,1],[1,1]], positive).
    Its factor complexity satisfies p(3) = 6 > 5 = 3 + 2, so the asserted
    universal bound fails at n = 3.  This script builds a prefix of length
    2^18 by the substitution and verifies p(n) > n + 2 for every n in [3,300].

  * Tribonacci word: the very word named in the conjecture, fixed point of
        0 -> 01, 1 -> 02, 2 -> 0.
    It satisfies p(n) = 2n + 1 exactly, hence p(n) > n + 2 for every n >= 2,
    so it too refutes the bound.

  * Period-doubling word: fixed point of
        0 -> 01, 1 -> 00.
    It first violates the bound at n = 5, where p(5) = 8 > 7.

  * Fibonacci word (Sturmian), fixed point of 0 -> 01, 1 -> 0, has
    p(n) = n + 1, confirming the second clause of the conjecture -- which only
    makes the first (universal bound) clause fail more starkly.

Standard library only.  Python 3.8+.  Prints PASS/FAIL and exits non-zero if
any check fails.
"""

# ----------------------------------------------------------------------------
# Substitutions (words are strings over '0','1','2')
# ----------------------------------------------------------------------------


def subst(mapping):
    """Return the morphism induced by `mapping` (a dict char -> string)."""
    def apply(w):
        return "".join(mapping[c] for c in w)
    return apply


THUE_MORSE = subst({"0": "01", "1": "10"})
PERIOD_DOUBLING = subst({"0": "01", "1": "00"})
TRIBONACCI = subst({"0": "01", "1": "02", "2": "0"})
FIBONACCI = subst({"0": "01", "1": "0"})


def build(morphism, target_len):
    """Iterate `morphism` from '0' until the word has length >= target_len."""
    w = "0"
    while len(w) < target_len:
        w = morphism(w)
    return w


# ----------------------------------------------------------------------------
# Factor complexity
# ----------------------------------------------------------------------------


def complexities(word, nmax):
    """[p(1), ..., p(nmax)] where p(n) is the number of distinct length-n
    factors of `word` (counted over this finite word)."""
    L = len(word)
    out = []
    for n in range(1, nmax + 1):
        out.append(len({word[i:i + n] for i in range(L - n + 1)}))
    return out


def converged_complexities(morphism, nmax, min_len):
    """Complexities over a prefix long enough that extending it by one more
    substitution step adds no new factor of length <= nmax.

    Returns (counts, len_prefix, len_extended)."""
    w = build(morphism, min_len)
    while True:
        w2 = morphism(w)
        c1 = complexities(w, nmax)
        c2 = complexities(w2, nmax)
        if c1 == c2:
            return c1, len(w), len(w2)
        w = w2


def main():
    checks = []          # (name, ok, detail)
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    # ------------------------------------------------------------------
    # 1. Thue-Morse: the primary counterexample
    # ------------------------------------------------------------------
    TARGET = 2 ** 18                      # >= 2^18, built by the substitution
    tm_word = build(THUE_MORSE, TARGET)
    assert len(tm_word) == TARGET

    NMAX = 300
    tm_p = complexities(tm_word, NMAX)

    expected_first_15 = [2, 4, 6, 10, 12, 16, 20, 22, 24, 28, 32, 36, 40, 42, 44]

    check("Thue-Morse: prefix built by the substitution has length >= 2^18",
          len(tm_word) >= 2 ** 18,
          f"|w| = {len(tm_word)} = 2^18")

    check("Thue-Morse: p(3) = 6",
          tm_p[2] == 6,
          f"p(3) = {tm_p[2]}")

    check("Thue-Morse: p(3) = 6 > 5 = 3 + 2  (the bound fails at n = 3)",
          tm_p[2] > 3 + 2,
          f"p(3) = {tm_p[2]} > {3 + 2}")

    check("Thue-Morse: p(n) matches the tabulated values for n = 1..15",
          tm_p[:15] == expected_first_15,
          f"p(1..15) = {tm_p[:15]}")

    bad = [n for n in range(3, NMAX + 1) if not tm_p[n - 1] > n + 2]
    check(f"Thue-Morse: p(n) > n + 2 for all n in [3, {NMAX}]",
          not bad,
          f"first violations: {bad[:10]}" if bad else
          f"all {NMAX - 2} values in [3, {NMAX}] satisfy p(n) > n + 2")

    # p is nondecreasing and p(1) = 2, p(2) = 4 for a binary aperiodic word
    check("Thue-Morse: p(1) = 2, p(2) = 4",
          tm_p[0] == 2 and tm_p[1] == 4,
          f"p(1) = {tm_p[0]}, p(2) = {tm_p[1]}")

    # ------------------------------------------------------------------
    # 2. Tribonacci: the word named by the conjecture also refutes it
    # ------------------------------------------------------------------
    TRI_MAX = 60
    tri_p, tri_len, tri_len2 = converged_complexities(TRIBONACCI, TRI_MAX, 150000)

    check("Tribonacci: complexity is stable under a further substitution step",
          True,
          f"prefixes of length {tri_len} and {tri_len2} give identical p(n), "
          f"n <= {TRI_MAX}")

    check("Tribonacci: p(n) = 2n + 1 exactly for all n in [1, %d]" % TRI_MAX,
          all(tri_p[n - 1] == 2 * n + 1 for n in range(1, TRI_MAX + 1)),
          f"p(1..10) = {tri_p[:10]}")

    tri_bad = [n for n in range(2, TRI_MAX + 1) if not tri_p[n - 1] > n + 2]
    check("Tribonacci: p(n) > n + 2 for all n in [2, %d]" % TRI_MAX,
          not tri_bad,
          f"p(2) = {tri_p[1]} > 4, ... ; first violations: {tri_bad[:10]}"
          if tri_bad else
          f"all values in [2, {TRI_MAX}] satisfy p(n) = 2n+1 > n + 2")

    # ------------------------------------------------------------------
    # 3. Period-doubling: violates the bound first at n = 5
    # ------------------------------------------------------------------
    PD_MAX = 40
    pd_p, pd_len, pd_len2 = converged_complexities(PERIOD_DOUBLING, PD_MAX, 2 ** 16)

    check("period-doubling: complexity is stable under a further step",
          True,
          f"prefixes of length {pd_len} and {pd_len2} give identical p(n), "
          f"n <= {PD_MAX}")

    first_pd = next((n for n in range(1, PD_MAX + 1) if pd_p[n - 1] > n + 2), None)
    check("period-doubling: first violation of p(n) <= n + 2 is at n = 5",
          first_pd == 5,
          f"first violation at n = {first_pd}; p(1..14) = {pd_p[:14]}")

    check("period-doubling: p(5) = 8 > 7 = 5 + 2",
          pd_p[4] == 8,
          f"p(5) = {pd_p[4]}")

    # ------------------------------------------------------------------
    # 4. Fibonacci (Sturmian): p(n) = n + 1, confirming the second clause
    # ------------------------------------------------------------------
    FIB_MAX = 40
    fib_p, fib_len, fib_len2 = converged_complexities(FIBONACCI, FIB_MAX, 100000)

    check("Fibonacci: p(n) = n + 1 exactly for all n in [1, %d]" % FIB_MAX,
          all(fib_p[n - 1] == n + 1 for n in range(1, FIB_MAX + 1)),
          f"p(1..10) = {fib_p[:10]}")

    # ------------------------------------------------------------------
    # Report
    # ------------------------------------------------------------------
    line = "=" * 74
    print(line)
    print("Disproof of conjecture 00000001260 -- reproduction")
    print(line)

    print("\n[1] Thue-Morse word  0 -> 01, 1 -> 10   (built by substitution)")
    print(f"    prefix length |w| = {len(tm_word)} = 2^18")
    print(f"    p(n) for n = 1..15:  {tm_p[:15]}")
    print(f"    n + 2 for n = 1..15: {[n + 2 for n in range(1, 16)]}")
    print("    => p(3) = 6 > 5 = 3 + 2: the universal bound fails at n = 3.")

    print("\n[2] Tribonacci word  0 -> 01, 1 -> 02, 2 -> 0   (named by the conjecture)")
    print(f"    prefix length ~ {tri_len}")
    print(f"    p(n) for n = 1..15:  {tri_p[:15]}")
    print(f"    2n + 1 for n = 1..15: {[2 * n + 1 for n in range(1, 16)]}")
    print("    => p(n) = 2n + 1 > n + 2 for every n >= 2: also refutes the bound.")

    print("\n[3] Period-doubling word  0 -> 01, 1 -> 00")
    print(f"    prefix length ~ {pd_len}")
    print(f"    p(n) for n = 1..14:  {pd_p[:14]}")
    print(f"    n + 2 for n = 1..14: {[n + 2 for n in range(1, 15)]}")
    print("    => first violation at n = 5, where p(5) = 8 > 7.")

    print("\n[4] Fibonacci (Sturmian) word  0 -> 01, 1 -> 0")
    print(f"    p(n) for n = 1..14:  {fib_p[:14]}")
    print(f"    n + 1 for n = 1..14: {[n + 1 for n in range(1, 15)]}")
    print("    => p(n) = n + 1, confirming the conjecture's second clause.")

    print("\n[5] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: conjecture 00000001260 is FALSE.")
        print("  Thue-Morse (0->01, 1->10, primitive): p(3) = 6 > 5 = 3 + 2,")
        print("  and p(n) > n + 2 for every n in [3,300].")
        print("  Tribonacci: p(n) = 2n+1 > n+2 for n >= 2.")
        print("  Period-doubling: first violation at n = 5 (8 > 7).")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
