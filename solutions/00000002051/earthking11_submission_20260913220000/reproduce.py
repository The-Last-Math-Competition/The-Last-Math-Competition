#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000002051.

    Definition (conjectures/00000002051.md): the fine spectrum f_V(n) of a
    variety V is the cardinality of its n-generated free algebra.
    Conjecture: the fine spectrum of the semigroup variety <x^2 = x> is the
    explicit closed form f(n) = 2^n * C_n (C_n the Catalan numbers).

The variety <x^2 = x> is the variety of BANDS (idempotent semigroups), so
f(n) is the number of elements of the free band on n generators.  The
conjecture is FALSE, already at n = 1:

  * n = 1:  the free band on one generator is {x}, a singleton, so f(1) = 1,
            while the formula gives 2^1 * C_1 = 2 * 1 = 2.

  * n = 2:  the free band on two generators has the six elements
            {a, b, ab, ba, aba, bab} (its multiplication table below is closed,
            associative and idempotent), so f(2) = 6, while the formula gives
            2^2 * C_2 = 4 * 2 = 8.  This is independent of the n = 1 witness.

The true free-band counts (OEIS A030449; Howie, Fundamentals of Semigroup
Theory, Oxford 1995, p. 123) are 1, 6, 159, 332380, ... , which differ from
2^n * C_n = 2, 8, 40, 224, ... for every n >= 1.

Standard library only.  Python 3.8+.  Exits non-zero if any check fails.
"""

from itertools import product

# ---------------------------------------------------------------------------
# Word reduction in the free band
# ---------------------------------------------------------------------------

def reduce_word(w):
    """Reduce a word by the free-band identity u*u -> u (repeat to a fixpoint).

    The rule u*u -> u is sound in every band: u, being an element of a band, is
    idempotent.  For alphabets of size <= 2 this reduction is complete (the
    irreducible words are the square-free words, and over a 2-letter alphabet
    no square-free word has length >= 4), so the fixpoint is a canonical form.
    """
    changed = True
    while changed:
        changed = False
        n = len(w)
        # Collapse the longest square factor first; repeat until none remains.
        for L in range(n // 2, 0, -1):
            for i in range(0, n - 2 * L + 1):
                if w[i:i + L] == w[i + L:i + 2 * L]:
                    w = w[:i] + w[i:i + L] + w[i + 2 * L:]
                    changed = True
                    break
            if changed:
                break
    return w


def reduced_classes(gens, maxlen):
    """All reduced forms of words over `gens` of length <= maxlen."""
    classes = {}
    for L in range(1, maxlen + 1):
        for tup in product(gens, repeat=L):
            w = ''.join(tup)
            classes.setdefault(reduce_word(w), []).append(w)
    return classes


def has_square_factor(w):
    """True iff w contains a factor ss for some non-empty s."""
    n = len(w)
    for L in range(1, n // 2 + 1):
        for i in range(0, n - 2 * L + 1):
            if w[i:i + L] == w[i + L:i + 2 * L]:
                return True
    return False


# ---------------------------------------------------------------------------
# Catalan numbers
# ---------------------------------------------------------------------------

def catalan(n):
    """Catalan numbers by the standard recursion C_0 = 1,
    C_{n+1} = C_n * 2(2n+1)/(n+2)."""
    c = 1
    for k in range(n):
        c = c * (2 * (2 * k + 1)) // (k + 2)
    return c


def formula(n):
    """The conjecture's closed form f(n) = 2^n * C_n."""
    return (2 ** n) * catalan(n)


# ---------------------------------------------------------------------------
# The expected six-element band (free band on {a, b})
# ---------------------------------------------------------------------------

CANON = ['a', 'b', 'ab', 'ba', 'aba', 'bab']

# Entry (u, v) is the reduced form of u ++ v.  Verified below against the
# reduction, not merely asserted.
EXPECTED_TABLE = {
    ('a', 'a'): 'a',   ('a', 'b'): 'ab',  ('a', 'ab'): 'ab',
    ('a', 'ba'): 'aba', ('a', 'aba'): 'aba', ('a', 'bab'): 'ab',
    ('b', 'a'): 'ba',  ('b', 'b'): 'b',   ('b', 'ab'): 'bab',
    ('b', 'ba'): 'ba', ('b', 'aba'): 'ba', ('b', 'bab'): 'bab',
    ('ab', 'a'): 'aba', ('ab', 'b'): 'ab', ('ab', 'ab'): 'ab',
    ('ab', 'ba'): 'aba', ('ab', 'aba'): 'aba', ('ab', 'bab'): 'ab',
    ('ba', 'a'): 'ba', ('ba', 'b'): 'bab', ('ba', 'ab'): 'bab',
    ('ba', 'ba'): 'ba', ('ba', 'aba'): 'ba', ('ba', 'bab'): 'bab',
    ('aba', 'a'): 'aba', ('aba', 'b'): 'ab', ('aba', 'ab'): 'ab',
    ('aba', 'ba'): 'aba', ('aba', 'aba'): 'aba', ('aba', 'bab'): 'ab',
    ('bab', 'a'): 'ba', ('bab', 'b'): 'bab', ('bab', 'ab'): 'bab',
    ('bab', 'ba'): 'ba', ('bab', 'aba'): 'ba', ('bab', 'bab'): 'bab',
}

# Free band counts from OEIS A030449 / Howie (1995), p. 123.
FREE_BAND = {1: 1, 2: 6, 3: 159, 4: 332380}


def mul(u, v):
    m = reduce_word(u + v)
    assert m in CANON, (u, v, m)
    return m


def main():
    checks = []

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))

    # ------------------------------------------------------------------
    # 1. n = 1: the free band on one generator is a singleton
    # ------------------------------------------------------------------
    classes1 = reduced_classes(['x'], 9)
    check("n=1: every word over {x} reduces to x",
          set(classes1) == {'x'},
          f"reduced classes = {sorted(classes1)}")
    check("n=1: f(1) = 1, but 2^1 * C_1 = 2",
          len(classes1) == 1 and 1 != formula(1),
          f"f(1) = {len(classes1)}; 2^1*C_1 = {formula(1)}")

    # ------------------------------------------------------------------
    # 2. n = 2: exactly six classes {a,b,ab,ba,aba,bab}
    # ------------------------------------------------------------------
    classes2 = reduced_classes(['a', 'b'], 9)
    check("n=2: exactly six reduced classes",
          set(classes2) == set(CANON) and len(classes2) == 6,
          f"reduced classes = {sorted(classes2)}")

    # every word of length >= 4 over 2 letters has a square factor (so the six
    # square-free words of length <= 3 are all of them)
    square_free_bad = []
    for L in range(4, 13):
        for tup in product('ab', repeat=L):
            w = ''.join(tup)
            if not has_square_factor(w):
                square_free_bad.append(w)
    check("n=2: every word of length 4..12 over {a,b} has a square factor",
          not square_free_bad,
          "no square-free word of length >= 4 found"
          if not square_free_bad else f"counterexamples: {square_free_bad[:5]}")
    check("n=2: the six canonical words are fixpoints of the reduction",
          all(reduce_word(w) == w for w in CANON),
          "the six reduced words are stable")

    # ------------------------------------------------------------------
    # 3. The six-element multiplication table
    # ------------------------------------------------------------------
    table = {p: mul(*p) for p in product(CANON, repeat=2)}
    check("n=2: multiplication table matches the expected free-band table",
          table == EXPECTED_TABLE,
          "table verified entry by entry"
          if table == EXPECTED_TABLE else
          f"mismatches: {[k for k in table if table[k] != EXPECTED_TABLE[k]]}")
    check("n=2: table is closed (every product is one of the six words)",
          all(v in CANON for v in table.values()),
          f"entries = {sorted(set(table.values()))}")
    check("n=2: table is associative (216 triples)",
          all(mul(mul(x, y), z) == mul(x, mul(y, z))
              for x in CANON for y in CANON for z in CANON),
          "all 216 triples agree")
    check("n=2: table is idempotent (all six diagonal entries)",
          all(mul(x, x) == x for x in CANON),
          f"diagonal = {[mul(x, x) for x in CANON]}")
    check("n=2: table is generated by {a, b}",
          set(_closure(['a', 'b'])) == set(CANON),
          f"closure(a,b) = {sorted(_closure(['a', 'b']))}")
    check("n=2: f(2) = 6, but 2^2 * C_2 = 8",
          len(CANON) == 6 and 6 != formula(2),
          f"f(2) = {len(CANON)}; 2^2*C_2 = {formula(2)}")

    # ------------------------------------------------------------------
    # 4. Literature values vs the formula
    # ------------------------------------------------------------------
    formula_vals = {n: formula(n) for n in range(1, 5)}
    check("formula matches the Catalan closed form 2, 8, 40, 224",
          formula_vals == {1: 2, 2: 8, 3: 40, 4: 224},
          f"2^n*C_n = {[formula_vals[n] for n in range(1, 5)]}")
    check("free band counts 1, 6, 159, 332380 differ from the formula for "
          "n = 1,2,3,4",
          all(FREE_BAND[n] != formula_vals[n] for n in range(1, 5)),
          "; ".join(f"n={n}: f={FREE_BAND[n]} vs {formula_vals[n]}"
                    for n in range(1, 5)))

    # ------------------------------------------------------------------
    # 5. Alternative readings also fail
    # ------------------------------------------------------------------
    check("reading (b): even irreducible-word counts 1 and 6 differ from "
          "the formula",
          len(classes1) != formula(1) and len(classes2) != formula(2),
          f"irreducible counts = {len(classes1)}, {len(classes2)}; "
          f"formula = {formula(1)}, {formula(2)}")
    adjoined1 = len(classes1) + 1
    adjoined2 = len(classes2) + 1
    check("reading (d): with an adjoined identity n=1 matches but n=2 fails",
          adjoined1 == formula(1) and adjoined2 != formula(2),
          f"adjoined-identity counts = {adjoined1}, {adjoined2}; "
          f"formula = {formula(1)}, {formula(2)}")
    check("reading (e): n=0 formula is 1; the free semigroup on no generators "
          "is empty (0 elements)",
          formula(0) == 1,
          "f(0) = 0 for the free semigroup on the empty set, vs 2^0*C_0 = 1")

    # ------------------------------------------------------------------
    # 6. Report
    # ------------------------------------------------------------------
    line = "=" * 72
    print(line)
    print("Disproof of conjecture 00000002051 -- reproduction")
    print(line)
    print("  fine spectrum of <x^2 = x> (the variety of bands) is claimed to be")
    print("  f(n) = 2^n * C_n; this script shows f(1) = 1 != 2 and f(2) = 6 != 8.")

    print("\n[1] n = 1: words over {x} reduced by u*u -> u")
    print(f"    reduced classes: {sorted(classes1)}")
    print(f"    f(1) = {len(classes1)}  vs  2^1*C_1 = {formula(1)}   -> FAILURE")

    print("\n[2] n = 2: words over {{a,b}} reduced by u*u -> u")
    print(f"    reduced classes: {sorted(classes2)}")
    print(f"    f(2) = {len(classes2)}  vs  2^2*C_2 = {formula(2)}   -> FAILURE")

    print("\n[3] multiplication table of the six-element free band")
    width = 5
    print("      " + "".join(f"{c:>{width}}" for c in CANON))
    for u in CANON:
        print(f"{u:>5} " + "".join(f"{mul(u, v):>{width}}" for v in CANON))

    print("\n[4] free band counts (A030449) vs the formula")
    print(f"    {'n':>3}  {'free band':>10}  {'2^n*C_n':>8}  equal?")
    for n in range(1, 5):
        print(f"    {n:>3}  {FREE_BAND[n]:>10}  {formula_vals[n]:>8}  "
              f"{'yes' if FREE_BAND[n] == formula_vals[n] else 'no'}")

    print("\n[5] checks")
    all_ok = True
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        all_ok = all_ok and ok
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok:
        print("PASS: all checks verified; conjecture 00000002051 is FALSE.")
        print("  f(1) = 1 != 2 = 2^1*C_1  (the free band on one generator is {x});")
        print("  f(2) = 6 != 8 = 2^2*C_2  (six-element free band, table above).")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


def _closure(gens):
    """The subsemigroup generated by `gens` under the free-band product."""
    seen = set(gens)
    frontier = list(gens)
    while frontier:
        u = frontier.pop()
        for v in list(seen) + list(gens):
            w = reduce_word(u + v)
            if w not in seen:
                seen.add(w)
                frontier.append(w)
    return seen


if __name__ == "__main__":
    raise SystemExit(main())
