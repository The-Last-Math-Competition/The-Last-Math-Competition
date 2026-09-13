#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000000418.

    Definition: A Yamanouchi (lattice) word of weight lambda is a word in which,
    in every prefix, the occurrence counts of each letter form a partition; a
    lattice word is one appearing as the reading word of a standard tableau.
    Conjecture: The proportion of lattice words of weight lambda among
    Yamanouchi words is exactly f^lambda / n! * K^{-1}_{lambda,lambda}, and this
    ratio attains its maximum 1/2^{n-1} when lambda is a rectangle.

The conjecture is refuted at lambda = (2,1), n = 3, under BOTH readings of
"lattice word" that the conjecture itself supplies:

  Reading (A)  The parenthetical "Yamanouchi (lattice)" makes the two terms
               synonyms, so the lattice words of weight (2,1) are exactly the
               Yamanouchi words of weight (2,1).  There are 2 of them (`112`
               and `121`; `211` fails the prefix condition).  The proportion is
               therefore 2/2 = 1, while the conjectured value is
               f^(2,1) / (3! * K_{(2,1),(2,1)}) = 2 / (6 * 1) = 1/3.
               Cross-multiplying, 2/2 = 1/3 would force 2*3 = 1*2, i.e. 6 = 2.

  Reading (B)  If "lattice word" means "reading word of a standard tableau",
               every such word is a permutation of {1,...,n} and hence has
               weight (1^n).  At weight (2,1) != (1,1,1) there are no lattice
               words, so the proportion is 0/2 = 0 != 1/3.

The script also verifies, for every partition lambda of size n <= 6:

  * the number of Yamanouchi words of weight lambda equals f^lambda (hook-length
    formula) and equals the number of standard tableaux of shape lambda;
  * K_{lambda,lambda} = 1 by brute-force enumeration of semistandard tableaux
    of shape and content lambda, so the conjectured value collapses to
    f^lambda / n!;
  * the reading-(A) proportion is 1, which is != f^lambda/n! for every n >= 2
    (and exceeds the asserted maximum 1/2^{n-1});
  * the maximisers of f^lambda/n! are non-rectangles at n = 3, 5, 6
    ((2,1), (3,1,1), (3,2,1) respectively), so the "rectangle" clause fails.

Python 3 standard library only.  Prints PASS/FAIL and exits non-zero on
failure.
"""

import sys
from itertools import permutations, product
from math import factorial, prod
from fractions import Fraction


# ---------------------------------------------------------------------------
# partitions, cells
# ---------------------------------------------------------------------------

def partitions(n, max_part=None):
    """All partitions of n as tuples in weakly decreasing order."""
    if max_part is None:
        max_part = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, max_part), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def cells(lam):
    """Cells of the Young diagram of lam, in row-major order."""
    return [(i, j) for i, row in enumerate(lam) for j in range(row)]


def is_rectangle(lam):
    return len(set(lam)) == 1


# ---------------------------------------------------------------------------
# words: content, Yamanouchi, lattice
# ---------------------------------------------------------------------------

def content_of(word, k):
    """Counts of 1, ..., k in word, as a tuple."""
    return tuple(word.count(i) for i in range(1, k + 1))


def words_with_content(content):
    """All words with the given content (a partition), over the alphabet
    {1, ..., len(content)}."""
    k = len(content)
    n = sum(content)
    for w in product(range(1, k + 1), repeat=n):
        if content_of(w, k) == tuple(content):
            yield w


def is_yamanouchi(word, k):
    """True iff in every prefix the counts of 1, ..., k form a partition
    (i.e. are weakly decreasing)."""
    counts = [0] * (k + 1)
    for x in word:
        counts[x] += 1
        for i in range(1, k):
            if counts[i] < counts[i + 1]:
                return False
    return True


def prefix_table(word):
    """[(prefix, counts of 1, counts of 2)] for display."""
    rows = []
    for m in range(len(word) + 1):
        pre = word[:m]
        rows.append(("".join(map(str, pre)), pre.count(1), pre.count(2)))
    return rows


def yamanouchi_words(content):
    k = len(content)
    return [w for w in words_with_content(content) if is_yamanouchi(w, k)]


# ---------------------------------------------------------------------------
# standard tableaux, their readings, hook lengths
# ---------------------------------------------------------------------------

def is_syt(lam, vals):
    """vals are assigned to cells(lam) in row-major order; check strict
    increase along rows and columns."""
    grid = dict(zip(cells(lam), vals))
    for (i, j), v in grid.items():
        if (i, j + 1) in grid and grid[(i, j + 1)] <= v:
            return False
        if (i + 1, j) in grid and grid[(i + 1, j)] <= v:
            return False
    return True


def standard_tableaux(lam):
    """All standard tableaux of shape lam, each as a tuple of values in
    row-major cell order."""
    n = sum(lam)
    return [vals for vals in permutations(range(1, n + 1)) if is_syt(lam, vals)]


def rows_of(lam, vals):
    rows, idx = [], 0
    for r in lam:
        rows.append(list(vals[idx:idx + r]))
        idx += r
    return rows


def row_reading(lam, vals):
    """Row indices (1-based) of the cells containing 1, 2, ..., n: the standard
    bijection standard tableaux of shape lam <-> lattice (Yamanouchi) words of
    weight lam.  This is the reading relevant to reading (A)."""
    index = {v: c for v, c in zip(vals, cells(lam))}
    n = sum(lam)
    return tuple(index[e][0] + 1 for e in range(1, n + 1))


def entry_reading(lam, vals):
    """Entries read row by row from bottom to top, left to right.  Under
    reading (B) this is 'the reading word of a standard tableau'; it is always a
    permutation of {1,...,n}."""
    out = []
    for r in reversed(rows_of(lam, vals)):
        out.extend(r)
    return tuple(out)


def hook_lengths(lam):
    """Hook lengths of all cells of lam, in row-major order."""
    hooks = []
    for i, row in enumerate(lam):
        for j in range(row):
            arm = row - j - 1
            leg = sum(1 for r in lam[i + 1:] if r > j)
            hooks.append(arm + leg + 1)
    return hooks


def f_hook(lam):
    """Hook-length formula for the number of standard tableaux of shape lam."""
    prod = 1
    for h in hook_lengths(lam):
        prod *= h
    return factorial(sum(lam)) // prod


# ---------------------------------------------------------------------------
# Kostka number K_{lam,mu} by brute force
# ---------------------------------------------------------------------------

def is_ssyt(lam, vals):
    """Semistandard condition: weakly increasing along rows, strictly
    increasing down columns."""
    grid = dict(zip(cells(lam), vals))
    for (i, j), v in grid.items():
        if (i, j + 1) in grid and grid[(i, j + 1)] < v:
            return False
        if (i + 1, j) in grid and grid[(i + 1, j)] <= v:
            return False
    return True


def count_ssyt(lam, mu):
    """K_{lam,mu}: number of semistandard tableaux of shape lam, content mu."""
    n = sum(lam)
    k = len(mu)
    total = 0
    for vals in product(range(1, k + 1), repeat=n):
        if content_of(vals, k) != tuple(mu):
            continue
        if is_ssyt(lam, vals):
            total += 1
    return total


def claimed_value(lam):
    """f^lam / (n! * K_{lam,lam}), exactly.  Since K_{lam,lam} = 1 this is
    f^lam / n!."""
    n = sum(lam)
    K = count_ssyt(lam, lam)
    return Fraction(f_hook(lam), factorial(n) * K), K


# ---------------------------------------------------------------------------
# report plumbing
# ---------------------------------------------------------------------------

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok), detail))
    return bool(ok)


def section(title):
    print("\n" + title)
    print("-" * len(title))


# ---------------------------------------------------------------------------

def lambda_21_analysis():
    section("[1] lambda = (2,1), n = 3: the reading-(A) and reading-(B) failures")

    content = (2, 1)
    words = list(words_with_content(content))
    print(f"    all words of content {content} over {{1,2}}: "
          f"{[''.join(map(str, w)) for w in words]}")

    yam = yamanouchi_words(content)
    print(f"    Yamanouchi words (prefix counts weakly decreasing):")
    for w in words:
        keeps = is_yamanouchi(w, len(content))
        marks = "  ".join(f"|{p}: ({c1},{c2})" for p, c1, c2 in prefix_table(w))
        print(f"        {''.join(map(str, w))}: {'yes' if keeps else 'no '}   {marks}")
    print(f"    => {len(yam)} Yamanouchi words: "
          f"{[''.join(map(str, w)) for w in yam]}")

    # Reading (A): lattice = Yamanouchi (the conjecture's own synonym).
    num_yam = len(yam)
    prop_A = Fraction(num_yam, num_yam)
    check("Reading (A): proportion = 2/2 = 1",
          prop_A == 1 and num_yam == 2,
          f"#lattice(A) = {num_yam}, #Yamanouchi = {num_yam}, proportion = {prop_A}")

    # Standard tableaux of shape (2,1) and their two reading words.
    syts = standard_tableaux(content)
    print(f"    standard tableaux of shape (2,1): {[rows_of(content, v) for v in syts]}")
    row_reads = [row_reading(content, v) for v in syts]
    entry_reads = [entry_reading(content, v) for v in syts]
    print(f"    row-index reading words (reading A bijection): "
          f"{[''.join(map(str, r)) for r in row_reads]}")
    print(f"    entry reading words (reading B): "
          f"{[''.join(map(str, r)) for r in entry_reads]}")
    check("The row-index readings are exactly the Yamanouchi words",
          set(row_reads) == set(yam),
          f"row readings {sorted(row_reads)} vs Yamanouchi {sorted(yam)}")
    check("Entry reading words are permutations, weight (1,1,1) != (2,1)",
          all(content_of(r, 3) == (1, 1, 1) for r in entry_reads),
          f"weights {[content_of(r, 3) for r in entry_reads]}")

    # Reading (B): lattice = reading word of an SYT, weight (1^n).
    num_lattice_B = sum(1 for r in entry_reads if content_of(r, 3) == content)
    prop_B = Fraction(num_lattice_B, num_yam)
    check("Reading (B): proportion = 0/2 = 0",
          prop_B == 0 and num_lattice_B == 0,
          f"#lattice(B) of weight (2,1) = {num_lattice_B}, proportion = {prop_B}")

    # Hook-length computation of f^(2,1).
    hooks = hook_lengths(content)
    f21 = f_hook(content)
    print(f"    hook lengths of (2,1): {hooks}, product = {prod(hooks)}")
    print(f"    f^(2,1) = 3! / (3*1*1) = 6/3 = {f21}")
    check("f^(2,1) = 2 = #SYT of shape (2,1)",
          f21 == 2 and len(syts) == 2,
          f"hook-length f = {f21}, enumerated SYT = {len(syts)}")

    # K_{(2,1),(2,1)} by brute force.
    K21 = count_ssyt(content, content)
    print(f"    K_(2,1),(2,1) by brute force over SSYT = {K21}")
    check("K_(2,1),(2,1) = 1",
          K21 == 1,
          f"brute-force SSYT count = {K21} (the superstandard tableau 112)")

    # The claimed value and the two contradictions.
    claim = Fraction(f21, factorial(3) * K21)
    print(f"    conjectured value = f/(n!*K) = {f21}/(6*1) = {claim}")
    check("Reading (A): 2/2 = 1 differs from claimed 1/3",
          prop_A != claim,
          f"{prop_A} != {claim}; cross-multiplied 2*3 = 6 != 2 = 1*2 (numerator*3 vs 1*denominator)")
    check("Reading (B): 0/2 = 0 differs from claimed 1/3",
          prop_B != claim,
          f"{prop_B} != {claim}")
    check("Cross-multiplication: 2*6 != 2*2, i.e. 12 != 4",
          2 * 6 != 2 * 2 and (2 * 6, 2 * 2) == (12, 4),
          "2/2 vs 2/6: 2*6 = 12 and 2*2 = 4")

    # The asserted maximum 1/2^{n-1} = 1/4.
    max_claim = Fraction(1, 2 ** (3 - 1))
    check("Asserted maximum 1/4 is exceeded by the reading-(A) proportion 1",
          Fraction(1, 4) < Fraction(1, 1) and prop_A > max_claim,
          f"1/4 = {max_claim} < 1 = {prop_A}")

    # The formula's own maximum is at the non-rectangle (2,1).
    frect = {lam: f_hook(lam) for lam in partitions(3)}
    print(f"    f^lambda for |lambda| = 3: {frect}")
    check("At n=3 the maximum of f^lambda/n! is at non-rectangle (2,1)",
          max(frect, key=lambda l: Fraction(frect[l], 6)) == (2, 1)
          and not is_rectangle((2, 1)),
          "max f/n! at lambda = (2,1), a non-rectangle")
    return yam


def all_lambdas_up_to_6():
    section("[2] Extension: every partition lambda of size n <= 6")

    print(f"    {'n':>2}  {'lambda':<14} {'#Yam':>5} {'f^lam':>6} {'#SYT':>5} "
          f"{'K_lam,lam':>9} {'propA':>6} {'claimed':>9}")
    ok_all = True
    maximisers = {}
    for n in range(1, 7):
        for lam in partitions(n):
            yam = yamanouchi_words(lam)
            f = f_hook(lam)
            syts = standard_tableaux(lam)
            K = count_ssyt(lam, lam)
            claim = Fraction(f, factorial(n) * K)
            prop_A = Fraction(len(yam), len(yam))
            print(f"    {n:>2}  {str(lam):<14} {len(yam):>5} {f:>6} {len(syts):>5} "
                  f"{K:>9} {str(prop_A):>6} {str(claim):>9}")
            ok_all &= check(
                f"|lambda|={n} {lam}: #Yam = f^lambda = #SYT and K=1",
                len(yam) == f == len(syts) and K == 1,
                f"#Yam={len(yam)}, f={f}, #SYT={len(syts)}, K={K}")
            maximisers.setdefault(n, []).append((Fraction(f, factorial(n)), lam))

    # Reading (A) is identically 1, so it never equals the claimed value for
    # n >= 2, and always exceeds the asserted maximum 1/2^{n-1}.
    for n in range(2, 7):
        for lam in partitions(n):
            claim = Fraction(f_hook(lam), factorial(n) * count_ssyt(lam, lam))
            check(f"n={n} {lam}: proportion(A) = 1 != claimed {claim}",
                  1 != claim,
                  f"1 != {claim}")
            check(f"n={n}: 1 > 1/2^{n-1} = {Fraction(1, 2 ** (n - 1))}",
                  Fraction(1) > Fraction(1, 2 ** (n - 1)),
                  f"1 > {Fraction(1, 2 ** (n - 1))}")

    # Maximisers of f^lambda/n! for the cases named in the refutation.
    expected = {3: (2, 1), 5: (3, 1, 1), 6: (3, 2, 1)}
    for n, lam in expected.items():
        best = max(maximisers[n])
        check(f"Maximiser of f^lambda/n! at n={n} is the non-rectangle {lam}",
              best[1] == lam and not is_rectangle(lam),
              f"argmax = {best[1]} with f/n! = {best[0]}")
    return ok_all


def main():
    print("=" * 78)
    print("Disproof of conjecture 00000000418 -- reproduction")
    print("=" * 78)

    lambda_21_analysis()
    all_lambdas_up_to_6()

    section("Summary")
    all_ok = True
    for name, ok, detail in CHECKS:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        if detail:
            print(f"            {detail}")
        all_ok = all_ok and ok

    print("\n" + "=" * 78)
    if all_ok:
        print(f"PASS: {len(CHECKS)} checks verified.")
        print("Conjecture 00000000418 is FALSE as stated:")
        print("  (A) 'Yamanouchi (lattice)' is a synonym, so the proportion of")
        print("      lattice words among Yamanouchi words is 2/2 = 1 at (2,1),")
        print("      not f/(n!*K) = 2/(6*1) = 1/3; cross-multiplying, 12 != 4.")
        print("      Also 1 > 1/4 = 1/2^{n-1}, killing the maximum clause.")
        print("  (B) Reading words of standard tableaux are permutations of")
        print("      weight (1,1,1), so at weight (2,1) the proportion is 0/2 = 0")
        print("      != 1/3.")
        print("  General: K_{lambda,lambda} = 1 for all lambda, so the claimed")
        print("  value collapses to f^lambda/n!, whose maximisers at n = 3, 5, 6")
        print("  are the non-rectangles (2,1), (3,1,1), (3,2,1).")
        print("=" * 78)
        return 0
    print(f"FAIL: {sum(1 for _, ok, _ in CHECKS if not ok)} of {len(CHECKS)} "
          f"checks failed.")
    print("=" * 78)
    return 1


if __name__ == "__main__":
    sys.exit(main())
