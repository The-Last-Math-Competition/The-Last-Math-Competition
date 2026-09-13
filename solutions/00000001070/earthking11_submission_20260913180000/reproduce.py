#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001070.

    Definition: the three-fold sumset A + A + A (repetitions allowed).
    Conjecture: the smallest |A| with 3A = F_p is ceil((p+1)/3) + 1.

The conjecture is FALSE.  Two distinct readings of "smallest |A| with
3A = F_p" are compared, and the conjecture is wrong in both.

  (E) Existential reading, which is what the conjecture literally states:
      the least k such that SOME k-element A satisfies 3A = F_p.
      This script computes it EXHAUSTIVELY for every prime p <= 30 (the
      counting bound |3A| <= C(k+2,3) prunes small k, so only k <= 6 is ever
      tested).  The true values are far below the conjectured ones: e.g. at
      p = 7, A = {0,1,3} of size 3 already covers F_7, while the conjecture
      demands 4.

  (U) Universal reading: the least k such that EVERY k-element A satisfies
      3A = F_p.  By Cauchy-Davenport this is exactly ceil((p+2)/3): if
      3|A| - 2 >= p then |3A| >= p, and the interval {0,...,k-1} with
      3k - 2 < p does not cover.  The conjectured ceil((p+1)/3) + 1 is too
      large here at p = 3 and at the primes p = 1 (mod 3), i.e.
      p = 3, 7, 13, 19 (<= 30).

The decisive counterexample for the conjecture as filed is p = 7,
A = {0,1,3}: |A| = 3, 3A = F_7, but the formula gives 4.

Python 3.8+, standard library only.  Runs in seconds.
"""

from itertools import combinations
from math import comb
import sys


# ---------------------------------------------------------------------------
# basics
# ---------------------------------------------------------------------------

def primes_upto(n):
    """All primes <= n by trial division."""
    return [m for m in range(2, n + 1)
            if all(m % d for d in range(2, int(m ** 0.5) + 1))]


def ceil_div(a, b):
    """ceil(a / b) for positive b."""
    return -(-a // b)


def threefold(A, p):
    """The set 3A = {a + b + c mod p : a, b, c in A} (repetitions allowed)."""
    return {(a + b + c) % p for a in A for b in A for c in A}


def conjecture_value(p):
    """The conjectured threshold ceil((p+1)/3) + 1."""
    return ceil_div(p + 1, 3) + 1


def universal_value(p):
    """The universal threshold ceil((p+2)/3) (also a counting upper bound)."""
    return ceil_div(p + 2, 3)


# ---------------------------------------------------------------------------
# true existential minimum, exhaustively
# ---------------------------------------------------------------------------

def true_minimum(p):
    """The least k such that some k-element A <= F_p has 3A = F_p.

    Method.  At most C(k+2,3) distinct three-fold sums can be formed from k
    elements (choices are unordered multisets of size 3), so k can be assumed
    to satisfy C(k+2,3) >= p.  For every k from 1 upwards we enumerate all
    C(p,k) subsets in lexicographic order and stop at the first covering set.
    For p <= 30 this reaches at most k = 6, and the running time is seconds.
    """
    full = set(range(p))
    k = 1
    while True:
        if comb(k + 2, 3) >= p:
            for S in combinations(range(p), k):
                if threefold(list(S), p) == full:
                    return k, S
        k += 1


# ---------------------------------------------------------------------------
# p = 7 witness
# ---------------------------------------------------------------------------

def witness_report(p=7):
    A = [0, 1, 3]
    sums = threefold(A, p)
    assert sums == set(range(p)), (A, sums)
    assert len(set(A)) == 3
    reps = {}
    for a in A:
        for b in A:
            for c in A:
                reps.setdefault((a + b + c) % p, (a, b, c))
    print("Decisive counterexample: p = 7")
    print("  A = {0, 1, 3}, |A| = 3")
    print("  3A = {" + ", ".join(str(y) for y in sorted(sums)) + "} = F_7")
    print("  witness triples (one per residue):")
    for y in range(p):
        a, b, c = reps[y]
        print("    %d = %d + %d + %d" % (y, a, b, c))
    print("  conjectured value at p = 7: ceil((7+1)/3) + 1 = %d"
          % conjecture_value(7))
    print("  true minimum at p = 7:      3   (so 3 < 4: the conjecture")
    print("  overestimates the existential threshold by one)")
    print()
    return sums == set(range(p)) and conjecture_value(7) == 4


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

EXPECTED_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
EXPECTED_TRUE = [2, 2, 3, 3, 4, 4, 5, 5, 5, 6]
EXPECTED_CONJ = [2, 3, 3, 4, 5, 6, 7, 8, 9, 11]
EXPECTED_UNIV = [2, 2, 3, 3, 5, 5, 7, 7, 9, 11]
EXPECTED_CONJ_MISMATCH = [3, 7, 11, 13, 17, 19, 23, 29]
EXPECTED_UNIV_MISMATCH = [11, 13, 17, 19, 23, 29]
# conjectured vs universal threshold: exactly p = 3 and p = 1 (mod 3)
EXPECTED_CONJ_VS_UNIV = [3, 7, 13, 19]


def main():
    ok = True
    print("=" * 82)
    print("Conjecture 00000001070: smallest |A| with 3A = F_p is")
    print("ceil((p+1)/3) + 1   -- claimed, but FALSE")
    print("=" * 82)
    print()

    ok &= witness_report(7)

    ps = primes_upto(30)
    print("Existential minimum, computed exhaustively (some A of size k")
    print("covers F_p); compared with the conjecture and with the universal")
    print("threshold ceil((p+2)/3) (every A of size k covers F_p).")
    print()
    header = ("  p   true   conj=ceil((p+1)/3)+1   univ=ceil((p+2)/3)   "
              "conj?  univ?")
    print(header)
    print("-" * len(header))

    true_vals, conj_vals, univ_vals = [], [], []
    conj_mism, univ_mism = [], []
    for p in ps:
        k_true, witness = true_minimum(p)
        conj = conjecture_value(p)
        univ = universal_value(p)
        true_vals.append(k_true)
        conj_vals.append(conj)
        univ_vals.append(univ)
        conj_ok = (conj == k_true)
        univ_ok = (univ == k_true)
        if not conj_ok:
            conj_mism.append(p)
        if not univ_ok:
            univ_mism.append(p)
        print("%3d   %4d   %21d   %17d   %-5s  %-5s"
              % (p, k_true, conj, univ,
                 "ok" if conj_ok else "BAD", "ok" if univ_ok else "BAD"))

    # Consistency with the hard-coded exhaustive table.
    if (ps != EXPECTED_PRIMES or true_vals != EXPECTED_TRUE
            or conj_vals != EXPECTED_CONJ or univ_vals != EXPECTED_UNIV):
        print()
        print("TABLE MISMATCH against expected exhaustive values")
        ok = False

    if conj_mism != EXPECTED_CONJ_MISMATCH:
        print("UNEXPECTED conjecture mismatch set: %s" % conj_mism)
        ok = False
    if univ_mism != EXPECTED_UNIV_MISMATCH:
        print("UNEXPECTED universal mismatch set: %s" % univ_mism)
        ok = False

    print()
    print("Conjecture ceil((p+1)/3)+1 fails to be the existential minimum at")
    print("  p = %s" % ", ".join(str(p) for p in conj_mism))
    print("and fails to be the universal threshold at")
    print("  p = %s" % ", ".join(str(p) for p in conj_mism if p in EXPECTED_CONJ_VS_UNIV))

    conj_vs_univ = [p for p in ps if conjecture_value(p) != universal_value(p)]
    print()
    print("Conjecture vs universal threshold differ exactly at p = %s"
          % ", ".join(str(p) for p in conj_vs_univ))
    print("  (p = 3, the only prime 0 (mod 3), and the primes p = 1 (mod 3))")
    if conj_vs_univ != EXPECTED_CONJ_VS_UNIV:
        print("  UNEXPECTED difference set")
        ok = False

    # The witness is decisive.
    if not (len({0, 1, 3}) == 3 and threefold([0, 1, 3], 7) == set(range(7))
            and conjecture_value(7) == 4):
        ok = False

    print()
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
