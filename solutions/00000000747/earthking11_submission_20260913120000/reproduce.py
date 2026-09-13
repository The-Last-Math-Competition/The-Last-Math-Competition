#!/usr/bin/env python3
"""Reproduction script for the disproof of conjecture 00000000747.

Conjecture (quoted): "For p >= 5, the iterative fixed points of x |-> x^p in
Z_p are only 0 and 1 (rigidity of superattracting orbits)."

The script refutes this on the finite residue quotients Z/p^k by explicitly
counting the roots of

    f(x) = x^p - x        (the fixed-point equation x^p = x)

for p = 5, 7, 11 and k = 1..8.  Since

    f'(x) = p*x^(p-1) - 1 = -1 (mod p)

is a unit modulo p, f has simple roots modulo p and Hensel's lemma lifts each
of the p residue classes to exactly one root in Z/p^k.  Hence the count is
exactly p at every level, never 2.

Checks performed (standard library only):

  (a) F_p reading: for each p, the number of residues x in [0, p) with
      x^p = x (mod p) is p (Fermat's little theorem).
  (b) Hensel lifting: the number of roots of f modulo p^k is exactly p for
      every k = 1..8.  The lifter is cross-validated against brute-force
      enumeration of all residues for small k.
  (c) The Hensel lift of the residue class 2 (mod 5) is tracked level by level
      to k = 8; it equals 280182 (mod 5^8), which is neither 0 nor 1.
  (d) 110443 (mod 5^8) is an explicit non-trivial root of x^5 = x (it lies in
      the residue class 3 mod 5).

The script prints a PASS/FAIL summary and exits with status 0 on success.
"""

import sys


# --------------------------------------------------------------------------
# core routines
# --------------------------------------------------------------------------

def roots_in_fp(p):
    """All roots of f(x) = x^p - x in F_p, i.e. residues x in [0, p)."""
    return [x for x in range(p) if (pow(x, p, p) - x) % p == 0]


def roots_by_bruteforce(p, k):
    """All roots of x^p = x modulo p^k, found by scanning every residue."""
    m = p ** k
    return [x for x in range(m) if (pow(x, p, m) - x) % m == 0]


def hensel_lift_all(p, kmax):
    """roots[k] = sorted list of roots of x^p = x modulo p^k, for k = 1..kmax.

    Hensel step: a root a modulo p^k lifts to a + t*p^k for a unique
    t in [0, p); the candidate is kept exactly when it solves the equation
    modulo p^(k+1).  Uniqueness is asserted below.
    """
    roots = {1: roots_in_fp(p)}
    for k in range(1, kmax):
        pk = p ** k
        pk1 = p ** (k + 1)
        lifted = []
        for a in roots[k]:
            found = [t for t in range(p)
                     if (pow(a + t * pk, p, pk1) - (a + t * pk)) % pk1 == 0]
            assert len(found) == 1, (
                "Hensel uniqueness failed for p=%d k=%d a=%d: %r"
                % (p, k, a, found))
            lifted.append((a + found[0] * pk) % pk1)
        roots[k + 1] = sorted(lifted)
    return roots


def hensel_lift_class(p, a0, kmax):
    """Track the unique lift of the class a0 modulo p up to p^kmax.

    Returns the list chain[1..kmax] with chain[j] = lift modulo p^j.
    """
    a = a0 % p
    chain = [None, a]
    for k in range(1, kmax):
        pk = p ** k
        pk1 = p ** (k + 1)
        found = [t for t in range(p)
                 if (pow(a + t * pk, p, pk1) - (a + t * pk)) % pk1 == 0]
        assert len(found) == 1, "no unique lift at p=%d k=%d" % (p, k)
        a = (a + found[0] * pk) % pk1
        chain.append(a)
    return chain


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------

P_LIST = [5, 7, 11]
KMAX = 8


def check_fp_reading():
    print("=" * 72)
    print("(a) F_p reading: number of roots of x^p = x in F_p")
    print("=" * 72)
    ok = True
    for p in P_LIST:
        roots = roots_in_fp(p)
        good = (len(roots) == p)
        ok = ok and good
        print("  p = {:2d}: {:2d} roots (all residues) -> {}   {}".format(
            p, len(roots), roots if p <= 11 else "...",
            "OK" if good else "!! expected %d" % p))
    print("  [a] {}".format("PASS" if ok else "FAIL"))
    return ok


def check_hensel_counts():
    print()
    print("=" * 72)
    print("(b) Hensel lifting: number of roots of x^p = x modulo p^k")
    print("=" * 72)
    ok = True
    for p in P_LIST:
        roots = hensel_lift_all(p, KMAX)
        counts = [len(roots[k]) for k in range(1, KMAX + 1)]
        good = all(c == p for c in counts)
        ok = ok and good
        print("  p = {:2d}: counts k=1..8 = {}   {}".format(
            p, counts, "OK (all equal %d)" % p if good else "!! expected %d" % p))

    # Cross-validate the lifter against brute force on small moduli.
    print("  cross-check against brute-force enumeration:")
    small = [(5, 5), (7, 3), (11, 2)]
    for p, kmax in small:
        roots = hensel_lift_all(p, kmax)
        for k in range(1, kmax + 1):
            lifted = sorted(x % (p ** k) for x in roots[k])
            brute = roots_by_bruteforce(p, k)
            if lifted != brute:
                ok = False
                print("    !! p={} k={}: lift {} != brute {}".format(
                    p, k, lifted, brute))
        print("    p={:2d}, k=1..{}: lift matches brute force".format(p, kmax))
    print("  [b] {}".format("PASS" if ok else "FAIL"))
    return ok


def check_lift_of_two():
    print()
    print("=" * 72)
    print("(c) Hensel lift of the residue class 2 (mod 5) to 5^8")
    print("=" * 72)
    ok = True
    chain = hensel_lift_class(5, 2, KMAX)
    for k in range(1, KMAX + 1):
        a = chain[k]
        assert (pow(a, 5, 5 ** k) - a) % (5 ** k) == 0
        print("  k={}: lift = {:6d} mod 5^{} = {:d}".format(
            k, a, k, 5 ** k))
    a8 = chain[KMAX]
    m8 = 5 ** 8
    print("  lift of class 2 mod 5 to mod 5^8: {}".format(a8))
    if a8 in (0, 1):
        ok = False
        print("  !! lift is 0 or 1")
    if (pow(a8, 5, m8) - a8) % m8 != 0:
        ok = False
        print("  !! lift is not a root")
    if a8 == 0 or a8 == 1:
        ok = False
    print("  lift = {} is neither 0 nor 1, and 5^5-lift = lift (mod 5^8): {}".format(
        a8, "OK" if ok else "FAIL"))
    print("  [c] {}".format("PASS" if ok else "FAIL"))
    return ok


def check_explicit_110443():
    print()
    print("=" * 72)
    print("(d) explicit non-trivial root 110443 modulo 5^8")
    print("=" * 72)
    ok = True
    a = 110443
    m8 = 5 ** 8
    if (pow(a, 5, m8) - a) % m8 != 0:
        ok = False
        print("  !! 110443 is not a root modulo 5^8")
    if a % m8 in (0, 1):
        ok = False
        print("  !! 110443 mod 5^8 is 0 or 1")
    cls = a % 5
    print("  110443 = {} (mod 5); 110443^5 = 110443 (mod 5^8): {}".format(
        cls, "OK" if ok else "FAIL"))
    print("  110443 lies in the residue class {} mod 5; the lift of class 2 is "
          "separate (see (c)).".format(cls))
    print("  [d] {}".format("PASS" if ok else "FAIL"))
    return ok


def main():
    a = check_fp_reading()
    b = check_hensel_counts()
    c = check_lift_of_two()
    d = check_explicit_110443()

    print()
    print("=" * 72)
    print("SUMMARY")
    print("=" * 72)
    print("  (a) F_p reading: p roots               : {}".format("PASS" if a else "FAIL"))
    print("  (b) Hensel counts modulo p^k equal p   : {}".format("PASS" if b else "FAIL"))
    print("  (c) lift of class 2 mod 5 is not 0, 1  : {}".format("PASS" if c else "FAIL"))
    print("  (d) explicit root 110443 mod 5^8       : {}".format("PASS" if d else "FAIL"))
    overall = a and b and c and d
    print("  OVERALL                                : {}".format(
        "PASS" if overall else "FAIL"))
    print()
    print("Conclusion: x |-> x^p has exactly p fixed points modulo p^k for every")
    print("k (p = 5, 7, 11, ..., k <= 8), namely one lift per residue class of F_p.")
    print("For p >= 5 this is at least 5 fixed points, not the 2 claimed, so")
    print("conjecture 00000000747 is FALSE.")
    return 0 if overall else 1


if __name__ == "__main__":
    sys.exit(main())
