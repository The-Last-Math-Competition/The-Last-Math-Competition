#!/usr/bin/env python3
"""
Independent reproduction script for the disproof of TLMC conjecture 00000000427.

Conjecture (paraphrased): "Spin symmetric plane partitions are plane partitions
in a cubic box symmetric under all diagonals and weighted by spin.  Their count
at t = 1 equals 2^{floor(n^2/4)} * prod_{i=1..n} (2i-1)!! / i!, ..."

At t = 1 the spin weight is identically 1 and does not affect any count.

Encoding (standard): a plane partition in an n x n x n cubic box is an order
ideal of the poset [n]x[n]x[n], equivalently a monotone non-decreasing height
function
    h : {0,...,n-1}^3 -> {0,1},
h(cell) = 1 iff the ideal contains the cell.  MacMahon's product formula
    M(n) = prod_{i,j,k=1..n} (i+j+k-1)/(i+j+k-2)
counts ALL plane partitions in the box (no symmetry): M(1) = 2, M(2) = 20.
The enumeration below reproduces these totals exactly, then counts the
diagonal-symmetric ones.

Two natural readings of "symmetric under all diagonals" are enumerated:
  A (mirror):  h invariant under every transposition of coordinates:
               h(i,j,k) = h(j,i,k) = h(k,j,i)   for all cells;
  B (cyclic):  h invariant under the 3-cycle (i->j->k->i):
               h(i,j,k) = h(j,k,i)              for all cells.

Verdict: under BOTH readings, for n = 1 and n = 2, the true symmetric count
differs from the conjectural closed form, so the conjecture is FALSE.
"""

from fractions import Fraction
from itertools import product
from math import factorial


def cells(n):
    """The n^3 cells (i, j, k) of the cube {0,...,n-1}^3."""
    return list(product(range(n), repeat=3))


def all_heights(n):
    """All 2^(n^3) {0,1}-valued functions on the cube, as dicts cell -> 0/1."""
    cs = cells(n)
    for assignment in product((0, 1), repeat=len(cs)):
        yield dict(zip(cs, assignment))


def monotone(h, n):
    """h is non-decreasing along each coordinate (the 3n^2 cover relations)."""
    for (i, j, k) in cells(n):
        if i + 1 < n and h[(i, j, k)] > h[(i + 1, j, k)]:
            return False
        if j + 1 < n and h[(i, j, k)] > h[(i, j + 1, k)]:
            return False
        if k + 1 < n and h[(i, j, k)] > h[(i, j, k + 1)]:
            return False
    return True


def sym_mirror(h, n):
    """Reading A: invariant under all coordinate transpositions."""
    for (i, j, k) in cells(n):
        if h[(i, j, k)] != h[(j, i, k)]:
            return False
        if h[(i, j, k)] != h[(k, j, i)]:
            return False
    return True


def sym_cyclic(h, n):
    """Reading B: invariant under the coordinate 3-cycle."""
    for (i, j, k) in cells(n):
        if h[(i, j, k)] != h[(j, k, i)]:
            return False
    return True


def macMahon(n):
    """MacMahon's product formula for the total number of plane partitions."""
    p = Fraction(1)
    for (i, j, k) in product(range(1, n + 1), repeat=3):
        p *= Fraction(i + j + k - 1, i + j + k - 2)
    assert p.denominator == 1
    return p.numerator


def ddouble(m):
    """Double factorial m!! (m = 2i-1 is odd here)."""
    r = 1
    for x in range(m, 0, -2):
        r *= x
    return r


def conjecture(n):
    """The conjectured closed form 2^{floor(n^2/4)} * prod (2i-1)!!/i!."""
    f = Fraction(2 ** (n * n // 4))
    for i in range(1, n + 1):
        f *= Fraction(ddouble(2 * i - 1), factorial(i))
    return f


def main():
    print("Disproof of TLMC conjecture 00000000427 (t = 1, spin weight == 1)")
    print("encoding: monotone {0,1}-valued height functions on {0..n-1}^3")
    print()
    for n in (1, 2):
        total_functions = 2 ** (n ** 3)
        mono = [h for h in all_heights(n) if monotone(h, n)]
        mirror = [h for h in mono if sym_mirror(h, n)]
        cyclic = [h for h in mono if sym_cyclic(h, n)]
        formula = conjecture(n)
        print(f"n = {n}:")
        print(f"  all 0-1 height functions      : {total_functions}  (= 2^{n**3})")
        print(f"  monotone (= plane partitions) : {len(mono)}"
              f"  (MacMahon product formula: {macMahon(n)})")
        print(f"  mono + mirror symmetry (A)    : {len(mirror)}")
        print(f"  mono + cyclic symmetry (B)    : {len(cyclic)}")
        print(f"  conjectured formula value     : {formula}")
        assert len(mono) == macMahon(n), "enumeration must reproduce MacMahon"
        assert len(mirror) != formula, "reading A unexpectedly matches formula"
        assert len(cyclic) != formula, "reading B unexpectedly matches formula"
        print(f"  => both readings refute the formula "
              f"({len(mirror)} != {formula} and {len(cyclic)} != {formula})")
        print()
    # show the 5 symmetric plane partitions of the 2x2x2 box explicitly
    n = 2
    mono = [h for h in all_heights(n) if monotone(h, n)]
    mirror = [h for h in mono if sym_mirror(h, n)]
    print("The 5 diagonally symmetric plane partitions in the 2x2x2 box,")
    print("given by orbit values (a, b, c, d) = "
          "(h(0,0,0), h(1,0,0), h(1,1,0), h(1,1,1)):")
    for h in mirror:
        print("   ", tuple(h[c] for c in
                           [(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1)]))


if __name__ == "__main__":
    main()
