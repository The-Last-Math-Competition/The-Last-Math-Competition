#!/usr/bin/env python3
"""Computational verification for the refutation of conjecture 00000001367.

The conjecture claims:
  * the classical chromatic number of the Cayley graph of Z^2 with generators
    {+/-e1, +/-e2} (i.e. the square grid) is 4, and
  * its Borel chromatic number is 5, because the Borel constraint forces an
    extra color.

This script refutes both values by checking, on a large finite patch of Z^2,
that the parity coloring (i, j) -> (i + j) mod 2 is a proper 2-coloring.

Consequences:
  * chi <= 2.  The patch contains an edge, so chi >= 2, hence chi = 2 (not 4).
  * On the countable space Z^2 every subset is Borel, so the parity coloring is
    Borel measurable: chi_Borel <= 2, and hence chi_Borel = 2 (not 5).

Standard library only.  Prints PASS/FAIL and exits 0 on PASS.
"""

import sys

# Half-width of the finite patch [-N, N]^2 of Z^2.
N = 250


def adj(p, q):
    """Grid adjacency: q is a unit step from p along an axis."""
    return (
        q == (p[0] + 1, p[1])
        or q == (p[0] - 1, p[1])
        or q == (p[0], p[1] + 1)
        or q == (p[0], p[1] - 1)
    )


def col(p):
    """Parity coloring (i, j) -> (i + j) mod 2, values in {0, 1}."""
    return (p[0] + p[1]) % 2


def check_parity_proper(n):
    """Check every edge of the patch [-n, n]^2 is properly colored."""
    for i in range(-n, n + 1):
        for j in range(-n, n + 1):
            p = (i, j)
            cp = col(p)
            for q in ((i + 1, j), (i - 1, j), (i, j + 1), (i, j - 1)):
                if -n <= q[0] <= n and -n <= q[1] <= n:
                    if cp == col(q):
                        return False, (p, q)
    return True, None


def main():
    n = N
    ok, witness = check_parity_proper(n)
    vertices = (2 * n + 1) ** 2

    if not ok:
        p, q = witness
        print(f"FAIL: monochromatic edge {p}--{q} under the parity coloring.")
        print("FAIL (exit 1)")
        return 1

    # Lower bound: an edge exists (e.g. (0,0)--(1,0)), so chi >= 2.
    has_edge = adj((0, 0), (1, 0))
    # 2-coloring exists, so chi <= 2; combined with has_edge, chi = 2.
    chi = 2 if has_edge else 1
    # Countable discrete space => all subsets Borel => parity coloring is Borel.
    chi_borel = chi

    print(f"Checked parity coloring on the patch [-{n}, {n}]^2 "
          f"({vertices} vertices, all internal edges): PROPER")
    print(f"Edge present (e.g. (0,0)--(1,0)): {has_edge}")
    print(f"classical chromatic number chi = {chi}")
    print(f"Borel chromatic number chi_Borel = {chi_borel} "
          f"(Z^2 countable => every subset Borel)")
    print("Conjecture asserts chi = 4 and chi_Borel = 5: both refuted.")
    print("PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
