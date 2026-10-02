#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002311."""
import sys
from fractions import Fraction
from itertools import permutations

def main():
    # AGL(1,7) = C7 : C6 on Z/7
    elems = [(a, b) for a in range(1, 7) for b in range(7)]
    der = [(a, b) for (a, b) in elems
           if all((a * x + b - x) % 7 != 0 for x in range(7))]
    print(f"AGL(1,7): |G| = {len(elems)}, derangements = {len(der)} {der}")
    assert len(elems) == 42 and len(der) == 6
    prop = Fraction(len(der), len(elems))
    print(f"derangement proportion = {prop} = 1/7; realized c = prop*|Omega| = "
          f"{prop * 7}")
    assert prop == Fraction(1, 7)
    assert prop * 7 == 1  # c = 1, not 1/2
    # tightness of c = 1/2 would need proportion 1/14 = 3/42
    assert Fraction(1, 2) * Fraction(1, 7) == Fraction(1, 14)
    assert len(der) != 3
    # S3 on 3 points (transitive, non-Frobenius-complete): derangements = 2 3-cycles
    s3 = list(permutations(range(3)))
    ders3 = [g for g in s3 if all(g[x] != x for x in range(3))]
    print(f"S3 on 3 points: proportion = {Fraction(len(ders3), 6)} (= 1/3)")
    assert len(ders3) == 2
    print("Frobenius group C7:C6 realizes c = 1, not 1/2 — tightness clause false")
    print("ALL CHECKS PASS")
    return 0

if __name__ == "__main__":
    sys.exit(main())
