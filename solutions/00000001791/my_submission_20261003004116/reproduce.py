#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001791.

lct of x^a + y^b (weighted-homogeneous isolated singularity) is
1/a + 1/b (Saito). For d = 3 the claimed layer set is
{1/m : m = 1,2,3} U {n + 1/m}. The value 5/6 = lct(x^2 + y^3) is in
neither layer, checked by exact Fraction arithmetic (equivalently the
cross-multiplication the Lean kernel certifies).
Exit 0 iff all checks pass.
"""
import sys
from fractions import Fraction


def main():
    lct = Fraction(1, 2) + Fraction(1, 3)   # lct(x^2 + y^3) = 5/6
    print(f"lct(x^2 + y^3) = 1/2 + 1/3 = {lct}")

    d = 3
    layer1 = [Fraction(1, m) for m in range(1, d + 1)]
    print(f"layer 1 {{1/m : m <= {d}}}: {layer1}")
    assert lct not in layer1, "5/6 unexpectedly in layer 1"

    # layer 2: n + 1/m for n >= 1, m = 1..d  (and n = 0 reduces to layer 1)
    hits = []
    for n in range(0, 50):
        for m in range(1, d + 1):
            v = Fraction(n, 1) + Fraction(1, m)
            if v == lct:
                hits.append((n, m))
            if n >= 1:
                assert v > lct, f"n+1/m = {v} <= 5/6 at n={n}, m={m}"
    print(f"layer 2 {{n + 1/m}}: no match in n = 0..49, m = 1..{d}; "
          f"all n >= 1 values are > 5/6")
    assert hits == []

    # context: the whole x^a + y^b family of degree <= 6
    print("lct values of x^a + y^b for a + b <= 6, a,b >= 2, vs the claimed layer:")
    for a in range(2, 5):
        for b in range(2, 7 - a):
            v = Fraction(1, a) + Fraction(1, b)
            inside = v in layer1 or any(
                Fraction(n, 1) + Fraction(1, m) == v
                for n in range(0, 10) for m in range(1, d + 1))
            print(f"  x^{a}+y^{b} (degree {a+b}): lct = {v}, inside claimed layer = {inside}")

    print("ALL CHECKS PASS — 5/6 = lct(x^2+y^3) is outside the claimed layer set")
    return 0


if __name__ == "__main__":
    sys.exit(main())
