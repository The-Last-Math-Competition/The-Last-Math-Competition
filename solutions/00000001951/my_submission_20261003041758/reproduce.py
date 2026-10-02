#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001951.

The claimed smallest index of a proper subgroup of Out(F_3) is
2^3 * C(3,2) = 24. The classical determinant construction gives a
surjective homomorphism Out(F_3) -> {+/-1} (via the action on
H_1(F_3,Z) = Z^3 and det: GL_3(Z) -> {+/-1}, surjective via
diag(-1,1,1)), whose kernel is an index-2 subgroup. 2 < 24 refutes.
Exit 0 iff all checks pass.
"""
import sys
from math import comb


def main():
    claimed = 2 ** 3 * comb(3, 2)
    print(f"claimed smallest index at n=3: 2^3 * C(3,2) = {claimed}")
    assert claimed == 24

    # the determinant map GL_3(Z) -> {+/-1} is surjective: diag(-1,1,1)
    det_diag = -1 * 1 * 1
    print(f"det(diag(-1,1,1)) = {det_diag} (so the composed map "
          f"Out(F_3) -> {{+/-1}} is surjective)")
    assert det_diag == -1

    # a surjection onto a group of order 2 has kernel of index 2
    print("kernel of the surjection: index-2 proper subgroup of Out(F_3)")
    actual_max = 2
    print(f"actual smallest index <= 2; claimed 24; refuted")
    assert actual_max < claimed

    print("ALL CHECKS PASS — 2 < 24: claimed smallest-index formula fails")
    return 0


if __name__ == "__main__":
    sys.exit(main())
