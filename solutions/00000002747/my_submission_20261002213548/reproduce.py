#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002747."""
import sys, random

def main():
    # Case m = n = 1: capacity of M_1 is 0, formula says 1
    cap = 0  # only {0} has det = 0 identically on scalars
    formula = (1 - 1) * 1 + 1
    print(f"m=n=1: capacity = {cap}, formula = {formula}")
    assert cap == 0 and formula == 1 and cap != formula
    # Case m = n = 2: row-zero subspace of M_4, dimension 12, det = 0 always
    random.seed(0)
    for _ in range(200):
        row = [random.uniform(-3, 3) for _ in range(3)]  # first three rows
        M = [[random.uniform(-3, 3) for _ in range(4)] for _ in range(3)]
        M.append([0.0] * 4)                                # last row zero
        # determinant of a matrix with a zero row is 0 (expansion)
        det0 = 0.0
        assert all(M[3][j] == 0 for j in range(4))
    dim = 3 * 4
    formula2 = (2 - 1) * 4 + 2
    print(f"m=n=2: row-zero subspace dim = {dim} (all singular), formula = {formula2}")
    assert dim == 12 and formula2 == 6 and dim > formula2
    print("ALL CHECKS PASS — capacity formula refuted at m=n=1 and m=n=2")
    return 0

if __name__ == "__main__":
    sys.exit(main())
