#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001581.

The Fricke surface x^2 + y^2 + z^2 - x*y*z = 1 over F_5 has exactly 6
F_5-points, while the conjectured point-count pattern
N_p = p^2 + a*p + 1 (a in {-1,0,1}) demands N_5 in {21, 26, 31}.
Exit 0 iff all checks pass.
"""
import sys


def main():
    p = 5
    k = 1
    sols = []
    for x in range(p):
        for y in range(p):
            for z in range(p):
                if (x * x + y * y + z * z - x * y * z - k) % p == 0:
                    sols.append((x, y, z))
    print(f"Fricke surface kappa = {k} over F_{p}: N = {len(sols)} points")
    print("points:", sols)
    assert len(sols) == 6
    assert set(sols) == {(0, 0, 1), (0, 0, 4), (0, 1, 0),
                         (0, 4, 0), (1, 0, 0), (4, 0, 0)}

    # the conjectured pattern at p = 5
    pattern = [p * p + a * p + 1 for a in (-1, 0, 1)]
    print("pattern values:", pattern)
    assert len(sols) not in pattern
    print(f"N = {len(sols)} not in {pattern} — pattern VIOLATED")

    # kappa = 1 is genuinely of PVI type (the generic kappa surface);
    # also count for the degenerate kappa = 0 for contrast
    sols0 = sum(1 for x in range(p) for y in range(p) for z in range(p)
                if (x * x + y * y + z * z - x * y * z) % p == 0)
    print(f"contrast, kappa = 0: N = {sols0} (not needed for refutation)")

    print("ALL CHECKS PASS — N_5 = 6 not in {21, 26, 31}: pattern refuted")
    return 0


if __name__ == "__main__":
    sys.exit(main())
