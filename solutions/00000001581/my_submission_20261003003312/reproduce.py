#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001581.

Exhaustively enumerates ALL F_p-points of the Fricke surface
x^2 + y^2 + z^2 - x*y*z = kappa (the PVI monodromy manifold family) for
p = 2, 3, 5, 7 and every kappa in F_p, and compares with the claimed
pattern N_p = p^2 + a*p + 1, a in {-1, 0, 1}.
Exit 0 iff the checks described in the README pass.
"""
import sys


def main():
    claimed = {5: {5 * 5 + 5 + 1, 5 * 5 + 1, 5 * 5 - 5 + 1}}
    for p in (2, 3, 5, 7):
        counts = {}
        for kappa in range(p):
            n = 0
            for x in range(p):
                for y in range(p):
                    for z in range(p):
                        if (x * x + y * y + z * z - x * y * z - kappa) % p == 0:
                            n += 1
            counts[kappa] = n
        allowed = {p * p + a * p + 1 for a in (-1, 0, 1)}
        print(f"p = {p}: counts per kappa {counts}; claimed-pattern set {sorted(allowed)}")
        if p == 5:
            assert counts[0] == 41 and counts[1] == 6 and counts[2] == 16 \
                and counts[3] == 36 and counts[4] == 26, "F_5 table mismatch"
            for k in (0, 1, 2, 3):
                assert counts[k] not in allowed, f"kappa={k} unexpectedly in set"
            assert counts[4] == 26  # the only coincidental match
            assert len(set(counts.values())) > 1, "count should vary with kappa"
    print("ALL CHECKS PASS — F_5 counts 41/6/16/36/26, four of five outside "
          "{21,26,31}, count varies with kappa")
    return 0


if __name__ == "__main__":
    sys.exit(main())
