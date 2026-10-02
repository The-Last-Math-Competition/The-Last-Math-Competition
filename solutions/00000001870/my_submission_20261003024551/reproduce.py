#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001870.

Monte-Carlo sampling of Haar U(N) via QR decomposition of complex
Ginibre matrices: the third moment E[(TrU)^3] = 0 by rotation symmetry
(verified numerically), so kappa_3 = 0, not the claimed 2*pi*i/(3N).
Exit 0 iff all checks pass.
"""
import sys
import random
import cmath
import math


def haar_unitary(n, rng):
    """QR of a complex Ginibre matrix, R positive-diagonal -> Haar."""
    A = [[complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(n)]
         for _ in range(n)]
    # Gram-Schmidt
    basis = []
    for j in range(n):
        v = [A[i][j] for i in range(n)]
        for b in basis:
            proj = sum((v[i] * b[i].conjugate() for i in range(n)),
                       start=0j)
            v = [v[i] - proj * b[i] for i in range(n)]
        norm = math.sqrt(sum((x.real ** 2 + x.imag ** 2) for x in v))
        basis.append([x / norm for x in v])
    # U = columns of basis (as rows here): U[i][j] = basis[j][i]
    return [[basis[j][i] for j in range(n)] for i in range(n)]


def trace3(U):
    t = sum(U[i][i] for i in range(len(U)))
    return t * t * t


def main():
    rng = random.Random(0)
    for N in (2, 3, 5):
        samples = []
        for _ in range(20000):
            U = haar_unitary(N, rng)
            samples.append(trace3(U))
        mean = sum(samples) / len(samples)
        spread = max(abs(s) for s in samples)
        print(f"N = {N}: E[(TrU)^3] ≈ {mean:.5f} + {mean.imag:.5f}i "
              f"(individual samples have |.| up to ~{spread:.2f})")
        assert abs(mean) < 0.05

    claimed_n1 = 2 * math.pi / 3
    print(f"claimed kappa_3 = 2*pi*i/(3N): at N = 1 that is "
          f"{claimed_n1:.4f}i (nonzero); at N = 2, 3 nonzero as well")
    print("ALL CHECKS PASS — E[(TrU)^3] = 0 by rotation symmetry; "
          "kappa_3 = 0, not 2*pi*i/(3N)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
