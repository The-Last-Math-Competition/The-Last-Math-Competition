#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001485.

The Arnold cat map A = [[2,1],[1,1]] is hyperbolic.  Its periodic
counts N_k = |det(A^k - I)| = L_{2k} - 2 (even Lucas), and its zeta
function is the rational function (1-z)^2 / (1 - 3z + z^2) with poles
at (3 +- sqrt 5)/2 ~ {0.382, 2.618}.  The radius of convergence is
(3 - sqrt 5)/2 ~ 0.382 < 1 (NOT 1), and the unit circle carries no
singularity — both clauses of the conjecture fail.  Suspension flows
preserve the periodic-orbit counts, so the same holds for the
suspension.
Exit 0 iff all checks pass.
"""
import math
import sys
from fractions import Fraction as F
from decimal import Decimal, getcontext
getcontext().prec = 60


def main():
    # 1. periodic counts via |det(A^k - I)|, A = [[2,1],[1,1]]
    A = [[2, 1], [1, 1]]

    def mul(X, Y):
        return [[X[0][0]*Y[0][0] + X[0][1]*Y[1][0],
                 X[0][0]*Y[0][1] + X[0][1]*Y[1][1]],
                [X[1][0]*Y[0][0] + X[1][1]*Y[1][0],
                 X[1][0]*Y[0][1] + X[1][1]*Y[1][1]]]

    Ak = [[1, 0], [0, 1]]
    counts = []
    for k in range(1, 7):
        Ak = mul(Ak, A)
        det = (Ak[0][0] - 1) * (Ak[1][1] - 1) - Ak[0][1] * Ak[1][0]
        counts.append(abs(det))
    print("periodic counts N_k =", counts)
    assert counts[:4] == [1, 5, 16, 45]

    # 2. the closed-form zeta function
    l1 = (3 + math.sqrt(5)) / 2
    l2 = (3 - math.sqrt(5)) / 2
    print(f"eigenvalues: {l1:.6f}, {l2:.6f}")
    # zeta(z) = (1-z)^2 / ((1-l1 z)(1-l2 z)); poles at 1/l1, 1/l2
    p1 = 1 / l1
    p2 = 1 / l2
    print(f"poles: {p1:.6f} (= (3-sqrt5)/2), {p2:.6f}")
    assert abs(p1 - (3 - math.sqrt(5)) / 2) < 1e-12
    assert p1 < 1 < p2

    # 3. radius of convergence = distance to nearest pole < 1
    radius = p1
    assert radius < 1
    print(f"radius of convergence = {radius:.6f} < 1 — clause 1 VIOLATED")

    # 4. singular set vs roots of unity: nearest pole is real in (0,1),
    #    not a root of unity (roots of unity on the unit circle have
    #    modulus exactly 1; this pole has modulus 0.382)
    assert abs(p1) != 1 and abs(p2) != 1
    print("singular set = {0.382, 2.618} — no root of unity; "
          "no unit-circle singularity — clause 2 VIOLATED")

    # 5. verify the zeta series expansion numerically at z = 0.3 (|z| < r):
    #    extend the counts via the Lucas recurrence N_k = 3N_{k-1} - N_{k-2} + 2
    N = counts[:]
    while len(N) < 61:
        N.append(3 * N[-1] - N[-2] + 2)
    z = F(3, 10)
    l1f = F(3, 2) + F(1, 2) * F(5).sqrt() if False else None
    # exact: work with Fraction z and exact closed form via float
    series = F(0)
    for k in range(1, 61):
        series += N[k - 1] * z ** k / k
    series_f = math.exp(float(series))
    closed = (1 - float(z)) ** 2 / ((1 - float(l1) * float(z)) *
                                    (1 - float(l2) * float(z)))
    del l1f
    print(f"zeta(0.3): exp(sum) = {series_f:.10f}, closed form = "
          f"{closed:.10f}")
    assert abs(series_f - closed) < 1e-6

    print("ALL CHECKS PASS — radius ≈ 0.382 < 1; no unit-circle "
          "singularities for the Arnold cat map suspension")
    return 0


if __name__ == "__main__":
    sys.exit(main())
