#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001870.

The third cumulant of Tr U under Haar measure on U(N) is exactly 0 for
every N (Haar invariance under U -> zeta*U rotates Tr U by zeta; the
third moment of a 90-degree-rotation-invariant distribution is zero).
The conjectured decay kappa_3 = c_3/N with c_3 = 2*pi*i/3 (a nonzero
imaginary constant) contradicts this.  Monte Carlo check at N = 2, 3.
Exit 0 iff all checks pass.
"""
import numpy as np
import sys


def haar_u(n, rng):
    z = (rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    d = np.diagonal(r)
    q = q * (d / np.abs(d))
    return q


def main():
    rng = np.random.default_rng(2026)
    for N in (2, 3):
        trials = 60000
        m3 = 0.0j
        m1 = 0.0j
        m2 = 0.0
        for _ in range(trials):
            U = haar_u(N, rng)
            t = U.trace()
            m3 += t**3
            m1 += t
            m2 += abs(t) ** 2
        m3 /= trials
        m1 /= trials
        m2 /= trials
        print(f"N = {N}: E[Tr] = {m1:.4f}, E[|Tr|^2] = {m2:.4f}, "
              f"E[(Tr)^3] = {m3:.5f}")
        assert abs(m1) < 0.01
        assert abs(m2 - 1) < 0.02          # known: E|Tr U|^2 = 1
        assert abs(m3) < 0.02, m3          # third moment vanishes (noise-scaled)

        # the conjectured value kappa_3 = 2*pi*i/(3N) is nonzero-imaginary
        import cmath
        claimed = 2 * cmath.pi * 1j / (3 * N)
        print(f"  claimed kappa_3 ~ {claimed} (magnitude "
              f"{abs(claimed):.3f}, nonzero imaginary)")
        assert abs(claimed) > 10 * abs(m3)  # claimed constant far from 0
    print("ALL CHECKS PASS — third cumulant is exactly 0, not c_3/N")
    return 0


if __name__ == "__main__":
    sys.exit(main())
