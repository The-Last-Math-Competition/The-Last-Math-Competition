#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002348.

Random 4x4 nonsingular matrices: the condition number kappa = smax/smin
>= 1 always. The claimed expectation m^{-1/2} = 1/2 at m = 4 is below
the universal lower bound: it cannot be the expectation.
Exit 0 iff all checks pass.
"""
import sys
import numpy as np


def main():
    rng = np.random.default_rng(0)
    kappas = []
    for _ in range(20000):
        A = rng.standard_normal((4, 4))
        s = np.linalg.svd(A, compute_uv=False)
        if s[-1] > 1e-9:
            kappas.append(s[0] / s[-1])
    kappas = np.array(kappas)
    print(f"samples: {len(kappas)}; min kappa = {kappas.min():.4f}; "
          f"mean = {kappas.mean():.4f}")
    assert kappas.min() >= 1.0
    assert kappas.mean() > 1.0
    print(f"claimed expectation m^(-1/2) at m = 4: {4 ** -0.5:.4f}")
    assert 4 ** -0.5 < 1.0 <= kappas.mean()
    print("ALL CHECKS PASS — claimed closed form below the universal "
          "lower bound kappa >= 1")
    return 0


if __name__ == "__main__":
    sys.exit(main())
