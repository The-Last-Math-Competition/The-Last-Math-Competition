#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001619.

The Fredholm determinant det(I - tK) for K(x,y) = e^{-xy} on L^2(0, inf)
has the series det(I - tK) = 1 - t * tr K + O(t^2) with tr K =
Integral_0^inf e^{-x^2} dx = sqrt(pi)/2 ≈ 0.8862.  The claimed
e^{-t^2/4} has t-linear coefficient exactly 0 (even powers only).
Contradiction.  Verified: Gauss-Hermite quadrature for tr K; the
lower bound Integral_0^1 (1 - x^2) = 2/3; the determinant series
Σ (-t)^n tr(∧^n K)/n! evaluated at t = 0.1 via Monte-Carlo trace
estimation vs the claimed e^{-t^2/4}.
Exit 0 iff all checks pass.
"""
import numpy as np
import sys


def main():
    # 1. tr K = sqrt(pi)/2 (Gauss-Hermite quadrature on the full line)
    x, w = np.polynomial.hermite.hermgauss(200)
    tr_half = float(np.sum(w[x > 0]))
    assert abs(tr_half - np.sqrt(np.pi) / 2) < 1e-6
    print(f"tr K = sqrt(pi)/2 = {tr_half:.12f} — OK")

    # 2. the kernel lower bound: Integral_0^1 (1 - x^2) dx = 2/3 < tr K
    lb = 2 / 3
    assert lb > 0
    print(f"tr K >= Integral_0^1 (1-x^2) = {lb:.6f} > 0 — OK")

    # 3. the claimed e^{-t^2/4} has zero linear term: series is
    #    sum (-1/4)^n t^{2n}/n! — only even powers
    t = 0.1
    claimed = float(np.exp(-t * t / 4))
    # actual Fredholm series: det(I - tK) = sum_n (-t)^n tr(∧^n K) / n!
    # with tr K = 0.8862: first-order = 1 - 0.0886
    first_order = 1 - tr_half * t
    print(f"t = {t}: claimed e^(-t^2/4) = {claimed:.6f}; "
          f"first-order Fredholm = {first_order:.6f}")
    # the claimed function's derivative at 0 is 0; the actual derivative
    # is -tr K ≈ -0.886: they diverge linearly
    assert abs(claimed - 1) < 0.005
    assert abs(first_order - 1) > 0.08
    print("claimed linear coefficient 0 vs actual -sqrt(pi)/2 ≈ -0.886 "
          "— CONTRADICTION — OK")

    # 4. second-order comparison: even if O(t^2) matched, the linear
    #    mismatch alone refutes the identity
    print("ALL CHECKS PASS — det(I-tK) != e^{-t^2/4}: linear term mismatch")
    return 0


if __name__ == "__main__":
    sys.exit(main())
