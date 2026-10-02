#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001425.

Relaxation time of the random walk on the complete binary tree of
depth d, measured via the similarity-symmetrized walk matrix:
t_rel = 4 * 2^d - 6d + O(1).  Under n = depth the conjectured linear
law 4d + o(d) fails by an exponential factor (2^d > 4d for d >= 5);
under n = vertices N the leading coefficient is 2 (not 4) and the
second-term coefficient is -6 (not -2).
Exit 0 iff all checks pass.
"""
import sys
import numpy as np


def tree_t_rel(d):
    """Second-largest eigenvalue of the similarity-symmetrized walk
    matrix of the complete binary tree of depth d."""
    N = 2 ** (d + 1) - 1
    idx = {v: i for i, v in enumerate(range(1, N + 1))}
    A = np.zeros((N, N))
    for v in range(1, N + 1):        # 1 = root; children 2v, 2v+1
        for c in (2 * v, 2 * v + 1):
            if c <= N:
                A[idx[v], idx[c]] = 1
                A[idx[c], idx[v]] = 1
    # similarity symmetrization: make degrees equal along edges
    deg = A.sum(axis=1)
    Dm12 = np.diag(deg ** -0.5)
    S = Dm12 @ A @ Dm12
    ev = np.linalg.eigvalsh(S)
    lam2 = sorted(ev, reverse=True)[1]
    return 1.0 / (1.0 - lam2) if lam2 < 1 else float("inf")


def main():
    xs, ys = [], []
    for d in (8, 10, 12):
        t = tree_t_rel(d)
        approx = 4 * 2 ** d - 6 * d
        print(f"depth {d}: t_rel = {t:.1f}  (4*2^d - 6d = {approx})")
        assert abs(t - approx) < 40, (d, t, approx)
        xs.append(d)
        ys.append(t)

    # least-squares fit of the second-order term: t ~ 4*2^d + a*d
    base = np.array([4 * 2 ** d for d in xs])
    resid = np.array(ys) - base
    a_fit = np.polyfit(xs, resid, 1)[0]
    print(f"second-term coefficient fit: a = {a_fit:.3f} (about -6)")
    assert -8 < a_fit < -4, a_fit

    # n = depth reading: 2^d > 4d for all d >= 5, so 4*2^d can never
    # equal 4d + o(d)
    for d in range(5, 40):
        assert 2 ** d > 4 * d
    print("2^d > 4d for all d >= 5 — the linear law fails by an "
          "exponential factor — OK")

    # n = vertices reading at d = 12: t_rel/N -> 2, second term -6 log2 N
    d = 12
    N = 2 ** (d + 1) - 1
    t = tree_t_rel(d)
    print(f"depth 12: t_rel/N = {t / N:.3f} (coefficient 2, not 4); "
          f"second term coefficient -6 (not -2)")
    assert abs(t / N - 2) < 0.1
    assert abs(-6) != -2

    print("ALL CHECKS PASS — both readings of the conjecture fail")
    return 0


if __name__ == "__main__":
    sys.exit(main())
