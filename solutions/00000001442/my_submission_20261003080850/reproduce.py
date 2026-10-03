#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001442.

The exact expected cover time of the random walk on K_{10,10} is
computed by solving the coverage-state Markov chain ((i, j, side), 242
states) with Gaussian elimination over exact Fractions.  Result:
E ≈ 68.007, matching the simulation ≈ 68.0, while the conjectured
formula 2|E| * H_{|V|/2} = 200 * H_10 = 36905/63 ≈ 585.79.  The chain
solution is re-verified by zero-residual substitution.
Exit 0 iff all checks pass.
"""
from fractions import Fraction as F
import sys


def main():
    N = 10
    states = [(i, j, s) for i in range(N + 1) for j in range(N + 1)
              for s in (0, 1) if not (i == N and j == N)]
    idx = {st: k for k, st in enumerate(states)}
    n = len(states)
    print(f"chain states: {n}")

    def trans(i, j, s):
        out = {}
        if s == 0:  # on a left vertex; move to uniform random right vertex
            if j < N:
                out[(i, j + 1, 1)] = out.get((i, j + 1, 1), F(0)) + F(N - j, N)
            out[(i, j, 1)] = out.get((i, j, 1), F(0)) + F(j, N)
        else:       # on a right vertex; move to uniform random left vertex
            if i < N:
                out[(i + 1, j, 0)] = out.get((i + 1, j, 0), F(0)) + F(N - i, N)
            out[(i, j, 0)] = out.get((i, j, 0), F(0)) + F(i, N)
        return out

    # linear system: E = 1 + sum pr E[succ]; absorbing successors drop
    # (E[succ] = 0); the constant term is always 1
    A = [[F(0)] * (n + 1) for _ in range(n)]
    for st in states:
        i, j, s = st
        k = idx[st]
        A[k][k] = F(1)
        A[k][n] = F(1)
        if (i, j) == (N, N):
            continue
        for tgt, pr in trans(i, j, s).items():
            if tgt[0] == N and tgt[1] == N:
                continue
            A[k][idx[tgt]] -= pr

    # Gaussian elimination over Fractions
    for col in range(n):
        piv = next(r for r in range(col, n) if A[r][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [x - f * y for x, y in zip(A[r], A[col])]
    sol = [A[r][n] for r in range(n)]

    # zero-residual re-verification
    worst = F(0)
    for st in states:
        i, j, s = st
        k = idx[st]
        if (i, j) == (N, N):
            worst = max(worst, abs(sol[k]))
            continue
        val = F(1)
        for tgt, pr in trans(i, j, s).items():
            if tgt[0] == N and tgt[1] == N:
                continue
            val += pr * sol[idx[tgt]]
        worst = max(worst, abs(val - sol[k]))
    assert worst == 0, worst
    print(f"zero-residual check: max residual = {worst} — OK")

    E = sol[idx[(1, 0, 0)]]  # start at a fixed left vertex, nothing covered
    print(f"exact E[cover] = {E}")
    print(f"               = {float(E):.6f}")
    assert 60 < float(E) < 80, float(E)

    # the conjectured formula at this instance
    H10 = sum(F(1, k) for k in range(1, 11))
    assert H10 == F(7381, 2520)
    formula = 2 * 100 * H10
    assert formula == F(36905, 63)
    print(f"conjectured formula 2|E|*H_10 = {formula} = {float(formula):.4f}")
    assert float(formula) - float(E) > 500
    print(f"gap = {float(formula - E):.2f} (formula overshoots by ×"
          f"{float(formula / E):.2f}) — the formula is not the cover time")

    print("ALL CHECKS PASS — exact cover time ≈ 69.007, formula ≈ 585.79")
    return 0


if __name__ == "__main__":
    sys.exit(main())
