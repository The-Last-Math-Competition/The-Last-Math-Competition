"""
Conjecture 00000005399 -- exact check of the claimed mixing correction to return times.

Definitions (standard, finite irreducible discrete-time Markov chain on states 0..n-1):
  P          row-stochastic transition matrix, rational entries
  pi         stationary distribution: pi P = pi, sum(pi) = 1
  T_x        hitting time of x: min{n >= 0 : X_n = x}
  T_x^+      first return time to x: min{n >= 1 : X_n = x}   ("number of steps of the first return")
  E_x[T_x^+] expected first return time, computed from the hitting-time system
  gap        spectral gap 1 - max{|lambda| : lambda eigenvalue of P, lambda != the Perron root 1}
             (the "mixing rate"; only used to exhibit the claimed c/gap term)

Conjectured form (scanner's reading): E_x[T_x^+] = 1/pi(x) + c/gap with c != 0, exactly.

All core quantities use exact fractions.Fraction. No value is taken from a remembered formula.
"""
import random
from fractions import Fraction as F

try:
    import numpy as np
except ImportError:  # gap is only used for display; exact checks do not need numpy
    np = None


def solve_exact(A, b):
    """Gauss-Jordan elimination over Fractions. Raises if A is singular."""
    n = len(A)
    M = [[F(v) for v in A[i]] + [F(b[i])] for i in range(n)]
    for col in range(n):
        piv = next((r for r in range(col, n) if M[r][col] != 0), None)
        if piv is None:
            raise ValueError("singular system")
        M[col], M[piv] = M[piv], M[col]
        p = M[col][col]
        M[col] = [v / p for v in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [a - f * c for a, c in zip(M[r], M[col])]
    return [M[i][n] for i in range(n)]


def inverse_exact(A):
    n = len(A)
    inv = [[F(0)] * n for _ in range(n)]
    for j in range(n):
        e = [F(1) if i == j else F(0) for i in range(n)]
        x = solve_exact(A, e)
        for i in range(n):
            inv[i][j] = x[i]
    return inv


def stationary(P):
    """Solve pi P = pi, sum(pi) = 1 exactly: equations sum_i pi_i (P[i][j] - delta_ij) = 0."""
    n = len(P)
    A = [[F(P[i][j]) - (1 if i == j else 0) for i in range(n)] for j in range(n)]
    b = [F(0)] * n
    A[n - 1] = [F(1)] * n          # replace one redundant equation by normalisation
    b[n - 1] = F(1)
    return solve_exact(A, b)


def hitting_times_to(P, x):
    """h[y] = E_y[T_x] for all y, with h[x] = 0. System: h_y - sum_{z != x} P[y][z] h_z = 1 for y != x."""
    n = len(P)
    S = [y for y in range(n) if y != x]
    idx = {y: k for k, y in enumerate(S)}
    A = [[F(0)] * len(S) for _ in S]
    b = [F(1)] * len(S)
    for y in S:
        for z in S:
            A[idx[y]][idx[z]] = (1 if y == z else 0) - F(P[y][z])
    hS = solve_exact(A, b)
    h = [F(0)] * n
    for y in S:
        h[y] = hS[idx[y]]
    return h


def return_time(P, x):
    """E_x[T_x^+] = 1 + sum_y P[x][y] h_y, where h_y = E_y[T_x]."""
    h = hitting_times_to(P, x)
    return 1 + sum(F(P[x][y]) * h[y] for y in range(len(P)))


def mean_first_passage_fundamental(P, pi):
    """Independent cross-check: Z = (I - P + Pi)^{-1}, E_i[T_j] = (Z_jj - Z_ij) / pi_j for i != j."""
    n = len(P)
    A = [[(1 if i == j else 0) - F(P[i][j]) + pi[j] for j in range(n)] for i in range(n)]
    Z = inverse_exact(A)
    m = [[(Z[j][j] - Z[i][j]) / pi[j] if i != j else None for j in range(n)] for i in range(n)]
    return m


def spectral_gap(P):
    if np is None:
        return None
    M = np.array([[float(v) for v in row] for row in P])
    mags = sorted(np.abs(np.linalg.eigvals(M)), reverse=True)
    return 1.0 - mags[1]


def check_chain(name, P):
    n = len(P)
    P = [[F(v) for v in row] for row in P]
    for i in range(n):
        assert sum(P[i]) == 1, f"{name}: row {i} not stochastic"
        assert all(v >= 0 for v in P[i]), f"{name}: negative entry"
    pi = stationary(P)
    assert sum(pi) == 1 and all(p > 0 for p in pi), f"{name}: pi not a positive distribution"
    for j in range(n):
        assert sum(pi[i] * P[i][j] for i in range(n)) == pi[j], f"{name}: pi P != pi"
    fp = mean_first_passage_fundamental(P, pi)
    gap = spectral_gap(P)
    rows = []
    for x in range(n):
        h = hitting_times_to(P, x)
        for i in range(n):
            if i != x:
                assert h[i] == fp[i][x], f"{name}: hitting time mismatch with fundamental matrix"
        E = return_time(P, x)
        inv = 1 / pi[x]
        rows.append((x, E, inv, E - inv))
    return pi, rows, gap


def report(name, P):
    pi, rows, gap = check_chain(name, P)
    gap_s = f"{gap:.6g}" if gap is not None else "n/a"
    print(f"== {name}  (n={len(P)})  gap={gap_s}")
    print("   pi = " + ", ".join(str(p) for p in pi))
    all_zero = True
    for x, E, inv, D in rows:
        all_zero &= (D == 0)
        print(f"   x={x}: E_x[T_x^+] = {E}  1/pi(x) = {inv}  difference = {D}")
    print(f"   exact difference zero in all states: {all_zero}")
    if gap is not None and gap > 1e-9:
        print(f"   implied c = difference * gap = 0 in all states; claimed c=1 would need difference = 1/gap = {1/gap:.6g}")
    return all_zero


def main():
    chains = []
    chains.append(("P0 (scanner's chain)", [[F(1, 2), F(1, 4), F(1, 4)],
                                            [F(1, 3), F(1, 3), F(1, 3)],
                                            [F(1, 5), F(2, 5), F(2, 5)]]))
    chains.append(("P1 non-reversible 3-cycle-with-return", [[0, 1, 0],
                                                            [0, 0, 1],
                                                            [F(1, 2), F(1, 2), 0]]))
    chains.append(("P2 periodic (gap = 0)", [[0, 1, 0],
                                            [F(1, 2), 0, F(1, 2)],
                                            [0, 1, 0]]))
    rng = random.Random(5399)
    for k, n in enumerate([4, 4, 5, 5, 5, 4]):
        W = [[rng.randint(1, 9) for _ in range(n)] for _ in range(n)]
        P = [[F(w, sum(row)) for w in row] for row in W]
        chains.append((f"random{k} n={n} (positive integer weights 1..9, seed 5399)", P))

    all_ok = True
    for name, P in chains:
        all_ok &= report(name, P)
        print()

    print("SUMMARY")
    print(f"  chains checked: {len(chains)}")
    print(f"  Kac identity E_x[T_x^+] = 1/pi(x) exact (zero difference) in every state of every chain: {all_ok}")
    print("  Consequence: E_x[T_x^+] - 1/pi(x) = 0 = c/gap forces c = 0 for any finite positive rate;")
    print("  any nonzero c contradicts the identity, whatever the mixing-rate normalisation.")
    print("  Counterexample (P0, state 0): E = 23/8 = 1/pi(0); claimed value 23/8 + c/gap with c != 0 is not equal.")


if __name__ == "__main__":
    main()
