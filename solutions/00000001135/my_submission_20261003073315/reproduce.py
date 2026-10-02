#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001135.

For a reduced word s_1...s_k the Bott-Samelson variety is an iterated
P^1-bundle, so its Betti generating function is P(t) = (1 + t^2)^k.
The conjecture's divisibility clause requires (1+t)^{floor(k/2)} | P(t)
with monic quotient; but (1+t) never divides (1+t^2)^k for k >= 1
(evaluation at t = -1: 0 = 2^k).  The note's quotient
(1+t)^{ceil(k/2)} * (1-t)^k for k = 6 has coefficients
1, -3, 0, 8, -6, -6, 8, 0, -3, 1 — with internal zeros — violating the
no-internal-zeros clause as well.
Exit 0 iff all checks pass.
"""
import sys


def polymul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def main():
    # 1. reduced words: P(t) = (1+t^2)^k; (1+t) does not divide it
    for k in (1, 2, 3, 4, 5, 6):
        P = [1]
        for _ in range(k):
            P = polymul(P, [1, 0, 1])  # 1 + t^2
        # direct: P(t) at t = -1
        at_minus1 = sum(c * (-1) ** i for i, c in enumerate(P))
        assert at_minus1 == 2 ** k, (k, at_minus1)
        print(f"k = {k}: P(-1) = 2^{k} = {at_minus1} != 0 — (1+t) does "
              f"not divide")
    # the divisibility check by polynomial long division over Z[t]
    for k in (2, 4, 6):
        P = [1]
        for _ in range(k):
            P = polymul(P, [1, 0, 1])
        # try dividing by (1+t): synthetic division root -1
        rem = 0
        Q = []
        for c in reversed(P):
            rem = c + rem * (-1)
            Q.insert(0, rem)
        assert rem != 0, (k, rem)
        print(f"k = {k}: remainder of P mod (1+t) = {rem} != 0 — not divisible")

    # 2. the note's quotient for k = 6: (1+t)^3 * (1-t)^6
    Q6 = [1]
    for _ in range(3):
        Q6 = polymul(Q6, [1, 1])
    for _ in range(6):
        Q6 = polymul(Q6, [1, -1])
    assert Q6 == [1, -3, 0, 8, -6, -6, 8, 0, -3, 1], Q6
    assert 0 in Q6[1:-1], "internal zero present"
    print("k = 6 quotient coefficients: 1, -3, 0, 8, -6, -6, 8, 0, -3, 1 "
          "(internal zero) — no-internal-zeros clause violated")

    # 3. monotonicity clause also fails at k = 2: P = 1 + 2t^2 + t^4
    P2 = [1, 0, 2, 0, 1]
    assert P2[1] == 0  # coefficient 0 breaks strict increase immediately
    print("strict increase clause: P(1+t^2)^2 has zero coefficients — "
          "strict increase fails")
    print("ALL CHECKS PASS — the conjecture's clauses fail for reduced words")
    return 0


if __name__ == "__main__":
    sys.exit(main())
