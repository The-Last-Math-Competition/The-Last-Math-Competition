#!/usr/bin/env python3
"""
Independent brute-force disproof verification for TLMC conjecture 00000001190
at (n, q) = (2, 7). No external dependencies, no absolute paths, no reliance on
any other artifact in this package.

Enumerates ALL 7^4 = 2401 matrices [[a, b], [c, d]] over Z/7Z, keeps those with
det != 0 (this is GL_2(F_7)), and counts:
  * elements of order exactly 2:  M != I and M^2 == I
  * elements of order exactly 3:  M != I and M^3 == I
then compares against the conjecture's formula values
  Theta_2(7) = 7^(4-2) * (7^1 - 1)/(7 - 1) = 49   (claimed N_2)
  0                                              (claimed N_3, since 3 does not divide 2)
"""

Q = 7
N = 2  # matrix size; this script is specific to 2x2

I = (1, 0, 0, 1)  # identity as (a, b, c, d) meaning [[a, b], [c, d]]


def det(m):
    a, b, c, d = m
    return (a * d - b * c) % Q


def mul(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return (
        (a * e + b * g) % Q,
        (a * f + b * h) % Q,
        (c * e + d * g) % Q,
        (c * f + d * h) % Q,
    )


def is_identity(m):
    return m == I


def has_exact_order(m, k):
    """True iff m^k == I and m^j != I for all 1 <= j < k."""
    p = I
    for _ in range(k):
        p = mul(p, m)
    if p != I:
        return False
    p = I
    for _ in range(k - 1):
        p = mul(p, m)
        if p == I:
            return False
    return True


def theta_r(q, n, r):
    """Theta_r(q) = q^(n^2 - r) * (q - 1)^(-1) * prod_{i=1}^{r-1} (q^(n - i) - 1).

    Computed over the integers; the result is an integer because q - 1 divides
    each factor (q^(n-i) - 1).
    """
    num = q ** (n * n - r)
    for i in range(1, r):
        num *= q ** (n - i) - 1
    assert num % (q - 1) == 0
    return num // (q - 1)


def main():
    all_matrices = [
        (a, b, c, d)
        for a in range(Q)
        for b in range(Q)
        for c in range(Q)
        for d in range(Q)
    ]
    print(f"total 2x2 matrices over Z/{Q}Z : {len(all_matrices)} (expect 2401)")
    assert len(all_matrices) == 2401

    gl = [m for m in all_matrices if det(m) != 0]
    print(f"|GL_2(F_7)|                    : {len(gl)} (expect 2016)")
    assert len(gl) == 2016

    order2 = [m for m in gl if not is_identity(m) and has_exact_order(m, 2)]
    order3 = [m for m in gl if not is_identity(m) and has_exact_order(m, 3)]
    print(f"elements of order exactly 2    : {len(order2)} (expect 57)")
    print(f"elements of order exactly 3    : {len(order3)} (expect 170)")
    assert len(order2) == 57
    assert len(order3) == 170

    formula_n2 = theta_r(Q, N, 2)  # sum over prime r | 2 is just r = 2
    formula_n3 = 0                 # no prime r | 2 equals 3 -> empty sum
    print(f"formula value for p=2 (Theta_2(7)) : {formula_n2} (expect 49)")
    print(f"formula value for p=3 (empty sum)  : {formula_n3} (expect 0)")
    assert formula_n2 == 49
    assert formula_n3 == 0

    # The conjecture ("zero error") is refuted twice:
    assert len(order2) != formula_n2, "conjecture unexpectedly correct for p=2"
    assert len(order3) != formula_n3, "conjecture unexpectedly correct for p=3"

    print()
    print("VERDICT: conjecture 00000001190 is FALSE at (n, q) = (2, 7):")
    print(f"  p=2: actual {len(order2)} != formula {formula_n2}")
    print(f"  p=3: actual {len(order3)} != formula {formula_n3}")
    print("All assertions passed.")


if __name__ == "__main__":
    main()
