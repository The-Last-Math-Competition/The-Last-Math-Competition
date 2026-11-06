#!/usr/bin/env python3
"""Exact check of conjecture 00000007468 (weight-limsup shift spectral disk).

Object. Unilateral forward weighted shift W on l^2(N), N = {0,1,2,...}:
    W e_k = w_k e_{k+1},   w_k = 2 if k odd, w_k = 1/2 if k even.

Standard definitions used (not remembered formulas):
  * sigma(W) = { lam in C : lam*I - W is not invertible in B(l^2) }.
  * r(W) = sup { |lam| : lam in sigma(W) }  (spectral radius).
  * limsup_k w_k = lim_{K->inf} sup_{k>=K} w_k.
  * ||W^n|| for a weighted shift: W^n e_k = P_{k,n} e_{k+n} with
    P_{k,n} = prod_{i=k}^{k+n-1} w_i, and the vectors e_{k+n} are orthogonal,
    so ||W^n|| = sup_k P_{k,n}  (exact, not an estimate).
  * Gelfand: r(W) = lim_n ||W^n||^{1/n}.

Conjecture: sigma(W) is a disk and its radius equals limsup_k w_k.

Everything below is exact rational arithmetic (fractions.Fraction) except the
last printed float column, which is only for display.
"""
from fractions import Fraction as F


def w(k: int) -> F:
    return F(2) if k % 2 == 1 else F(1, 2)


def window_product(k: int, n: int) -> F:
    p = F(1)
    for i in range(k, k + n):
        p *= w(i)
    return p


BIG = 1000  # finite range used for checks that are periodic anyway


def main() -> None:
    print("== 1. Weights and limsup ==")
    print("sup_{k<1000} w_k =", max(w(k) for k in range(BIG)))
    for K in [1, 2, 10, 100, 500, 990]:
        tail_sup = max(w(k) for k in range(K, BIG))
        print(f"  sup_(k>={K}, k<1000) w_k = {tail_sup}")
    print("  => limsup_k w_k = 2 (tail suprema are all 2; w_k = 2 for every odd k)")
    assert all(w(k) == 2 for k in range(1, BIG, 2))
    assert all(w(k) == F(1, 2) for k in range(0, BIG, 2))

    print()
    print("== 2. Consecutive products (W^2 e_k = w_k w_{k+1} e_{k+2}) ==")
    cons = [w(k) * w(k + 1) for k in range(BIG)]
    print("  all w_k*w_{k+1} == 1 for k<1000:", all(c == 1 for c in cons))
    assert all(c == 1 for c in cons)
    print("  => W^2 e_k = e_{k+2} exactly: W^2 is an isometry, W^2 ~ S (+) S,")
    print("     where S is the unweighted unilateral shift.")

    print()
    print("== 3. ||W^n|| = sup_k P_{k,n} and Gelfand-type quantities ==")
    print(f"{'n':>3} {'||W^n|| (exact)':>18} {'expected':>9} {'||W^n||^(1/n) (display)':>26}")
    ok = True
    for n in range(1, 61):
        # P_{k,n} is 2-periodic in k, so sup over k in [0, 2) is exact;
        # we take a wider window [0, 200) as a sanity check of periodicity.
        Mn = max(window_product(k, n) for k in range(200))
        Mn_check = max(window_product(k, n) for k in range(0, 2))
        assert Mn == Mn_check, (n, Mn, Mn_check)
        expected = F(2) if n % 2 == 1 else F(1)
        ok = ok and (Mn == expected)
        if n <= 10 or n % 10 == 0:
            print(f"{n:>3} {str(Mn):>18} {str(expected):>9} {float(Mn) ** (1.0 / n):>26.10f}")
    print("  all M_n match the predicted pattern (2 for odd n, 1 for even n):", ok)
    assert ok

    print()
    print("== 4. Spectral radius bounds ==")
    # Elementary upper bound: for any bounded T and n >= 1, sigma(T) lies in
    # {|lam| <= ||T^n||^(1/n)}. Take n = 2: ||W^2|| = 1, so r(W) <= 1.
    n2 = max(window_product(k, 2) for k in range(200))
    print(f"  ||W^2|| = {n2}  =>  r(W) <= ||W^2||^(1/2) = 1  (Neumann-series bound)")
    assert n2 == 1
    # Spectral mapping for the polynomial p(z)=z^2:
    #   sigma(W^2) = { lam^2 : lam in sigma(W) }.
    # W^2 is unitarily equivalent to S (+) S, and sigma(S) = closed unit disk,
    # so sigma(W^2) = closed unit disk, hence r(W)^2 = r(W^2) = 1, i.e. r(W) = 1.
    print("  sigma(W^2) = sigma(S (+) S) = closed unit disk  (spectral mapping)")
    print("  => r(W) = 1 exactly")

    # Rotation invariance: U_theta = diag(e^{i k theta}) gives U W U^* = e^{i theta} W,
    # so sigma(W) is rotation invariant. Combined with sigma(W)^2 = closed disk
    # this forces sigma(W) = closed unit disk exactly.
    print("  rotation invariance: U_t W U_t^* = e^{it} W  (checked analytically:")
    print("    U e_k = e^{ikt} e_k gives U W U^* e_k = e^{it} w_k e_{k+1})")
    print("  => sigma(W) = closed unit disk {|z| <= 1}")

    print()
    print("== 5. Verdict on the conjecture ==")
    limsup_w = 2
    r_W = 1
    print(f"  claimed radius  = limsup w_k = {limsup_w}")
    print(f"  actual spectral radius r(W)  = {r_W}")
    print("  The spectrum IS a disk (centered 0, radius 1), but its radius is 1, not 2.")
    print("  A disk of radius 2 cannot lie inside the closed unit disk, so no disk of")
    print("  radius 2 (at any centre) equals sigma(W).")
    assert r_W != limsup_w
    print("  => the radius identity r = limsup w_k is FALSE for this shift.")


if __name__ == "__main__":
    main()
