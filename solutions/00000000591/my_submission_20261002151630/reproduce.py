#!/usr/bin/env python3
"""
Reproduction script for the disproof of TLMC conjecture 00000000591 (v2).

Conjecture (new-direction attaché to Wilf, conjectures/00000000591.md):
on embedding-dimension-3 numerical semigroups the surplus ratio
    (3*n(S) - g(S) - 3) / g(S)
tends to 0 as g(S) -> infinity.

Disproof: the explicit infinite family
    S_k = <6, 2*(6k+5), 3*(6k+5)>   (k = 0, 1, 2, ...)
is a family of complete-intersection (hence symmetric) numerical semigroups of
embedding dimension 3 with
    g_k   = 42*k + 29          (Frobenius number)
    n_k   = 21*k + 15          (nongaps on [0, g_k])
    sur_k = 3*n_k - g_k - 3 = 21*k + 13
    ratio = sur_k / g_k = (g-3)/(2g) -> 1/2  (>= 1/3 for all k, since g >= 29)

This script verifies, by exhaustive enumeration (no closed formulas trusted):
  1. for every k in 0..K_MAX and a set of large spot-check k:
       - g_k = 42k+29 is a gap and the 6r consecutive integers above it are
         nongaps, so g_k is exactly the Frobenius number of S_k;
       - n_k = 21k+15 is the exact nongap count on [0, g_k];
       - surplus_k = 21k+13; ratio_k >= 1/3; gcd(surplus_k, g_k) = 1;
  2. the same closed formulas on the prime-triple family <pq, pr, qr> for
     (p,q,r) = (2,3,5), (2,3,7), (2,5,7), (3,5,7);
  3. the ratio tends to 1/2 along the family.
"""

from math import gcd

def representable(a, b, c, n):
    """n in <a,b,c> (exhaustive bounded search: y <= n//b, z <= n//c)."""
    for y in range(n // b + 1):
        for z in range(n // c + 1):
            s = y * b + z * c
            if s <= n and (n - s) % a == 0:
                return True
    return False

def semigroup_facts(a, b, c, g_guess, cover):
    """Check that g_guess is exactly the Frobenius number of <a,b,c> and
    return (g, n, surplus, ratio)."""
    assert not representable(a, b, c, g_guess), f"{g_guess} is representable"
    for k in range(cover):  # a consecutive nongaps above g close the semigroup
        assert representable(a, b, c, g_guess + 1 + k), f"{g_guess+1+k} is a gap"
    n = sum(1 for t in range(g_guess + 1) if representable(a, b, c, t))
    surplus = 3 * n - g_guess - 3
    return g_guess, n, surplus, surplus / g_guess

print("=" * 72)
print("1. Infinite family S_k = <6, 12k+10, 18k+15>  (p,q,r) = (2,3,6k+5)")
print("=" * 72)
K_MAX = 300
for k in list(range(K_MAX + 1)) + [500, 1000, 5000, 100000]:
    r = 6 * k + 5
    a, b, c = 6, 2 * r, 3 * r
    g, n, sur, ratio = semigroup_facts(a, b, c, 42 * k + 29, cover=a)
    assert g == 42 * k + 29
    assert n == 21 * k + 15
    assert sur == 21 * k + 13
    assert gcd(sur, g) == 1
    assert ratio >= 1 / 3, (k, ratio)
    if k <= 5 or k % 50 == 0 or k > K_MAX:
        print(f"  k={k:>6}  S=<{a},{b},{c}>  g={g:>8}  n={n:>8}  "
              f"surplus={sur:>8}  ratio={ratio:.6f}")
print("  OK: g=42k+29, n=21k+15, surplus=21k+13, ratio >= 1/3, gcd=1 "
      f"for all k in 0..{K_MAX} and spot checks")

print()
print("=" * 72)
print("2. Prime-triple complete intersections <pq, pr, qr>")
print("=" * 72)
for (p, q, r) in [(2, 3, 5), (2, 3, 7), (2, 5, 7), (3, 5, 7)]:
    g, n, sur, ratio = semigroup_facts(p * q, p * r, q * r,
                                       2*p*q*r - p*q - p*r - q*r,
                                       cover=p * q)
    assert n == (g + 1) // 2 and sur == (g - 3) // 2
    print(f"  (p,q,r)=({p},{q},{r}):  S=<{p*q},{p*r},{q*r}>  g={g:>4}  n={n:>3}  "
          f"surplus={sur:>3}  ratio={ratio:.6f}  ( (g-3)/(2g) = {(g-3)/(2*g):.6f} )")
print("  OK: n=(g+1)/2, surplus=(g-3)/2, ratio=(g-3)/(2g)")

print()
print("=" * 72)
print("3. The ratio tends to 1/2, not 0")
print("=" * 72)
for k in [0, 10, 100, 1000, 10000, 1000000]:
    g = 42 * k + 29
    sur = 21 * k + 13
    print(f"  k={k:>7}:  surplus/g = {sur}/{g} = {sur/g:.9f}")
print("  OK: ratio -> 1/2 from above 1/3; the conjectured limit 0 is false.")
print()
print("ALL CHECKS PASSED.")
