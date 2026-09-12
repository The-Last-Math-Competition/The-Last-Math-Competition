#!/usr/bin/env python3
"""
Independent brute-force recalculation for the disproof of TLMC conjecture 00000001854.

Conjecture (literal claim):
    #{M in Mat_n(F_q) : charpoly(M) is squarefree} = q^{n^2} * prod_i (1 - q^{-i^2})
"is an exact closed form".

Method (no sympy, no external deps):
  * Implement F_q for prime q (elements 0..q-1) and for q = 4 (elements
    0,1,w,w^2 with w^2 = w + 1) as small Python field objects.
  * Implement polynomials over such a field (coefficient lists, low-degree first),
    polynomial long division, gcd, derivative.
  * f is squarefree  <=>  gcd(f, f') is a unit (degree 0).
  * n = 1: Mat_1(F_q) = { [a] : a in F_q }, charpoly([a]) = X - a (degree 1,
    derivative = 1, gcd = 1) => every matrix counts => LHS = q.
  * n = 2, q = 2: enumerate all 2^(2*2) = 16 matrices, compute charpoly as
    det(xI - M) and count the squarefree ones.
  * Compare with the conjectured RHS under BOTH natural readings of the
    unbounded product "prod(1 - q^{-i^2})":
        reading A: i = 1..n   (truncated product, matches degree count)
        reading B: i = 1..inf (infinite product, computed exactly as a Fraction,
                              truncated at i <= 10; the tail is < q^{-121})
    and assert that the enumeration disagrees with the formula in every case.

Expected outcome (disproof):
    n = 1: LHS = q for every q, but q*(1 - q^{-1}) = q - 1 != q  (reading A),
           and any product of factors < 1 is < q as well            (reading B).
    n = 2, q = 2: LHS = 8, reading A gives 15/2 (not even an integer).
"""

from fractions import Fraction
from itertools import product as iterproduct

# ---------------------------------------------------------------- finite fields


class PrimeField:
    """F_p for prime p; elements are ints 0..p-1."""

    def __init__(self, p):
        assert p >= 2
        self.p = p
        self.q = p
        self.zero = 0
        self.one = 1
        self.elements = list(range(p))

    def add(self, a, b):
        return (a + b) % self.p

    def neg(self, a):
        return (-a) % self.p

    def mul(self, a, b):
        return (a * b) % self.p

    def inv(self, a):
        assert a % self.p != 0, "0 has no inverse"
        return pow(a, -1, self.p)

    def eq(self, a, b):
        return a == b


class GF4:
    """F_4 = F_2[w]/(w^2 + w + 1); element e encodes a0 + a1*w with e = a0 + 2*a1."""

    def __init__(self):
        self.q = 4
        self.zero = 0
        self.one = 1
        self.elements = [0, 1, 2, 3]  # 0, 1, w, w^2 (= 1 + w)

    def add(self, a, b):  # characteristic 2: componentwise xor
        return a ^ b

    def neg(self, a):  # characteristic 2: a = -a
        return a

    def mul(self, a, b):
        a0, a1 = a & 1, (a >> 1) & 1
        b0, b1 = b & 1, (b >> 1) & 1
        # (a0 + a1 w)(b0 + b1 w) = a0 b0 + (a0 b1 + a1 b0) w + a1 b1 w^2
        # with w^2 = 1 + w
        c0 = a0 * b0 + a1 * b1
        c1 = a0 * b1 + a1 * b0 + a1 * b1
        return (c0 & 1) | ((c1 & 1) << 1)

    def inv(self, a):
        assert a != 0, "0 has no inverse"
        for b in self.elements:
            if b != 0 and self.mul(a, b) == 1:
                return b
        raise AssertionError("unreachable")

    def eq(self, a, b):
        return a == b


def int_mul(field, n, c):
    """n * c inside `field` via repeated addition (n small)."""
    r = field.zero
    for _ in range(n):
        r = field.add(r, c)
    return r


# --------------------------------------------------- polynomials over F_q ------
# coefficient list, low degree first, e.g. [c0, c1, c2] = c0 + c1 X + c2 X^2


def ptrim(f, zero):
    g = list(f)
    while g and g[-1] == zero:
        g.pop()
    return g


def pdeg(f, zero):
    f = ptrim(f, zero)
    return len(f) - 1


def padd(F, f, g):
    n = max(len(f), len(g))
    return ptrim([F.add(f[i] if i < len(f) else F.zero,
                        g[i] if i < len(g) else F.zero) for i in range(n)], F.zero)


def pneg(F, f):
    return ptrim([F.neg(c) for c in f], F.zero)


def pmul(F, f, g):
    if not f or not g:
        return []
    out = [F.zero] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] = F.add(out[i + j], F.mul(a, b))
    return ptrim(out, F.zero)


def psub(F, f, g):
    return padd(F, f, pneg(F, g))


def pderiv(F, f):
    return ptrim([int_mul(F, i, f[i]) for i in range(1, len(f))], F.zero)


def pmod(F, f, g):
    """Remainder of f mod g (Euclidean long division)."""
    r = list(f)
    dg = pdeg(g, F.zero)
    if dg < 0:
        raise ZeroDivisionError("division by zero polynomial")
    while pdeg(r, F.zero) >= dg and r:
        shift = pdeg(r, F.zero) - dg
        factor = F.mul(r[-1], F.inv(g[-1]))
        sub = [F.zero] * shift + [F.mul(factor, c) for c in g]
        r = psub(F, r, sub)
    return ptrim(r, F.zero)


def pgcd(F, f, g):
    a, b = ptrim(f, F.zero), ptrim(g, F.zero)
    while b:
        a, b = b, pmod(F, a, b)
    # normalize to monic (does not change degree)
    if a:
        inv_lc = F.inv(a[-1])
        a = ptrim([F.mul(inv_lc, c) for c in a], F.zero)
    return a


def is_squarefree(F, f):
    """Over a field: f != 0 is squarefree <=> gcd(f, f') has degree 0.

    In particular every degree-1 polynomial X - a has derivative 1, hence
    gcd(X - a, 1) = 1, hence IS squarefree.  This generic check covers that
    case without any special casing.
    """
    if not ptrim(f, F.zero):
        return False  # the zero polynomial is not squarefree by convention
    g = pgcd(F, f, pderiv(F, f))
    return pdeg(g, F.zero) == 0


def charpoly1(F, a):
    """charpoly of the 1x1 matrix [a]:  X - a  ->  [-a, 1]."""
    return [F.neg(a), F.one]


def charpoly2(F, m):
    """charpoly of the 2x2 matrix m = [[a, b], [c, d]]: det(xI - M)."""
    a, b, c, d = m
    x_minus_a = [F.neg(a), F.one]              # X - a  (coeffs low degree first)
    x_minus_d = [F.neg(d), F.one]              # X - d
    diag = pmul(F, x_minus_a, x_minus_d)      # (X - a)(X - d)
    off = [F.mul(b, c)]                        # (-b)(-c) = b c  (constant)
    return psub(F, diag, off)


# ------------------------------------------------------------------ formula ----


def formula_partial(F_q, n):
    """Reading A: q^{n^2} * prod_{i=1..n} (1 - q^{-i^2}), exact rational."""
    res = Fraction(F_q) ** (n * n)
    for i in range(1, n + 1):
        res *= 1 - Fraction(1, F_q ** (i * i))
    return res


def formula_infinite(F_q, n, imax=10):
    """Reading B: q^{n^2} * prod_{i=1..inf} (1 - q^{-i^2}), truncated at i<=imax.

    Tail bound: prod_{i>imax} (1 - q^{-i^2}) differs from the truncation by
    less than sum_{i>imax} q^{-i^2} <= q^{-(imax+1)^2} / (1 - q^{-2(imax+1)-1}),
    which is < 10^{-100} for every case below, so the exact comparison against
    an integer LHS is unaffected by the truncation.
    """
    res = Fraction(F_q) ** (n * n)
    for i in range(1, imax + 1):
        res *= 1 - Fraction(1, F_q ** (i * i))
    return res


# ---------------------------------------------------------------- main --------


def fmt(x):
    return f"{x}  (= {float(x):.6f})" if isinstance(x, Fraction) else str(x)


def main():
    failures_of_conjecture = 0

    # ---------- n = 1 over F_2, F_3, F_4, F_5 ----------
    print("=" * 72)
    print("n = 1: enumerate every matrix [a], a in F_q; charpoly = X - a")
    print("=" * 72)
    for F in (PrimeField(2), PrimeField(3), GF4(), PrimeField(5)):
        q = F.q
        matrices = [[a] for a in F.elements]
        sqfree_flags = [is_squarefree(F, charpoly1(F, a)) for [a] in matrices]
        count = sum(sqfree_flags)
        rhs_A = formula_partial(q, 1)
        rhs_B = formula_infinite(q, 1)
        print(f"\nF_{q}: |Mat_1| = {len(matrices)}")
        print(f"  charpoly([a]) = X - a, degree 1, derivative = 1 -> "
              f"squarefree for ALL {count}/{len(matrices)} matrices")
        print(f"  LHS (enumerated)          = {count}")
        print(f"  RHS reading A (i=1..n)    = {fmt(rhs_A)}")
        print(f"  RHS reading B (i=1..inf)  = {fmt(rhs_B)}")
        assert count == q, "n=1: every 1x1 matrix must have squarefree charpoly"
        assert count != rhs_A, "n=1 reading A unexpectedly equals LHS"
        assert count != rhs_B, "n=1 reading B unexpectedly equals LHS"
        failures_of_conjecture += 1
        print(f"  -> conjecture FAILS at n = 1, q = {q} "
              f"(LHS {count} != RHS {rhs_A} and != {rhs_B})")

    # ---------- n = 2, q = 2 ----------
    print()
    print("=" * 72)
    print("n = 2, q = 2: enumerate all 16 matrices of Mat_2(F_2)")
    print("=" * 72)
    F = PrimeField(2)
    count2 = 0
    for a, b, c, d in iterproduct(F.elements, repeat=4):
        if is_squarefree(F, charpoly2(F, (a, b, c, d))):
            count2 += 1
    rhs_A = formula_partial(2, 2)
    rhs_B = formula_infinite(2, 2)
    print(f"  LHS (enumerated)          = {count2}   (of 16 matrices)")
    print(f"  RHS reading A (i=1..n)    = {fmt(rhs_A)}   <- not an integer!")
    print(f"  RHS reading B (i=1..inf)  = {fmt(rhs_B)}")
    assert count2 == 8, "n=2,q=2: enumeration disagrees with hand check (8)"
    assert count2 != rhs_A and count2 != rhs_B
    failures_of_conjecture += 1
    print(f"  -> conjecture FAILS at n = 2, q = 2 "
          f"(LHS {count2} != RHS {rhs_A}, and the formula is not even an integer)")

    # ---------- verdict ----------
    print()
    print("=" * 72)
    print(f"VERDICT: conjecture 00000001854 is FALSE "
          f"({failures_of_conjecture} counterexample families, all enumerated).")
    print("The proposed formula is not an exact closed form; at n = 1 the true")
    print("count is q while the formula gives q - 1 (reading A), and under the")
    print("infinite-product reading (B) it gives q * (product of factors < 1) < q.")
    print("=" * 72)


if __name__ == "__main__":
    main()
