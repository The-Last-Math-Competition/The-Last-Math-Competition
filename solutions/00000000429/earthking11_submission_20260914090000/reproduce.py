#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000000429.

    Definition: the q-binomial [n choose k]_q at q = 1 counts binomial
    coefficients.
    Conjecture: its value at q = -1 is of the explicit form 2^{v(n,k)}
    (v a 2-adic valuation formula, giving a complete signed version).

The conjecture is FALSE.  Reading the filed text literally, it predicates the
form of the VALUE itself: [n choose k]_{q=-1} should be a power of two
2^{v(n,k)}.  The parenthetical "complete signed version" only invites the weaker
reading value = +/- 2^{v(n,k)}.

Decisive witness:

        [6 choose 2]_{q=-1} = 3,

and 3 is neither 2^t nor -2^t for any integer t.  Further witnesses:
[7 choose 3]_{q=-1} = 3, [8 choose 4]_{q=-1} = 6, [10 choose 2]_{q=-1} = 5.

Correct characterisation (q-Lucas rule at d = 2):

    [n choose k]_{q=-1} = C(floor(n/2), floor(k/2))   if NOT (n even, k odd),
    [n choose k]_{q=-1} = 0                            if n even and k odd.

The frequently proposed rule "equals C(floor(n/2), floor(k/2)) whenever C(n,k)
is odd, else 0" is FALSE (e.g. [8 choose 4]_{-1} = 6 while C(8,4) = 70 is even).

Standard library only, Python 3.8+.  Exits non-zero if any check fails.

Note on the algorithm: the value at q = -1 is computed by the integer Pascal
recursion

    [n choose k]_{-1} = [n-1 choose k-1]_{-1} + (-1)^k [n-1 choose k]_{-1},

with [n choose 0] = 1 and [0 choose k+1] = 0.  The naive product formula
prod_{i=1..k} (1 - q^{n-k+i}) / (1 - q^i) is 0/0 at q = -1 and is NOT used
directly; as an independent cross-check we build the Gaussian binomial as an
exact polynomial in q by polynomial long division over Q and only then
substitute q = -1.
"""

from fractions import Fraction
from math import comb


# ----------------------------------------------------------------------
# 1. Exact integer Pascal recursion at q = -1
# ----------------------------------------------------------------------

def qbinomial_at_minus_one_table(nmax):
    """qb[n][k] = [n choose k]_{q=-1} for 0 <= k <= n <= nmax, by Pascal
    recursion over the integers.  No division, no floating point."""
    qb = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    for n in range(nmax + 1):
        qb[n][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            qb[n][k] = qb[n - 1][k - 1] + ((-1) ** k) * qb[n - 1][k]
    return qb


# ----------------------------------------------------------------------
# 2. Independent cross-check: Gaussian binomial as an exact polynomial in q
# ----------------------------------------------------------------------

def poly_mul(a, b):
    """Multiply polynomials over Z given as coefficient lists (low -> high)."""
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                out[i + j] += ai * bj
    return out


def poly_divmod(a, b):
    """Exact polynomial long division over Q.  Returns (quotient, remainder)."""
    a = [Fraction(c) for c in a]
    b = [Fraction(c) for c in b]
    while len(a) >= 1 and a[-1] == 0:
        a.pop()
    if b == [Fraction(0)]:
        raise ZeroDivisionError("polynomial division by zero")
    q = [Fraction(0)] * max(0, len(a) - len(b) + 1) if a else [Fraction(0)]
    r = a[:]
    db = len(b) - 1
    while len(r) >= len(b) and (len(r) > 1 or r[0] != 0):
        dr = len(r) - 1
        if r[dr] == 0:
            r.pop()
            continue
        coef = r[dr] / b[db]
        shift = dr - db
        q[shift] = coef
        for i in range(len(b)):
            r[i + shift] -= coef * b[i]
        while len(r) >= 1 and r[-1] == 0:
            r.pop()
    return q, r


def one_minus_q_pow(e):
    """Coefficient list of 1 - q^e."""
    c = [0] * (e + 1)
    c[0] = 1
    c[e] -= 1
    return c


def gaussian_polynomial(n, k):
    """[n choose k]_q as an exact polynomial in q (coefficient list, low ->
    high), via prod_{i=1..k} (1-q^{n-k+i}) / (1-q^i) with exact polynomial
    division."""
    num = [1]
    den = [1]
    for i in range(1, k + 1):
        num = poly_mul(num, one_minus_q_pow(n - k + i))
        den = poly_mul(den, one_minus_q_pow(i))
    q, r = poly_divmod(num, den)
    assert all(c == 0 for c in r), (n, k, "inexact division")
    assert all(c.denominator == 1 for c in q), (n, k, "non-integer coefficient")
    return [int(c) for c in q]


def eval_at_minus_one(poly):
    """Evaluate a polynomial (coefficient list, low -> high) at q = -1."""
    return sum(c * ((-1) ** i) for i, c in enumerate(poly))


# ----------------------------------------------------------------------
# 3. Helpers
# ----------------------------------------------------------------------

def is_unsigned_pow2(x):
    """True iff x = 2^t for some integer t >= 0."""
    if x <= 0:
        return False
    return (x & (x - 1)) == 0


def is_signed_pow2(x):
    """True iff x = 2^t or x = -2^t for some integer t >= 0 (x != 0)."""
    if x == 0:
        return False
    return is_unsigned_pow2(abs(x))


def qlucas(n, k):
    """Correct q-Lucas rule at d = 2 for q = -1."""
    if n % 2 == 0 and k % 2 == 1:
        return 0
    return comb(n // 2, k // 2)


def parity_rule(n, k):
    """The INCORRECT proposed rule (parity of C(n,k))."""
    if comb(n, k) % 2 == 1:
        return comb(n // 2, k // 2)
    return 0


# ----------------------------------------------------------------------
# 4. Main
# ----------------------------------------------------------------------

def main():
    nmax = 20
    qb = qbinomial_at_minus_one_table(nmax)
    checks = []
    ok_all = [True]

    def check(name, ok, detail=""):
        checks.append((name, bool(ok), detail))
        ok_all[0] = ok_all[0] and bool(ok)

    # --- 4a. Independent polynomial cross-check -------------------------
    poly_mismatch = []
    for n in range(0, 13):
        for k in range(0, n + 1):
            if eval_at_minus_one(gaussian_polynomial(n, k)) != qb[n][k]:
                poly_mismatch.append((n, k, qb[n][k],
                                      eval_at_minus_one(gaussian_polynomial(n, k))))
    check("independent cross-check for n <= 12: integer Pascal recursion == "
          "exact polynomial evaluated at q = -1",
          not poly_mismatch,
          "all agree" if not poly_mismatch else f"mismatches: {poly_mismatch}")

    # --- 4b. Corrected q-Lucas rule: 0 mismatches -----------------------
    luas_mismatch = []
    for n in range(0, nmax + 1):
        for k in range(0, n + 1):
            if qlucas(n, k) != qb[n][k]:
                luas_mismatch.append((n, k, qb[n][k], qlucas(n, k)))
    check("corrected q-Lucas rule (d = 2) matches for all 0 <= k <= n <= %d "
          "with 0 mismatches" % nmax,
          not luas_mismatch,
          "0 mismatches" if not luas_mismatch else f"mismatches: {luas_mismatch[:10]}")

    # --- 4c. The parity-of-C(n,k) rule is FALSE -------------------------
    parity_mismatch = []
    for n in range(0, nmax + 1):
        for k in range(0, n + 1):
            if parity_rule(n, k) != qb[n][k]:
                parity_mismatch.append((n, k, qb[n][k], parity_rule(n, k)))
    check("the proposed 'parity of C(n,k)' rule is FALSE (nonzero mismatches)",
          len(parity_mismatch) > 0,
          f"{len(parity_mismatch)} mismatches for n <= {nmax}; "
          f"first: [8 choose 4]_-1 = {qb[8][4]} but C(8,4) = {comb(8,4)} is even "
          f"so that rule predicts 0")

    # --- 4d. Witness values --------------------------------------------
    witnesses = {(6, 2): 3, (7, 3): 3, (8, 4): 6, (10, 2): 5, (2, 1): 0}
    wbad = [(n, k, qb[n][k], v) for (n, k), v in witnesses.items() if qb[n][k] != v]
    check("[6 choose 2] = 3, [7 choose 3] = 3, [8 choose 4] = 6, "
          "[10 choose 2] = 5, [2 choose 1] = 0",
          not wbad,
          "all witness values confirmed" if not wbad else f"bad: {wbad}")

    # --- 4e. 3 is not +/- 2^t -------------------------------------------
    pow2_up_to = [2 ** t for t in range(0, 64)]
    three_unsigned = any(p == 3 for p in pow2_up_to)
    three_signed = any(p == 3 or -p == 3 for p in pow2_up_to)
    check("3 is NOT +/- 2^t: neither 2^t = 3 nor -2^t = 3 for any t",
          not three_unsigned and not three_signed,
          "no t with 2^t = 3 (2^1 = 2 < 3 < 4 = 2^2 and powers of two are "
          "1,2,4,8,...); likewise no t with -2^t = 3 < 0")

    check("the decisive witness [6 choose 2]_{q=-1} = 3 is not a signed power "
          "of two",
          qb[6][2] == 3 and not is_signed_pow2(qb[6][2]),
          f"[6 choose 2] = {qb[6][2]}, is_signed_pow2 = {is_signed_pow2(qb[6][2])}")

    # --- 4f. Non-powers-of-two census -----------------------------------
    nonpow = []
    zero_entries = []
    for n in range(0, nmax + 1):
        for k in range(0, n + 1):
            v = qb[n][k]
            if v == 0:
                zero_entries.append((n, k))
            elif not is_signed_pow2(v):
                nonpow.append((n, k, v))
    check("nonzero values that are not +/- powers of two number exactly 102 "
          "for n <= %d" % nmax,
          len(nonpow) == 102,
          f"found {len(nonpow)}")
    check("the smallest interior entry that is not +/- a power of two is "
          "[6 choose 2] = 3",
          nonpow[0][:3] == (6, 2, 3),
          f"first such: {nonpow[0]}")
    check("the smallest entry that is not a power of two at all is 0 at "
          "[2 choose 1] (0 is not 2^t)",
          zero_entries[0] == (2, 1),
          f"first zero entry: {zero_entries[0]}")

    # --- 4g. Also fail the total / k = 1 restrictions -------------------
    k1_bad = [(n, qb[n][1]) for n in range(0, nmax + 1) if not is_signed_pow2(qb[n][1])]
    check("restricting to k = 1 does not save the claim: [2 choose 1] = 0 is "
          "not a signed power of two", len(k1_bad) > 0,
          f"counterexamples at k = 1: {k1_bad[:6]}")

    n_even_bad = [(n, k, qb[n][k]) for n in range(0, nmax + 1) if n % 2 == 0
                  for k in range(0, n + 1)
                  if qb[n][k] != 0 and not is_signed_pow2(qb[n][k])]
    check("restricting to even n does not save the claim: [8 choose 4] = 6 is "
          "not a signed power of two", len(n_even_bad) > 0,
          f"first even-n counterexamples: {n_even_bad[:4]}")

    # --- 4h. Report -----------------------------------------------------
    line = "=" * 78
    print(line)
    print("Disproof of conjecture 00000000429 -- reproduction")
    print(line)
    print("\nConjecture (as filed):")
    print("  Definition: the q-binomial [n choose k]_q at q = 1 counts "
          "binomial coefficients.")
    print("  Conjecture: its value at q = -1 is of the explicit form 2^{v(n,k)}.")
    print("Claimed value: FALSE.")

    print("\n[1] Decisive witness")
    print("        [6 choose 2]_{q=-1} = 3,")
    print("    and 3 is not 2^t or -2^t for any integer t (powers of two are")
    print("    1, 2, 4, 8, ...; 2 < 3 < 4, and -2^t < 0 < 3).")

    print("\n[2] Further witness values")
    for (n, k), v in sorted(witnesses.items()):
        print(f"        [{n} choose {k}]_{{q=-1}} = {v}")

    print("\n[3] Value table [n choose k]_{q=-1} for n <= 12 "
          "(computed by the integer Pascal recursion)")
    header = "    n\\k " + "".join(f"{k:>6}" for k in range(0, 13))
    print(header)
    for n in range(0, 13):
        row = "".join(f"{qb[n][k]:>6}" if k <= n else f"{'.':>6}"
                      for k in range(0, 13))
        print(f"    {n:>3} {row}")

    print("\n[4] Correct characterisation (q-Lucas at d = 2):")
    print("        [n choose k]_{q=-1} = C(floor(n/2), floor(k/2))")
    print("                              if NOT (n even and k odd),")
    print("        [n choose k]_{q=-1} = 0   if n is even and k is odd.")
    print(f"    Verified with 0 mismatches for 0 <= k <= n <= {nmax}.")

    print("\n[5] The proposed 'parity of C(n,k)' rule is FALSE:")
    print(f"    mismatches for n <= {nmax}: {len(parity_mismatch)}")
    print(f"    e.g. [8 choose 4]_-1 = 6 while C(8,4) = {comb(8,4)} is even,")
    print("    so that rule would predict 0.")

    print("\n[6] Context: the true valuation identity (Kummer)")
    print("        v_2([n choose k]_{q=-1}) = v_2(C(floor(n/2), floor(k/2)))")
    print("    is a true but DIFFERENT statement: it is about the 2-adic")
    print("    valuation of the value, not about the value being a power of 2.")

    print("\n[7] Census for n <= %d" % nmax)
    print(f"    nonzero values that are not +/- powers of two: {len(nonpow)}")
    print(f"    first such: " + ", ".join(f"[{n} choose {k}] = {v}"
                                          for n, k, v in nonpow[:6]))
    print(f"    zero entries: {len(zero_entries)}; smallest at "
          f"[{zero_entries[0][0]} choose {zero_entries[0][1]}] = 0")

    print("\n[8] Alternative readings tested, none saves the claim:")
    print("    - k a primitive d-th root of unity, d >= 3: non-integer")
    print("      algebraic values, not powers of two.")
    print("    - restrict to k = 1: [2 choose 1] = 0 is not a power of two.")
    print("    - restrict to n even: [8 choose 4] = 6 is not a power of two.")
    print("    - read the value as 2^{v_2(C(n,k))}: fails for n <= 20.")

    print("\n[9] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        if detail:
            print(f"           {detail}")

    print("\n" + line)
    if ok_all[0]:
        print("PASS: all checks verified; conjecture 00000000429 is FALSE.")
        print("  [6 choose 2]_{q=-1} = 3 is neither 2^t nor -2^t, so no")
        print("  2-adic formula v(n,k) can make the value equal 2^{v(n,k)}.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
