#!/usr/bin/env python3
"""
Reproduction script for the refutation of conjecture 00000001323.

Conjecture (conjectures/00000001323.md):
    In Aut(C^2), the set of possible periods of elements whose Jacobian is
    constant 1 is {1, 2, 3, 4, 6}.

Refutation:
    For every m >= 1, zeta_m = exp(2*pi*i/m) is a primitive m-th root of unity,
    and A_m = diag(zeta_m, zeta_m^{-1}) is a linear (hence polynomial)
    automorphism of C^2.  Its Jacobian is the constant matrix A_m with
    det A_m = zeta_m * zeta_m^{-1} = 1, and A_m has order exactly m.
    Therefore every positive integer m is a period; in particular 5, which is
    not in {1,2,3,4,6}.

This script builds A_m symbolically with sympy for m = 5..12 and verifies,
for each m:
    (1) det(A_m) == 1                        (Jacobian determinant 1)
    (2) A_m**m == I                          (period divides m)
    (3) A_m**k != I for every 1 <= k < m     (period is exactly m)

Exit code 0 iff all checks PASS.  Uses only the Python standard library and
sympy.
"""

import sys

import sympy as sp

# The conjectured set of possible periods.
CONJECTURED = {1, 2, 3, 4, 6}

M_START, M_STOP = 5, 12  # inclusive range of periods to test


def matrix_eq_identity(M):
    """Exact symbolic test: is the 2x2 matrix M equal to the identity?"""
    diff = (M - sp.eye(2)).applyfunc(sp.simplify)
    return diff == sp.zeros(2, 2)


def is_zero_exact(expr):
    """Exact symbolic test: is expr identically zero?"""
    return sp.simplify(expr) == 0


def nonzero_numeric(expr, tol=1e-12):
    """High-precision numeric corroboration that expr is not zero."""
    val = complex(sp.N(expr, 40))
    return abs(val) > tol


def check(m):
    """Return (ok, list_of_report_lines) for the witness A_m."""
    lines = []
    zeta = sp.exp(2 * sp.pi * sp.I / m)
    A = sp.Matrix([[zeta, 0], [0, zeta ** -1]])

    ok = True

    # (1) determinant is 1
    det = sp.simplify(A.det())
    det_ok = is_zero_exact(det - 1)
    ok &= det_ok
    lines.append("  det(A_%d) = %s  -> %s" % (m, det, "PASS" if det_ok else "FAIL"))

    # (2) period divides m: A_m**m = I
    Am = A ** m
    pow_ok = matrix_eq_identity(Am)
    # scalar corroboration in the two diagonal slots
    pow_ok &= is_zero_exact(zeta ** m - 1)
    pow_ok &= is_zero_exact(zeta ** (-m) - 1)
    ok &= pow_ok
    lines.append("  A_%d ** %d == I  -> %s" % (m, m, "PASS" if pow_ok else "FAIL"))

    # (3) period is exactly m: A_m**k != I for 1 <= k < m
    distinct = True
    for k in range(1, m):
        Ak = A ** k
        if matrix_eq_identity(Ak):
            distinct = False
        # the first diagonal entry zeta**k must differ from 1
        if is_zero_exact(zeta ** k - 1) or not nonzero_numeric(zeta ** k - 1):
            distinct = False
    ok &= distinct
    lines.append(
        "  A_%d ** k != I for 1 <= k < %d  -> %s"
        % (m, m, "PASS" if distinct else "FAIL")
    )

    # Consistency with the claim: m should witness a period outside the set.
    if m not in CONJECTURED:
        lines.append("  period %d is NOT in %s" % (m, sorted(CONJECTURED)))

    return ok, lines


def main():
    print("Conjecture 00000001323 refutation: diag(zeta_m, zeta_m^{-1}) over C")
    print("Conjectured period set: %s" % sorted(CONJECTURED))
    print("=" * 64)
    all_ok = True
    for m in range(M_START, M_STOP + 1):
        ok, lines = check(m)
        all_ok &= ok
        print("m = %d: %s" % (m, "PASS" if ok else "FAIL"))
        for line in lines:
            print(line)
        print("-" * 64)

    if all_ok:
        print(
            "RESULT: PASS -- every m in %d..%d occurs as a period, so the "
            "period set is not %s." % (M_START, M_STOP, sorted(CONJECTURED))
        )
        print("In particular m = 5 occurs, and 5 is not in the conjectured set.")
        return 0
    print("RESULT: FAIL")
    return 1


if __name__ == "__main__":
    sys.exit(main())
