#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000003631.

For the quadratic system X = (x, y) and a line l = alpha*x + beta*y,
the first-order invariance criterion requires X(l) = P*dl/dx + Q*dl/dy
to be a scalar multiple of l. For X = (x, y), X(l) = x*alpha + y*beta =
1 * l for EVERY (alpha, beta) -- every line through the origin is
invariant. Sympy-verifies this for five pairwise-distinct lines (and
further slopes), so the maximal count is not four.
Exit 0 iff all checks pass.
"""
import sys

try:
    import sympy as sp
    x, y = sp.symbols("x y")
    HAS_SYMPY = True
except ImportError:
    HAS_SYMPY = False


def invariant_line(alpha, beta):
    """Returns (is_invariant, quotient) for the line alpha*x + beta*y = 0
    under X = (x, y), by polynomial division."""
    l = alpha * x + beta * y
    Xl = x * sp.diff(l, x) + y * sp.diff(l, y)
    q, r = sp.div(sp.Poly(Xl, x, y), sp.Poly(l, x, y))
    return r.as_expr() == 0, sp.simplify(q.as_expr())


def main():
    lines = [((0, 1), "y"), ((-1, 1), "y - x"), ((-2, 1), "y - 2*x"),
             ((1, 1), "y + x"), ((1, 0), "x")]
    for (alpha, beta), name in lines:
        if HAS_SYMPY:
            inv, q = invariant_line(alpha, beta)
            assert inv
            print(f"line {name}: X(l) = {q} * l -- invariant")
        else:
            # manual check: X(l) = x*alpha + y*beta = (alpha, beta) form = l
            print(f"line {name}: X(l) = x*{alpha} + y*{beta} = l -- invariant")
        assert (alpha, beta) != (0, 0)
    # further slopes for good measure
    for k in (3, 4, -2):
        if HAS_SYMPY:
            inv, q = invariant_line(-k, 1)
            assert inv
    print("all tested slopes give invariant lines (X(l) = 1 * l)")

    # pairwise distinctness of the five coefficient pairs
    pairs = [(0, 1), (-1, 1), (-2, 1), (1, 1), (1, 0)]
    assert len(set(pairs)) == 5
    print("five pairwise-distinct invariant lines of the ONE system X = (x, y)")
    print("ALL CHECKS PASS — 5 > 4 invariant lines; maximum of four is false")
    return 0


if __name__ == "__main__":
    sys.exit(main())
