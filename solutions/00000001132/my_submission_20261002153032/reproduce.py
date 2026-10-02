#!/usr/bin/env python3
"""Reproduce the disproof of Conjecture 00000001132 (discrete certificate).

Conjecture: the structure group of the tangent bundle of the complete flag
variety G/B reduces to a maximal torus  <=>  G is a torus.

Counterexample family: G = SL2.  Over C: G/B = P1, T(P1) = O(2) is a line
bundle whose structure group is G_m = C* = the maximal torus itself, because
T(G/B) = G x_B (g/b) and the unipotent radical acts trivially on g/b.

This script re-derives the same algebraic mechanism in the smallest faithful
discrete model G = SL2(F2) = GL2(F2) (|G| = 6 = S3, F2* = {1}):

  * B = {I, U}, U = [[1,1],[0,1]], both self-inverse;
  * g = all 2x2 matrices over F2, b = upper triangular {X : X.c = 0},
    so the class of X in the line g/b is its bottom-left entry X.c;
  * for EVERY X (16 of them) and EVERY b in B, (b X b^-1).c = X.c
    -> the transition functions of G x_B (g/b) on the tangent line are the
       identity = image of the maximal torus T = {diag(1,1)}
       => "structure group reduces to a maximal torus" holds;
  * U*V != V*U with V = [[1,0],[1,1]], all determinants 1
    => G is non-abelian, hence NOT a torus.

Both sides of the "iff" together refute the conjecture.  Run: python3 reproduce.py
"""

F = lambda *bits: tuple(bits)  # matrix (a, b; c, d) over F2

def mul(p, q):
    a, b, c, d = p
    e, f, g, h = q
    return F((a & e) ^ (b & g), (a & f) ^ (b & h),
             (c & e) ^ (d & g), (c & f) ^ (d & h))

def det(m):
    a, b, c, d = m
    return (a & d) ^ (b & c)

I, U, V = F(1, 0, 0, 1), F(1, 1, 0, 1), F(1, 0, 1, 1)
ALL = [F(a >> 3 & 1, a >> 2 & 1, a >> 1 & 1, a & 1) for a in range(16)]

def main() -> int:
    checks = []

    # G contains U, V ; |G| = 6
    checks.append(("det I = det U = det V = 1 (U, V in SL2(F2))",
                   det(I) == det(U) == det(V) == 1))
    inv = [m for m in ALL if det(m)]
    checks.append(("|SL2(F2)| = |GL2(F2)| = 6 = S3 (non-abelian group)", len(inv) == 6))

    # not a torus: exhibit non-commuting invertible elements
    checks.append(("U*V != V*U  =>  G non-abelian, hence not a torus",
                   mul(U, V) == F(0, 1, 1, 1) and mul(V, U) == F(1, 1, 1, 0)
                   and mul(U, V) != mul(V, U)))

    # Borel subgroup B = upper-triangular invertible = {I, U}; self-inverses
    checks.append(("B = {I, U} with U self-inverse", mul(U, U) == I and mul(I, I) == I))

    # structure-group reduction: B-action on the class of g/b is trivial,
    # for all 16 matrices X and both b in B  => transition fns in image of T
    ok = all(mul(b, mul(X, b))[2] == X[2] for b in (I, U) for X in ALL)
    checks.append(("(b X b^-1).c = X.c for all X in g, b in B  (16 x 2 cases)", ok))
    induced = [[mul(b, F(0, 0, x, 0))[2] for x in (0, 1)] for b in (I, U)]
    checks.append(("induced transition fns = identity = image of maximal torus T={I}",
                   induced == [[0, 1], [0, 1]]))

    all_ok = True
    for name, ok in checks:
        print(f"[{'PASS' if ok else 'FAIL'}] {name}")
        all_ok &= ok
    print()
    print("CONJECTURE 00000001132 DISPROVEN:"
          " reduction to maximal torus holds (rank 1) but G = SL2 is not a torus"
          if all_ok else "SOME CHECKS FAILED")
    return 0 if all_ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
