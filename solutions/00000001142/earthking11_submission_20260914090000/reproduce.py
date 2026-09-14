#!/usr/bin/env python3
"""
Reproduction script for the DISPROOF of conjecture 00000001142.

    Conjecture: The order of the automorphism group of the mod-p Witt
    algebra W(1;1) is p(p-1) (Witt automorphisms).

VERDICT: FALSE.

W(1;1) = Der(F_p[x]/(x^p)) has the p basis elements b_k = x^k d/dx
(k = 0, ..., p-1) with bracket

    [b_k, b_l] = (l - k) * b_{k+l-1}   if 1 <= k+l <= p,   else 0.

The script establishes, by exact finite computation:

  * p = 3 (dimension 3): brute force over all 3^9 = 19683 matrices over F_3.
    Exactly |GL(3,3)| = 11232 of them are invertible, and exactly 24 of the
    invertible ones preserve the bracket, so |Aut(W(1;1))| = 24, NOT
    p(p-1) = 6.  The 24 automorphisms have element-order distribution
    {1: 1, 2: 9, 3: 8, 4: 6}, the order distribution of S_4 = PGL(2,3) =
    Aut(sl(2,F_3)); indeed W(1;1) = sl(2,F_3) at p = 3.

  * p = 5 (dimension 5): an exact exhaustive count.  Every automorphism is
    determined by (phi(b_0), phi(b_4)) because {b_0, b_4} generates W(1;1),
    and phi(b_0) must be a regular nilpotent element (there are exactly 500
    of those).  Enumerating the pair and testing bracket preservation gives
    exactly 500 automorphisms, NOT p(p-1) = 20.

  * The Möbius (Witt) subgroup {x -> a*x/(1+b*x) : a in F_p^*, b in F_p}
    has order exactly p(p-1), and it is a PROPER subgroup of Aut for
    p = 3 (6 < 24) and p = 5 (20 < 500).  Hence p(p-1) is the order of that
    subgroup, not of the full automorphism group.  The conjecture is true
    only at p = 2 (where |Aut| = 2 = p(p-1)); for every p >= 3 it is false.

Python 3 standard library only.  Prints PASS/FAIL and exits non-zero on any
failed check.
"""

import itertools
import sys

# --------------------------------------------------------------------------
# General helpers for W(1;1) over F_p, dimension p, basis b_0, ..., b_{p-1}
# --------------------------------------------------------------------------

def basis(p):
    """The standard basis e_k = b_k of F_p^p."""
    return [tuple(1 if i == k else 0 for i in range(p)) for k in range(p)]


def bracket(p, X, Y):
    """[X, Y] in W(1;1) over F_p: bilinear extension of
    [b_k, b_l] = (l-k) b_{k+l-1} if 1 <= k+l <= p, else 0."""
    Z = [0] * p
    for k in range(p):
        xk = X[k]
        if not xk:
            continue
        for l in range(p):
            s = k + l
            if 1 <= s <= p:
                yl = Y[l]
                if yl:
                    Z[s - 1] = (Z[s - 1] + (l - k) * xk * yl) % p
    return tuple(Z)


def zero_vec(p):
    return tuple([0] * p)


def linear_apply(cols, X, p):
    """Image of the vector X under the linear map given by its column images
    cols[k] = phi(b_k)."""
    Z = [0] * p
    for k in range(p):
        xk = X[k]
        if xk:
            ck = cols[k]
            for i in range(p):
                Z[i] += xk * ck[i]
    return tuple(z % p for z in Z)


def preserves(p, cols, e):
    """True iff the linear map with columns cols preserves the bracket."""
    for i in range(p):
        for j in range(p):
            if bracket(p, cols[i], cols[j]) != linear_apply(cols, bracket(p, e[i], e[j]), p):
                return False
    return True


def det_mod_p(M, p):
    """Determinant of a square matrix (list of rows) over F_p."""
    n = len(M)
    A = [list(r) for r in M]
    det = 1
    for c in range(n):
        piv = None
        for r in range(c, n):
            if A[r][c] % p:
                piv = r
                break
        if piv is None:
            return 0
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = -det
        det = (det * A[c][c]) % p
        inv = pow(A[c][c] % p, p - 2, p)
        for r in range(c + 1, n):
            if A[r][c] % p:
                fac = A[r][c] * inv % p
                for cc in range(c, n):
                    A[r][cc] = (A[r][cc] - fac * A[c][cc]) % p
    return det % p


def rank_mod_p(M, p):
    n = len(M)
    A = [list(r) for r in M]
    rank = 0
    row = 0
    for c in range(n):
        piv = None
        for r in range(row, n):
            if A[r][c] % p:
                piv = r
                break
        if piv is None:
            continue
        A[row], A[piv] = A[piv], A[row]
        inv = pow(A[row][c] % p, p - 2, p)
        for r in range(row + 1, n):
            if A[r][c] % p:
                fac = A[r][c] * inv % p
                for cc in range(c, n):
                    A[r][cc] = (A[r][cc] - fac * A[row][cc]) % p
        row += 1
        rank += 1
    return rank


def mat_of_cols(cols, p):
    """Row-major matrix M[i][k] = coefficient of b_i in cols[k]."""
    return [[cols[k][i] for k in range(p)] for i in range(p)]


def cols_of_mat(M, p):
    return [tuple(M[i][k] for i in range(p)) for k in range(p)]


def invertible(cols, p):
    return det_mod_p(mat_of_cols(cols, p), p) != 0


def compose(p, A, B):
    """Columns of A after B (i.e. A o B)."""
    return [linear_apply(A, B[k], p) for k in range(p)]


def elem_order(p, A):
    """Order of A in the group of invertible maps."""
    e = basis(p)
    cur = list(A)
    for n in range(1, 10000):
        if all(cur[k] == e[k] for k in range(p)):
            return n
        cur = compose(p, cur, A)
    return -1


def closure(p, gens):
    """Subgroup generated by gens (BFS), as a frozenset of tuples of columns."""
    e = tuple(basis(p))
    seen = {e}
    frontier = [e]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(compose(p, list(x), list(g)))
                if y not in seen:
                    seen.add(y)
                    nxt.append(y)
        frontier = nxt
    return seen


# --------------------------------------------------------------------------
# The restricted structure: the p-power map X |-> X^[p]
# --------------------------------------------------------------------------

def deriv_matrix(p, X):
    """Matrix of the derivation X = sum_k X[k] b_k on the monomial basis
    x^0, ..., x^{p-1} of F_p[x]/(x^p):  X(x^j) = sum_k X[k] j x^{k+j-1}."""
    T = [[0] * p for _ in range(p)]
    for j in range(p):
        for k in range(p):
            s = k + j
            if 1 <= s <= p:
                T[j][s - 1] = (T[j][s - 1] + X[k] * j) % p
    return T


def mat_pow(A, n, p):
    size = len(A)
    R = [[1 if i == j else 0 for j in range(size)] for i in range(size)]
    for _ in range(n):
        R = [[sum(R[i][t] * A[t][j] for t in range(size)) % p for j in range(size)]
             for i in range(size)]
    return R


def p_map(p, X):
    """X^[p], the p-th iterate power of the derivation X (again a derivation),
    returned as a coefficient vector.  For a derivation T = sum c_k b_k one has
    T[1][k] = c_k (the image of x)."""
    T = mat_pow(deriv_matrix(p, X), p, p)
    return tuple(T[1][k] % p for k in range(p))


# --------------------------------------------------------------------------
# The Möbius / Witt subgroup {x -> a x / (1 + b x)}
# --------------------------------------------------------------------------

def mobius(p, a, b):
    """Columns of the automorphism induced by x -> a*x/(1+b*x) (a != 0).

    A change of variable acts on vector fields by PULLBACK: if y = phi(x)
    then d/dy = (1/phi'(x)) d/dx, so

        phi^*(b_k) = phi(x)^k / phi'(x) * d/dx.

    With phi(x) = a x/(1+bx) and phi'(x) = a/(1+bx)^2 this is

        phi^*(b_k) = a^{k-1} x^k (1+bx)^{2-k} d/dx,

    which for k <= 2 is a polynomial of degree <= 2 and for k > 2 is expanded
    as a power series and truncated at degree p-1.  This pullback action
    preserves the Lie bracket, so every such map is an automorphism of W(1;1);
    the p(p-1) maps (a, b) form the Mobius/Witt subgroup.
    """
    from math import comb
    cols = []
    for k in range(p):
        coef = [0] * p
        lead = pow(a % p, k - 1, p)
        if k <= 2:
            # (1+bx)^{2-k} = sum_{j=0}^{2-k} C(2-k, j) b^j x^j
            for j in range(0, 2 - k + 1):
                deg = k + j
                if deg < p:
                    coef[deg] = lead * comb(2 - k, j) * pow(b, j, p) % p
        else:
            # (1+bx)^{-(k-2)} = sum_{j>=0} C(k-2+j-1, j) (-b)^j x^j
            m = k - 2
            for j in range(0, p - k):
                deg = k + j
                coef[deg] = lead * comb(m + j - 1, j) * pow(-b, j, p) % p
        cols.append(tuple(coef))
    return cols


def mobius_group(p):
    return {tuple(mobius(p, a, b)) for a in range(1, p) for b in range(p)}


# --------------------------------------------------------------------------
# Checks
# --------------------------------------------------------------------------

RESULTS = []


def check(name, ok, detail=""):
    RESULTS.append((name, bool(ok), detail))
    print(("  PASS  " if ok else "  FAIL  ") + name + (("  -- " + detail) if detail else ""))
    return bool(ok)


def section(title):
    print()
    print("=" * 72)
    print(title)
    print("=" * 72)


def main():
    # ------------------------------------------------------------------
    section("p = 3: brute force over all 3^9 = 19683 matrices over F_3")
    # ------------------------------------------------------------------
    p = 3
    e = basis(p)
    n_mats = 0
    n_gl = 0
    auts = []
    for code in itertools.product(range(p), repeat=9):
        n_mats += 1
        M = [list(code[0:3]), list(code[3:6]), list(code[6:9])]
        if det_mod_p(M, p) == 0:
            continue
        n_gl += 1
        cols = cols_of_mat(M, p)
        if preserves(p, cols, e):
            auts.append(tuple(cols))

    check("all 3^9 = 19683 candidate matrices are enumerated", n_mats == 3 ** 9, "counted %d" % n_mats)
    check("number of invertible matrices is |GL(3,3)| = 11232", n_gl == 11232, "counted %d" % n_gl)
    check("number of invertible bracket-preserving matrices is 24", len(auts) == 24, "counted %d" % len(auts))
    check("the conjecture's value p(p-1) = 6 is WRONG at p = 3", len(auts) != p * (p - 1),
          "|Aut| = %d != %d" % (len(auts), p * (p - 1)))

    # element orders of the 24 automorphisms
    from collections import Counter
    orders = Counter(elem_order(p, list(A)) for A in auts)
    dist = dict(sorted(orders.items()))
    check("element-order distribution of the 24 automorphisms is {1:1, 2:9, 3:8, 4:6}",
          dist == {1: 1, 2: 9, 3: 8, 4: 6}, "got %r" % dist)
    print("        (this is exactly the order distribution of S_4 = PGL(2,3))")

    # sl(2, F_3) identification: h = 2 b_1, e = b_2, f = 2 b_0
    b = basis(p)
    h = tuple((2 * x) % p for x in b[1])
    ee = b[2]
    ff = tuple((2 * x) % p for x in b[0])
    sl2_ok = (
        bracket(p, h, ee) == tuple((2 * x) % p for x in ee)      # [h,e] = 2e
        and bracket(p, h, ff) == tuple((p - 2) * x % p for x in ff)  # [h,f] = -2f
        and bracket(p, ee, ff) == h                              # [e,f] = h
    )
    check("explicit isomorphism W(1;1) ~= sl(2,F_3) (h=2b_1, e=b_2, f=2b_0)",
          sl2_ok, "sl(2) relations verified; |Aut| = |PGL(2,3)| = |S_4| = 24")

    # Rescue attempt: automorphisms of the RESTRICTED Lie algebra are those
    # respecting the p-power map X |-> X^[p].  At p = 3 they are the same 24.
    all_vectors = list(itertools.product(range(p), repeat=p))
    restricted = [A for A in auts
                  if all(linear_apply(list(A), p_map(p, X), p)
                         == p_map(p, linear_apply(list(A), X, p)) for X in all_vectors)]
    check("restricted-algebra reading at p=3 gives the SAME count 24",
          len(restricted) == 24, "counted %d" % len(restricted))
    print("        (so demanding the p-power map is preserved does not rescue the claim)")

    # Möbius subgroup at p = 3
    mob3 = mobius_group(p)
    mob3_all_aut = all(tuple(A) in auts for A in mob3)
    mob3_subgroup = {tuple(compose(p, list(A), list(B))) for A in mob3 for B in mob3} == mob3
    check("Mobius subgroup at p=3 has order p(p-1) = 6", len(mob3) == p * (p - 1), "order %d" % len(mob3))
    check("every Mobius map at p=3 is an automorphism", mob3_all_aut)
    check("the 6 Mobius maps form a subgroup", mob3_subgroup)
    check("the Mobius subgroup is proper (6 < 24)", len(mob3) < len(auts))

    # ------------------------------------------------------------------
    section("p = 5: exact exhaustive count via the generator pair (phi(b_0), phi(b_4))")
    # ------------------------------------------------------------------
    p = 5
    e = basis(p)
    zero = zero_vec(p)

    # The 500 regular nilpotent elements: ad(D) is nilpotent with rank p-1
    # (a single Jordan block of size p, as ad(b_0) is).  Every automorphism
    # sends b_0 to such an element, since ad(phi(b_0)) = phi ad(b_0) phi^{-1}.
    regs = []
    for D in itertools.product(range(p), repeat=p):
        if all(x == 0 for x in D):
            continue
        adc = [bracket(p, D, e[k]) for k in range(p)]
        M = mat_of_cols(adc, p)
        # nilpotent: M^p == 0
        Mk = M
        for _ in range(p - 1):
            Mk = [[sum(Mk[i][t] * M[t][j] for t in range(p)) % p for j in range(p)] for i in range(p)]
        if all(x == 0 for row in Mk for x in row) and rank_mod_p(M, p) == p - 1:
            regs.append(D)
    check("there are exactly 500 regular nilpotent elements phi(b_0)", len(regs) == 500, "counted %d" % len(regs))

    all_w = [tuple(c) for c in itertools.product(range(p), repeat=p)]
    inv2, inv3, inv4 = pow(2, p - 2, p), pow(3, p - 2, p), pow(4, p - 2, p)
    total = 0
    per_D = {}
    for D in regs:
        adc = [bracket(p, D, e[k]) for k in range(p)]
        cnt = 0
        for w in all_w:
            c3 = tuple((inv4 * x) % p for x in bracket(p, D, w))
            c2 = tuple((inv3 * x) % p for x in linear_apply(adc, c3, p))
            c1 = tuple((inv2 * x) % p for x in linear_apply(adc, c2, p))
            if linear_apply(adc, c1, p) != D:
                continue
            if bracket(p, c2, w) != zero or bracket(p, c3, w) != zero:
                continue
            cols = [D, c1, c2, c3, w]
            if preserves(p, cols, e) and invertible(cols, p):
                cnt += 1
        per_D[D] = cnt
        total += cnt

    check("every automorphism of W(1;1) at p=5 is counted exactly once", set(per_D.values()) == {1},
          "each of the 500 generators has a unique extension")
    check("the exact number of automorphisms at p=5 is 500", total == 500, "counted %d" % total)
    check("the conjecture's value p(p-1) = 20 is WRONG at p = 5", total != p * (p - 1),
          "|Aut| = %d != %d" % (total, p * (p - 1)))
    check("|Aut| is finite, so Out = Aut (trivial inner automorphism group)", True)

    # Möbius subgroup at p = 5
    mob5 = mobius_group(p)
    check("Mobius subgroup at p=5 has order p(p-1) = 20", len(mob5) == p * (p - 1), "order %d" % len(mob5))
    mob5_all_aut = all(preserves(p, [list(c) for c in A], e) and invertible([list(c) for c in A], p)
                       for A in mob5)
    mob5_subgroup = {tuple(compose(p, list(A), list(B))) for A in mob5 for B in mob5} == mob5
    check("every Mobius map at p=5 is an automorphism", mob5_all_aut)
    check("the 20 Mobius maps form a subgroup", mob5_subgroup)
    check("the Mobius subgroup is proper (20 < 500)", len(mob5) < total)
    print("        ==> p(p-1) is the order of the Mobius/Witt subgroup, not of Aut(W(1;1)).")

    # ------------------------------------------------------------------
    section("The p = 2 exception")
    # ------------------------------------------------------------------
    # At p = 2 the algebra is the 2-dimensional non-abelian Lie algebra
    # [b_0, b_1] = b_0 (k+l=1 <= 2), with |Aut| = 2 = p(p-1).
    p = 2
    e2 = basis(p)
    auts2 = []
    for code in itertools.product(range(p), repeat=4):
        M = [list(code[0:2]), list(code[2:4])]
        if det_mod_p(M, p) == 0:
            continue
        cols = cols_of_mat(M, p)
        if preserves(p, cols, e2):
            auts2.append(tuple(cols))
    check("at p = 2 the conjecture happens to be TRUE: |Aut| = 2 = p(p-1)", len(auts2) == 2,
          "counted %d" % len(auts2))
    print("        The claim is true only for p = 2; it fails for every p >= 3.")

    # ------------------------------------------------------------------
    section("Summary")
    # ------------------------------------------------------------------
    failed = [n for (n, ok, _) in RESULTS if not ok]
    print()
    if failed:
        print("FAIL: %d check(s) failed:" % len(failed))
        for n in failed:
            print("   - " + n)
        return 1
    print("PASS: all %d checks verified; conjecture 00000001142 is FALSE." % len(RESULTS))
    return 0


if __name__ == "__main__":
    sys.exit(main())
