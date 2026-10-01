#!/usr/bin/env python3
"""Independent recomputation for the disproof of TLMC conjecture 00000000556.

Conjecture 00000000556: HH^1(Lambda) = 0  iff  Lambda is representation-finite
and rigid.

Attack (F-queue): Lambda = k[x]/(x^2), the dual numbers.
  * representation-finite: modules over k[x]/(x^2) are vector spaces V with a
    nilpotent endomorphism T, T^2 = 0; over an algebraically closed field these
    decompose into Jordan blocks of size <= 2, so the only indecomposables are
    k and Lambda  (2 of them).
  * rigid (self-injective): the linear form lam(a + b x) = b has bilinear form
    B(u, v) = lam(u*v) with matrix [[0, 1], [1, 0]], det = -1 != 0 in any
    characteristic, so Lambda is Frobenius, hence self-injective.
    (Also Ext^1(Lambda, Lambda) = 0 trivially, since Lambda is projective over
    itself.)
  * HH^1 != 0: a derivation is determined by d(1) = 0 and d(x) = v with
    2 x v = 0; inner derivations vanish (Lambda commutative), and
    d = x*partial (d(x) = x) is therefore non-inner. Concretely
    HH^1 = Der/Inn ≅ k when char k != 2 and ≅ k^2 when char k = 2.

This script recomputes all of it by exact linear algebra over Q, F2 and F3.
"""

from fractions import Fraction

BASIS = [(1, 0), (0, 1)]  # e0 = 1, e1 = x


# ---------- field-generic helpers (p = None means Q) ----------
def sca(p, c, u):
    r = (c * u[0], c * u[1])
    return r if p is None else (r[0] % p, r[1] % p)


def addv(p, u, v):
    r = (u[0] + v[0], u[1] + v[1])
    return r if p is None else (r[0] % p, r[1] % p)


def mulk(p, u, v):
    a, b = u
    c, d = v
    r = (a * c, a * d + b * c)  # (a + b x)(c + d x) = ac + (ad + bc) x, x^2 = 0
    return r if p is None else (r[0] % p, r[1] % p)


def apply_D(p, m, u):
    """Apply the linear map given by matrix entries m = (m00, m01, m10, m11):
    columns D(e0) = (m00, m10), D(e1) = (m01, m11)."""
    return addv(p, sca(p, u[0], (m[0], m[2])), sca(p, u[1], (m[1], m[3])))


def constraints(p, m):
    """Constraint vectors that must vanish for D (given by m) to be a derivation:
    D(1) = 0 and the Leibniz rule on all basis pairs."""
    out = [apply_D(p, m, (1, 0))]
    for u in BASIS:
        for v in BASIS:
            uv = mulk(p, u, v)
            lhs = apply_D(p, m, uv)
            rhs = addv(p, mulk(p, u, apply_D(p, m, v)), mulk(p, apply_D(p, m, u), v))
            out.append(addv(p, lhs, sca(p, -1 if p is None else p - 1, rhs)))
    return out


def solve_homog_dim(A, p, nvars=4):
    A = [list(Fraction(x) if p is None else x % p for x in r) for r in A]
    piv, r, m = [], 0, len(A)
    for c in range(nvars):
        pr = next((i for i in range(r, m)
                   if (p is None and A[i][c] != 0) or (p is not None and A[i][c] % p != 0)),
                  None)
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        v = A[r][c]
        inv = Fraction(1, 1) / v if p is None else pow(v, p - 2, p)
        A[r] = [x * inv if p is None else (x * inv) % p for x in A[r]]
        for i in range(m):
            if i != r:
                f = A[i][c]
                if (p is None and f != 0) or (p is not None and f % p != 0):
                    A[i] = [a - f * b if p is None else (a - f * b) % p
                            for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    return nvars - len(piv)


def rank_vecs(p, vecs):
    vs = [sca(p, 1, v) for v in vecs if sca(p, 1, v) != (0, 0)]
    if not vs:
        return 0
    r, a = 0, None
    for v in vs:
        if r == 0:
            a, r = v, 1
        else:
            det = a[0] * v[1] - a[1] * v[0]
            if (p is None and det != 0) or (p is not None and det % p != 0):
                r = 2
    return r


E = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]


def hh1(p):
    """dim Der, dim Inn for Lambda = k[x]/(x^2) over k (p = None for Q)."""
    C0 = constraints(p, (0, 0, 0, 0))
    rows = []
    for c in range(len(C0)):
        for comp in (0, 1):
            rows.append([constraints(p, E[j])[c][comp] - C0[c][comp] for j in range(4)])
    rows = [r for r in rows if any(x != 0 for x in r)]
    d_der = solve_homog_dim(rows, p)
    imgs = []
    for u in BASIS:
        for v in BASIS:
            a, b = mulk(p, u, v), mulk(p, v, u)
            imgs.append(addv(p, a, sca(p, -1 if p is None else p - 1, b)))
    d_inn = rank_vecs(p, imgs)
    return d_der, d_inn


def main():
    print("Lambda = k[x]/(x^2)  (dual numbers); basis 1, x with x^2 = 0\n")

    ok = True
    for p in (None, 2, 3):
        name = "Q" if p is None else f"F{p}"
        d_der, d_inn = hh1(p)
        hh1_dim = d_der - d_inn

        # Frobenius (self-injective / rigid) check: lam(a + bx) = b
        B = [[mulk(p, u, v)[1] for v in BASIS] for u in BASIS]
        det = B[0][0] * B[1][1] - B[0][1] * B[1][0]
        frob = (det != 0) if p is None else (det % p != 0)

        # the attacking derivation d(1) = 0, d(x) = x  (d = x*partial)
        mstar = (0, 0, 0, 1)
        is_der = all(all(x == 0 for x in c) for c in constraints(p, mstar))

        expect_der = 1 if p in (None, 3) else 2  # char 2: D(x) arbitrary (dim 2)
        line_ok = (hh1_dim == expect_der and d_inn == 0 and frob and is_der)
        ok = ok and line_ok
        print(f"[{name}] dim Der = {d_der}, dim Inn = {d_inn}, dim HH^1 = {hh1_dim}")
        print(f"[{name}] Frobenius form [[0,1],[1,0]], det = {det if p is None else det % p}"
              f" -> self-injective (rigid): {frob}")
        print(f"[{name}] d(x) = x is a derivation: {is_der}; non-inner since Inn = 0\n")

    print("Representation-finite: modules are (V, T), T^2 = 0; Jordan blocks of size")
    print("<= 2 over alg. closed k, so indecomposables are exactly {k, Lambda}.")
    print()
    print("Boundary notes:")
    print(" * char k != 2: HH^1 ~= k (dim 1).  char k = 2: HH^1 ~= k^2 (dim 2).")
    print("   Either way HH^1 != 0, so the attack works over every field (and over Z).")
    print(" * 'rigid' as self-injective (the verdict reading): holds (Frobenius).")
    print(" * If 'rigid' meant deformation-rigid (HH^2 = 0): the 2-periodic bimodule")
    print("   resolution gives HH^2 ~= Lambda/(x) ~= k != 0, so Lambda would NOT be")
    print("   rigid and this attack would not apply under that reading.")
    print(" * If 'rigid' meant 'all indecomposables rigid': Ext^1(k, k) ~= k != 0 via")
    print("   the nonsplit 0 -> (x) -> Lambda -> k -> 0; attack would not apply.")
    print()
    print("VERDICT:", "CONFIRMED (HH^1 != 0 while representation-finite and rigid;"
          " the iff fails in the '<=' direction)" if ok else "FAILED CHECKS")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
