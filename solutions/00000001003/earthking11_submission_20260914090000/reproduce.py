#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001003.

    Definition: a cap is a point set of PG(n,q) with no three collinear.
    Conjecture: the maximal cap size in PG(4,q) is
                    q^2 + q + 1 + floor((q+1)/3)        for all odd q,
                attained by an elliptic quadric with an explicit three-point
                augmentation; for even q the value increases by 2.

The conjecture is FALSE.  The smallest odd prime power already fails:

    q = 3:  the formula predicts  9 + 3 + 1 + floor(4/3) = 14,
            but PG(4,3) contains an explicit 20-point cap (no three collinear),
            and in fact the true maximum is 20 (upper bound: SAT certificate,
            classical table M_2(5,3) = 20).

Other failures, all checked below:

  * q = 5: the formula predicts 25 + 5 + 1 + 2 = 33, but PG(4,5) contains an
           explicit 47-point cap.
  * q = 2 (even): the formula plus 2 gives 4 + 2 + 1 + 1 + 2 = 10, whereas
           PG(4,2) contains a 16-point cap and the true maximum is 16 = 2^4
           (upper bound by SAT, classical M_2(n,2) = 2^n).
  * internal inconsistency: an elliptic quadric in PG(4,q) has q^2 + 1 points,
           and adding 3 gives q^2 + 4, which is not q^2 + q + 1 + floor((q+1)/3).

Standard library only, Python 3.8+.  Exits non-zero if any check fails.

Everything is exact integer arithmetic over F_p; no randomised search is used
(the two explicit caps are hard-coded lists, verified from scratch here).
"""

import itertools

# ---------------------------------------------------------------------------
# Linear algebra over F_q (q prime), points and lines of PG(n,q)
# ---------------------------------------------------------------------------


def normalize(v, q):
    """Projective normalisation: scale so the first nonzero coordinate is 1."""
    for c in v:
        if c % q != 0:
            inv = pow(c % q, -1, q)
            return tuple((x * inv) % q for x in v)
    return None  # the zero vector


def pg_points(n, q):
    """All points of PG(n-1,q): nonzero vectors of F_q^n, normalised."""
    P = set()
    for v in itertools.product(range(q), repeat=n):
        if any(v):
            P.add(normalize(v, q))
    return sorted(P)


def line_through(a, b, q):
    """The projective line through two distinct points a, b (q+1 points)."""
    n = len(a)
    line = {b}
    for lam in range(q):
        w = tuple((a[k] + lam * b[k]) % q for k in range(n))
        if any(w):
            line.add(normalize(w, q))
    return frozenset(line)


def pg_lines(P, q):
    """All lines of PG(n-1,q), as frozensets of q+1 projective points."""
    L = set()
    for i, a in enumerate(P):
        for b in P[i + 1:]:
            L.add(line_through(a, b, q))
    return L


def rank_mod_p(rows, p):
    """Rank of a list of vectors over F_p by Gaussian elimination."""
    M = [list(r) for r in rows]
    cols = len(M[0]) if M else 0
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, len(M)):
            if M[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c] % p, -1, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p:
                f = M[i][c] % p
                M[i] = [(M[i][k] - f * M[r][k]) % p for k in range(cols)]
        r += 1
        if r == len(M):
            break
    return r


def collinear_by_rank(a, b, c, q):
    """Three points are collinear iff the rank of their 3 vectors is <= 2."""
    return rank_mod_p([a, b, c], q) <= 2


# ---------------------------------------------------------------------------
# The explicit caps (all coordinates already normalised: first nonzero = 1)
# ---------------------------------------------------------------------------

CAP20_PG43 = [
    (1, 0, 0, 0, 2), (0, 0, 0, 1, 2), (1, 2, 2, 1, 1), (0, 1, 0, 0, 0),
    (1, 0, 2, 1, 2), (1, 0, 1, 2, 0), (0, 1, 0, 1, 0), (1, 2, 1, 2, 1),
    (1, 1, 2, 2, 0), (1, 2, 0, 1, 2), (1, 2, 0, 1, 0), (1, 2, 1, 0, 2),
    (1, 0, 1, 1, 0), (0, 1, 1, 1, 2), (0, 0, 1, 0, 0), (0, 1, 2, 2, 0),
    (1, 0, 2, 2, 2), (1, 2, 1, 2, 2), (0, 1, 2, 2, 2), (1, 1, 0, 1, 1),
]

CAP47_PG45 = [
    (0, 1, 1, 1, 0), (0, 1, 1, 2, 3), (0, 1, 1, 3, 0), (0, 1, 1, 3, 4),
    (0, 1, 2, 1, 0), (0, 1, 2, 1, 3), (0, 1, 2, 2, 1), (0, 1, 2, 3, 3),
    (0, 1, 3, 2, 3), (0, 1, 4, 0, 1), (0, 1, 4, 1, 2), (1, 0, 0, 0, 4),
    (1, 0, 0, 1, 1), (1, 0, 0, 1, 3), (1, 0, 0, 3, 2), (1, 0, 1, 2, 3),
    (1, 0, 2, 0, 0), (1, 0, 2, 0, 3), (1, 0, 2, 1, 3), (1, 0, 3, 0, 2),
    (1, 0, 3, 4, 1), (1, 0, 4, 1, 1), (1, 1, 0, 0, 0), (1, 1, 2, 2, 2),
    (1, 1, 3, 0, 2), (1, 1, 3, 2, 0), (1, 1, 3, 2, 4), (1, 1, 4, 4, 2),
    (1, 2, 3, 1, 1), (1, 2, 3, 2, 4), (1, 3, 0, 1, 3), (1, 3, 0, 2, 0),
    (1, 3, 0, 2, 3), (1, 3, 0, 3, 1), (1, 3, 1, 0, 1), (1, 3, 1, 2, 0),
    (1, 3, 1, 2, 3), (1, 3, 1, 3, 0), (1, 3, 2, 4, 3), (1, 3, 3, 1, 0),
    (1, 3, 3, 4, 0), (1, 3, 4, 0, 2), (1, 3, 4, 2, 4), (1, 4, 0, 4, 1),
    (1, 4, 3, 1, 0), (1, 4, 4, 2, 3), (1, 4, 4, 4, 2),
]


def formula(q):
    """The conjecture's formula q^2 + q + 1 + floor((q+1)/3)."""
    return q * q + q + 1 + (q + 1) // 3


# ---------------------------------------------------------------------------
# Cap checks
# ---------------------------------------------------------------------------


def is_cap_pairwise(S, q):
    """(ok, witness): exhaustive pairwise line-membership cap test."""
    Sset = set(S)
    for i, a in enumerate(S):
        for b in S[i + 1:]:
            ln = line_through(a, b, q)
            for x in ln:
                if x != a and x != b and x in Sset:
                    return False, (a, b, x)
    return True, None


def all_triples_noncollinear(S, q, P, lines):
    """Check every C(|S|,3) triple two independent ways.

    Returns (ok_line, bad_line, ok_rank, bad_rank, n_triples).
      * line membership: the triple lies on one of the precomputed lines of
        PG(n-1,q);
      * rank over F_q: the three vectors are collinear iff rank <= 2.
    """
    Sset = set(S)
    line_triples = set()
    for ln in lines:
        for t in itertools.combinations(sorted(ln), 3):
            line_triples.add(t)
    bad_line = []
    bad_rank = []
    n = 0
    for t in itertools.combinations(S, 3):
        n += 1
        if tuple(sorted(t)) in line_triples:
            bad_line.append(t)
        if collinear_by_rank(t[0], t[1], t[2], q):
            bad_rank.append(t)
    return (not bad_line, bad_line, not bad_rank, bad_rank, n)


def is_inclusion_maximal(S, P, q):
    """Is S inclusion-maximal, i.e. no point of P can be added to S?"""
    Sset = set(S)
    addable = []
    for p in P:
        if p in Sset:
            continue
        ok = True
        for s in S:
            ln = line_through(s, p, q)
            if any((x in Sset) for x in ln if x != s and x != p):
                ok = False
                break
        if ok:
            addable.append(p)
    return (not addable), addable


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main():
    checks = []
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    line = "=" * 76
    print(line)
    print("Disproof of conjecture 00000001003 -- reproduction")
    print(line)
    print("\nDefinition: a cap is a point set of PG(n,q) with no three collinear.")
    print("Conjecture: max cap in PG(4,q) = q^2+q+1+floor((q+1)/3) (q odd),")
    print("            +2 for even q, attained by an augmented elliptic quadric.")
    print("Verdict: FALSE.")

    # -----------------------------------------------------------------
    # 1. Build PG(4,3): 121 points, 1210 lines
    # -----------------------------------------------------------------
    P3 = pg_points(5, 3)
    lines3 = pg_lines(P3, 3)
    print("\n[1] Geometry of PG(4,3)")
    print(f"    points = {len(P3)}   lines = {len(lines3)}")
    check("PG(4,3) has exactly 121 points", len(P3) == 121, f"got {len(P3)}")
    check("PG(4,3) has exactly 1210 lines", len(lines3) == 1210, f"got {len(lines3)}")
    check("all points are distinct normalised projective points "
          "(first nonzero coordinate = 1)",
          len(set(P3)) == len(P3)
          and all(next(x for x in p if x != 0) == 1 for p in P3),
          "121 distinct, all normalised")

    # -----------------------------------------------------------------
    # 2. The explicit 20-point cap
    # -----------------------------------------------------------------
    S20 = [tuple(p) for p in CAP20_PG43]
    print("\n[2] The explicit 20-point cap in PG(4,3)")
    n_before = len(checks)
    check("the 20 listed points are pairwise distinct", len(set(S20)) == len(S20),
          f"|set| = {len(set(S20))}")
    check("the 20 listed points are normalised (first nonzero coordinate = 1)",
          all(next(x for x in p if x != 0) == 1 for p in S20), "all normalised")
    check("the 20 listed points all lie in PG(4,3)",
          all(p in set(P3) for p in S20), "all 20 are points of PG(4,3)")

    ok_l, bad_l, ok_r, bad_r, ntri = all_triples_noncollinear(S20, 3, P3, lines3)
    print(f"    C(20,3) = {ntri} triples checked")
    check(f"no collinear triple among the 20 points, by line membership "
          f"({ntri} triples)", ok_l and ntri == 1140,
          f"collinear triples = {len(bad_l)}; triples checked = {ntri}")
    check(f"no collinear triple among the 20 points, by rank over F_3 "
          f"({ntri} triples)", ok_r,
          f"collinear triples = {len(bad_r)}")

    ok_pair, wit = is_cap_pairwise(S20, 3)
    check("pairwise line-membership cap test on the 20 points", ok_pair,
          "valid cap" if ok_pair else f"witness {wit}")

    # Non-vacuity: the collinearity test does detect a real collinear triple.
    col_triple = [(1, 0, 0, 0, 0), (0, 1, 0, 0, 0), (1, 1, 0, 0, 0)]
    check("sanity: the test detects the collinear triple "
          "(1,0,0,0,0),(0,1,0,0,0),(1,1,0,0,0)",
          not is_cap_pairwise(col_triple, 3)[0]
          and collinear_by_rank(*col_triple, 3),
          "correctly rejected")
    inde_triple = [(1, 0, 0, 0, 0), (0, 1, 0, 0, 0), (1, 0, 1, 0, 0)]
    check("sanity: the test accepts the non-collinear triple "
          "(1,0,0,0,0),(0,1,0,0,0),(1,0,1,0,0)",
          is_cap_pairwise(inde_triple, 3)[0]
          and not collinear_by_rank(*inde_triple, 3),
          "correctly accepted")

    # -----------------------------------------------------------------
    # 3. The refutation 20 > 14 and inclusion-maximality
    # -----------------------------------------------------------------
    print("\n[3] Refutation at q = 3")
    print(f"    conjecture value: formula(3) = {formula(3)}")
    print(f"    explicit cap size: {len(S20)}")
    check("the conjecture's formula at q = 3 is 14", formula(3) == 14,
          f"formula(3) = {formula(3)}")
    check("20 > 14, so the explicit cap refutes the q = 3 value",
          len(S20) > formula(3) and len(S20) == 20 and formula(3) == 14,
          f"{len(S20)} > {formula(3)}")

    incl, addable = is_inclusion_maximal(S20, P3, 3)
    check("the 20-cap is inclusion-maximal (no point of PG(4,3) can be added)",
          incl, f"addable points = {len(addable)}")
    print("    (This addresses the reading 'maximal = inclusion-maximal':")
    print("     the witness is already inclusion-maximal, so that reading does")
    print("     not rescue the value 14 either.)")

    # -----------------------------------------------------------------
    # 4. General-formula failure at q = 5
    # -----------------------------------------------------------------
    print("\n[4] General-formula failure at q = 5")
    P5 = pg_points(5, 5)
    S47 = [tuple(p) for p in CAP47_PG45]
    ok_l5, bad_l5, ok_r5, bad_r5, ntri5 = all_triples_noncollinear(
        S47, 5, P5, [])
    ok_pair5, wit5 = is_cap_pairwise(S47, 5)
    print(f"    PG(4,5) points = {len(P5)};  explicit cap size = {len(S47)};  "
          f"formula(5) = {formula(5)}")
    print(f"    C(47,3) = {ntri5} triples checked by rank")
    check("the 47 listed points are distinct normalised points of PG(4,5)",
          len(set(S47)) == 47
          and all(next(x for x in p if x != 0) == 1 for p in S47)
          and all(p in set(P5) for p in S47),
          "47 distinct, normalised, in PG(4,5)")
    check("no collinear triple among the 47 points of PG(4,5) "
          "(pairwise line membership)", ok_pair5,
          "valid cap" if ok_pair5 else f"witness {wit5}")
    check("no collinear triple among the 47 points of PG(4,5) "
          "(rank over F_5)", ok_r5 and len(bad_r5) == 0,
          f"collinear triples = {len(bad_r5)}")
    check("47 > 33 = formula(5), so the general odd-q formula fails",
          len(S47) > formula(5), f"{len(S47)} > {formula(5)}")

    # -----------------------------------------------------------------
    # 5. Even-q clause fails at q = 2
    # -----------------------------------------------------------------
    print("\n[5] Even-q clause fails at q = 2")
    P2 = pg_points(5, 2)
    S16 = [tuple((1,) + v) for v in itertools.product(range(2), repeat=4)]
    ok_l2, bad_l2, ok_r2, bad_r2, ntri2 = all_triples_noncollinear(
        S16, 2, P2, [])
    ok_pair2, wit2 = is_cap_pairwise(S16, 2)
    print(f"    PG(4,2) points = {len(P2)};  explicit cap size = {len(S16)};  "
          f"formula(2)+2 = {formula(2) + 2}")
    check("the 16 points (1,v), v in F_2^4, are a cap in PG(4,2)",
          ok_pair2 and ok_r2 and len(S16) == 16,
          "valid 16-point cap (line membership and rank agree)")
    check("16 > 10 = formula(2)+2, so the even-q clause fails at q = 2",
          len(S16) > formula(2) + 2, f"{len(S16)} > {formula(2) + 2}")

    # -----------------------------------------------------------------
    # 6. Internal inconsistency of the statement
    # -----------------------------------------------------------------
    print("\n[6] Internal inconsistency: elliptic quadric + 3 vs the formula")
    print("    An elliptic quadric in PG(4,q) has q^2+1 points; adding 3 gives")
    print("    q^2+4, which is not q^2+q+1+floor((q+1)/3).")
    incons = {}
    for q in [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23]:
        quad_plus_3 = q * q + 4
        stated = formula(q)
        incons[q] = (quad_plus_3, stated)
    print(f"    q = 3:  q^2+4 = {incons[3][0]}  but  formula(3) = {incons[3][1]}")
    print(f"    q = 5:  q^2+4 = {incons[5][0]}  but  formula(5) = {incons[5][1]}")
    check("the stated formula differs from the quadric description for every "
          "odd q in 3..23 (in particular q = 3: 13 vs 14)",
          all(a != b for (a, b) in incons.values())
          and incons[3] == (13, 14),
          f"q=3: {incons[3]}, q=5: {incons[5]}")

    # -----------------------------------------------------------------
    # 7. Cited bounds (not checked here; reported honestly)
    # -----------------------------------------------------------------
    print("\n[7] Exactness of the values (cited, not checked by this script)")
    print("    max cap in PG(4,3) is exactly 20, and max cap in PG(4,2) is")
    print("    exactly 16 = 2^4.  The lower bounds are the explicit caps above.")
    print("    The upper bounds rest on SAT certificates: a cap of >= 21 in")
    print("    PG(4,3) spans PG(4,3) and contains 5 independent points; GL(5,3)")
    print("    is transitive on ordered bases, so WLOG the 5 standard basis")
    print("    points lie in the cap and the SAT instance is UNSAT.  The")
    print("    refutation of the conjecture needs only the lower bounds.")

    # -----------------------------------------------------------------
    # Report
    # -----------------------------------------------------------------
    print("\n" + line)
    print("Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"  [{mark}] {name}")
        print(f"         {detail}")
    print(line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000001003 is FALSE.")
        print("  A 20-point cap in PG(4,3) beats the predicted 14; a 47-point")
        print("  cap in PG(4,5) beats the predicted 33; a 16-point cap in")
        print("  PG(4,2) beats the predicted 10; and the quadric description is")
        print("  inconsistent with the stated formula.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
