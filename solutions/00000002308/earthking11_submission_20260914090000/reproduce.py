#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000002308.

    Definition: A complete group satisfies G = Aut(G).
    Conjecture: The order of the smallest nontrivial solvable complete group is
                2^{11}*3 (an explicit discovery); its structure is a minimal
                example of a semidirect product of a 2-group.

The conjecture is FALSE.  Under the standard meaning of "complete" (trivial
center and every automorphism inner, equivalently G = Aut(G) via conjugation):

  * S_3, of order 6, is complete:  Z(S_3) = {e} and |Aut(S_3)| = |Inn(S_3)| = 6,
    the latter computed here by filtering all 720 bijections S_3 -> S_3;
  * S_3 is solvable:  A_3 is normal of index 2 with abelian factors Z/3 and
    Z/2, and S_3 = C_3 : C_2 is a semidirect product;
  * every group of order 2, 3, 4 or 5 is abelian (checked exhaustively), hence
    has center equal to the whole group and cannot be complete;
  * therefore 6 is the least order of a non-trivial solvable complete group,
    and 6 < 2^{11}*3 = 6144.

Standard library only, Python 3.8+.  Prints PASS/FAIL and exits non-zero if any
check fails.
"""

from itertools import permutations


# ----------------------------------------------------------------------
# S_3 as permutations of {0, 1, 2}
# ----------------------------------------------------------------------

ELEMENTS = list(permutations(range(3)))          # the 6 elements of S_3
N = 6


def compose(a, b):
    """Product a*b of two permutations (a after b)."""
    return tuple(a[b[i]] for i in range(3))


def inverse(a):
    """Inverse permutation."""
    r = [0, 0, 0]
    for i in range(3):
        r[a[i]] = i
    return tuple(r)


INDEX = {p: i for i, p in enumerate(ELEMENTS)}

# Multiplication table and inverse table on indices 0..5.
T = [[INDEX[compose(a, b)] for b in ELEMENTS] for a in ELEMENTS]
INV = [INDEX[inverse(a)] for a in ELEMENTS]

# Handy aliases: 0 = id, 1 = (12), 2 = (01), 3 = (012), 4 = (021), 5 = (02)
IDENT = 0
TAU = 2      # transposition (01)
SIGMA = 3    # 3-cycle (012)


def mul(i, j):
    return T[i][j]


def is_bijection(p):
    """p is a tuple of length 6; true iff it is a permutation of range(6)."""
    return sorted(p) == list(range(N))


def is_hom_tuple(p):
    """p : index -> index with p[i] the image of element i; respects products."""
    return all(T[p[i]][p[j]] == p[T[i][j]] for i in range(N) for j in range(N))


def is_aut_tuple(p):
    return is_bijection(p) and is_hom_tuple(p)


# ----------------------------------------------------------------------
# Exhaustive group check for small orders, via reduced Latin squares
# ----------------------------------------------------------------------

def reduced_latin_squares(n):
    """All reduced Latin squares of order n (first row and column = 0..n-1).

    Every finite group of order n, after relabelling its elements so that the
    identity is 0 and the remaining elements are ordered arbitrarily, has a
    multiplication table that is a reduced Latin square.  So checking all
    reduced Latin squares checks all groups of order n.
    """
    grid = [[None] * n for _ in range(n)]
    for i in range(n):
        grid[0][i] = i
        grid[i][0] = i
    cells = [(i, j) for i in range(1, n) for j in range(1, n)]
    out = []

    def bt(k):
        if k == len(cells):
            out.append([row[:] for row in grid])
            return
        i, j = cells[k]
        row = grid[i]
        used_col = {grid[r][j] for r in range(i)}
        for v in range(n):
            if v in row or v in used_col:
                continue
            row[j] = v
            bt(k + 1)
            row[j] = None

    bt(0)
    return out


def is_associative(t, n):
    """Check (a*b)*c = a*(b*c) for all triples (t is an n x n table)."""
    for a in range(n):
        for b in range(n):
            ab = t[a][b]
            for c in range(n):
                if t[ab][c] != t[a][t[b][c]]:
                    return False
    return True


def is_abelian_table(t, n):
    return all(t[a][b] == t[b][a] for a in range(n) for b in range(n))


# ----------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------

def main():
    checks = []
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    # ------------------------------------------------------------------
    # 0. S_3 is a group (associativity, identity, inverses)
    # ------------------------------------------------------------------
    assoc = all(mul(mul(i, j), k) == mul(i, mul(j, k))
                for i in range(N) for j in range(N) for k in range(N))
    check("S_3 is associative on the 6 elements",
          assoc, "all 216 triples satisfy (ab)c = a(bc)")

    id_ok = all(mul(IDENT, i) == i and mul(i, IDENT) == i for i in range(N))
    inv_ok = all(mul(i, INV[i]) == IDENT and mul(INV[i], i) == IDENT
                 for i in range(N))
    check("identity 0 and inverse table are correct",
          id_ok and inv_ok,
          "0 is a two-sided identity; every element has a two-sided inverse")

    # ------------------------------------------------------------------
    # 1. Center of S_3 is trivial
    # ------------------------------------------------------------------
    center = [z for z in range(N) if all(mul(z, a) == mul(a, z) for a in range(N))]
    check("center Z(S_3) = {identity}",
          center == [IDENT],
          f"central element indices = {center} -> permutation {ELEMENTS[IDENT]}")

    # ------------------------------------------------------------------
    # 2. Exhaustive |Aut(S_3)| over all 720 bijections S_3 -> S_3
    # ------------------------------------------------------------------
    bijs = [p for p in permutations(range(N))]
    check("there are exactly 720 = 6! bijections S_3 -> S_3",
          len(bijs) == 720, f"enumerated {len(bijs)} bijections")

    auts = [p for p in bijs if is_aut_tuple(p)]
    aut_set = set(auts)
    check("|Aut(S_3)| = 6 (filtering all 720 bijections by the homomorphism property)",
          len(auts) == 6,
          f"bijective homomorphisms found: {len(auts)}")

    # ------------------------------------------------------------------
    # 3. Inner automorphisms and Aut = Inn
    # ------------------------------------------------------------------
    inn = []
    for g in range(N):
        conj = tuple(mul(mul(g, x), INV[g]) for x in range(N))
        inn.append(conj)
    inn_set = set(inn)

    check("|Inn(S_3)| = 6 (the six conjugations are pairwise distinct)",
          len(inn_set) == 6,
          f"distinct conjugations: {len(inn_set)}")

    check("Inn(S_3) is a subset of Aut(S_3)",
          inn_set <= aut_set,
          "every conjugation g x g^-1 is a bijective homomorphism")

    check("Aut(S_3) = Inn(S_3) (every automorphism is inner)",
          aut_set == inn_set,
          f"|Aut| = {len(aut_set)}, |Inn| = {len(inn_set)}, equal as sets: "
          f"{aut_set == inn_set}")

    check("S_3 is COMPLETE: Z(S_3) = 1 and Aut(S_3) = Inn(S_3)",
          center == [IDENT] and aut_set == inn_set,
          "trivial center and all automorphisms inner")

    # Cross-check with the generator-based reduction used in the Lean proof.
    def mk_hom(u, v):
        # words: 1, tau*sigma, tau, sigma, sigma^2, tau*sigma^2
        return (IDENT, mul(u, v), u, v, mul(v, v), mul(u, mul(v, v)))

    gen_pairs = [(u, v) for u in range(N) for v in range(N)]
    gen_auts = [(u, v) for (u, v) in gen_pairs
                if is_aut_tuple(mk_hom(u, v))]
    check("generator-based reduction over the 36 pairs (f(tau), f(sigma)) "
          "also yields |Aut| = 6",
          len(gen_auts) == 6,
          f"automorphism inducing pairs: {gen_auts}")

    # Closure of {tau, sigma} is all of S_3.
    closure = {IDENT}
    frontier = [IDENT]
    while frontier:
        x = frontier.pop()
        for g in (TAU, SIGMA):
            for y in (mul(x, g), mul(g, x)):
                if y not in closure:
                    closure.add(y)
                    frontier.append(y)
    check("{tau, sigma} generates S_3 (closure has all 6 elements)",
          closure == set(range(N)),
          f"closure = {sorted(closure)}; tau = {ELEMENTS[TAU]}, "
          f"sigma = {ELEMENTS[SIGMA]}")

    # ------------------------------------------------------------------
    # 4. Solvability of S_3
    # ------------------------------------------------------------------
    A3 = sorted({IDENT, SIGMA, mul(SIGMA, SIGMA)})           # {0, 3, 4}
    check("A_3 is the abelian normal subgroup of index 2",
          len(A3) == 3 and 6 % len(A3) == 0 and 6 // len(A3) == 2,
          f"A_3 = {A3}, |A_3| = {len(A3)}, |S_3|/|A_3| = {6 // len(A3)}")

    a3_closed = all(mul(a, b) in A3 for a in A3 for b in A3)
    a3_abelian = all(mul(a, b) == mul(b, a) for a in A3 for b in A3)
    check("A_3 is abelian (isomorphic to Z/3)",
          a3_closed and a3_abelian,
          "A_3 is closed under multiplication and commutative")

    a3_normal = all(mul(mul(g, a), INV[g]) in A3
                    for g in range(N) for a in A3)
    check("A_3 is normal in S_3",
          a3_normal,
          "g a g^-1 is in A_3 for every g in S_3 and a in A_3")

    quotient_abelian = (6 // len(A3)) == 2   # S_3/A_3 has order 2
    check("S_3 is solvable: 1 < A_3 < S_3 with abelian factors "
          "A_3 = Z/3 and S_3/A_3 = Z/2",
          a3_normal and a3_abelian and quotient_abelian,
          "derived series S_3 |> A_3 |> 1 has abelian factors")

    # ------------------------------------------------------------------
    # 5. S_3 = C_3 : C_2 (semidirect product)
    # ------------------------------------------------------------------
    T2 = sorted({IDENT, TAU})
    t2_closed = all(mul(a, b) in T2 for a in T2 for b in T2)
    t2_order2 = mul(TAU, TAU) == IDENT and TAU != IDENT
    check("T2 = {1, tau} is a subgroup of order 2 (a 2-group C_2)",
          t2_closed and t2_order2 and len(T2) == 2,
          f"T2 = {T2}, tau^2 = 1; |T2| = 2 = 2^1")

    inter = sorted(set(A3) & set(T2))
    check("A_3 and T2 intersect trivially",
          inter == [IDENT], f"A_3 & T2 = {inter}")

    products = sorted({mul(a, t) for a in A3 for t in T2})
    check("A_3 * T2 = S_3 (every element is a*t)",
          products == list(range(N)),
          f"products = {products}")

    action_nontrivial = any(mul(mul(TAU, a), INV[TAU]) != a for a in A3)
    check("T2 acts on A_3 by conjugation with non-trivial action "
          "(so the product is a non-trivial semidirect product)",
          action_nontrivial,
          "some a in A_3 satisfies tau a tau^-1 != a; "
          "hence S_3 = C_3 : C_2 is not the direct product C_6")

    check("S_3 is a semidirect product of a 2-group: S_3 = C_3 : C_2 "
          "with normal C_3 and complement C_2",
          a3_normal and t2_closed and inter == [IDENT]
          and products == list(range(N)),
          "matches the conjecture's structural description, at order 6")

    # ------------------------------------------------------------------
    # 6. Every group of order 2, 3, 4, 5 is abelian (exhaustive)
    # ------------------------------------------------------------------
    for n in (2, 3, 4, 5):
        ls = reduced_latin_squares(n)
        groups = [t for t in ls if is_associative(t, n)]
        nonabelian = [t for t in groups if not is_abelian_table(t, n)]
        check(f"every group of order {n} is abelian "
              f"(exhaustive over all {len(ls)} reduced Latin squares)",
              len(groups) > 0 and not nonabelian,
              f"{len(groups)} group table(s) found, {len(nonabelian)} non-abelian")

    # Consequently no group of order 2, 3, 4, 5 is complete.
    check("no group of order 2, 3, 4 or 5 is complete (each is abelian, so its "
          "center is the whole group and is non-trivial)",
          True,
          "complete requires a trivial center; abelian groups of order > 1 "
          "have Z(G) = G ≠ 1")

    # ------------------------------------------------------------------
    # 7. The order comparison against the claimed 2^{11}*3
    # ------------------------------------------------------------------
    claimed = 2 ** 11 * 3
    check("the claimed order is 2^11 * 3 = 6144",
          claimed == 6144, f"2^11 * 3 = {claimed}")

    check("6 < 6144, so the claimed smallest order is wrong",
          6 < claimed,
          f"the witness S_3 has order 6, and 6 < {claimed}")

    check("minimality: orders 2, 3, 4, 5 are excluded (all groups abelian), "
          "and 6 is attained by the solvable complete group S_3, so the least "
          "non-trivial solvable complete order is 6, not 2^11*3",
          True,
          "6 < 6144 contradicts the conjecture as filed")

    # ------------------------------------------------------------------
    # Report
    # ------------------------------------------------------------------
    line = "=" * 76
    print(line)
    print("Disproof of conjecture 00000002308 -- reproduction")
    print(line)
    print("\nDefinition: a complete group satisfies G = Aut(G) (trivial center")
    print("            and every automorphism is inner).")
    print("Conjecture: the smallest nontrivial solvable complete group has")
    print("            order 2^11*3 = 6144.")
    print("Verdict:    FALSE.")

    print("\n[1] The model S_3 (permutations of {0,1,2}):")
    for i, p in enumerate(ELEMENTS):
        print(f"      index {i}: {p}" +
              ("   <- identity" if i == IDENT else
               "   <- transposition tau" if i == TAU else
               "   <- 3-cycle sigma" if i == SIGMA else ""))

    print("\n[2] S_3 is complete:")
    print(f"      center            Z(S_3)      = {[ELEMENTS[z] for z in center]}")
    print(f"      inner automorphisms |Inn(S_3)| = {len(inn_set)}")
    print(f"      automorphisms       |Aut(S_3)| = {len(aut_set)}  "
          f"(from all {len(bijs)} bijections)")
    print(f"      Aut(S_3) = Inn(S_3): {aut_set == inn_set}")
    print(f"      generator-based check |Aut| = {len(gen_auts)} from the "
          f"36 pairs (f(tau), f(sigma))")

    print("\n[3] S_3 is solvable and a semidirect product:")
    print(f"      A_3 = {A3} (abelian, normal, index {6 // len(A3)}), "
          f"T2 = {T2} (order 2)")
    print(f"      A_3 * T2 = S_3: {products == list(range(N))},  "
          f"A_3 & T2 = {inter}")
    print("      S_3 = C_3 : C_2, a semidirect product of the 2-group C_2.")

    print("\n[4] Small orders 2, 3, 4, 5 (exhaustive reduced Latin squares):")
    for n in (2, 3, 4, 5):
        ls = reduced_latin_squares(n)
        groups = [t for t in ls if is_associative(t, n)]
        nonab = [t for t in groups if not is_abelian_table(t, n)]
        print(f"      order {n}: {len(ls):>3} Latin square(s), "
              f"{len(groups):>2} group table(s), {len(nonab)} non-abelian")
    print("      All are abelian, hence not complete (center = whole group).")

    print("\n[5] Order comparison:")
    print(f"      6 < 2^11 * 3 = {claimed}.  The least order of a non-trivial")
    print("      solvable complete group is 6 (witness S_3), not 6144.")

    print("\n[6] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"      [{mark}] {name}")
        print(f"             {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000002308 is FALSE.")
        print("  S_3 (order 6) is solvable and complete; 6 < 6144, and every")
        print("  group of order 2, 3, 4, 5 is abelian, hence not complete.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
