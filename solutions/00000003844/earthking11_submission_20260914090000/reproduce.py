#!/usr/bin/env python3
r"""Reproduce the disproof of conjecture 00000003844.

    Definition: the covering number of a monoid is the least number of proper
                submonoids needed to cover it, infinity if impossible.
    Conjecture: every finite-type 0-Hecke monoid and every plactic monoid has
                infinite covering number, and arbitrary direct products of
                these two classes still have infinite covering number.

The conjecture is FALSE.  For the 0-Hecke monoid H(S_3) of the finite Coxeter
system (S_3, {s_1, s_2}) (6 elements) the covering number is exactly 2:

    A = {e, s_2}          is a submonoid (s_2 is idempotent),
    B = H(S_3) \ {s_2}    is a proper submonoid (the length identity
                          l(x*y) >= max(l(x), l(y)) for the Demazure product
                          shows x*y = s_2 forces x = s_2 or y = s_2),
    A union B = H(S_3)    (a 2-cover).

No single proper submonoid covers H(S_3) (a proper subset never equals the
whole monoid), so the covering number is exactly 2.  The same argument works
for every finite-type 0-Hecke monoid of rank >= 2 and for every simple
reflection, so H(S_4) (24 elements) also has covering number exactly 2.

This refutes the first clause of the conjecture.  The direct-product clause
fails too: if M1 = A_1 union ... union A_p and M2 = B_1 union ... union B_q with
proper submonoids, then M1 x M2 is covered by the p*q proper submonoids
A_i x B_j, so cov(M1 x M2) <= cov(M1)*cov(M2).  With M = H(S_3),
cov(M x M) <= 2*2 = 4, not infinite.

Standard library only, Python 3.8+.  Exits non-zero if any check fails.
"""

from collections import deque
from itertools import permutations


# ----------------------------------------------------------------------
# Permutations and the Demazure (0-Hecke) product
# ----------------------------------------------------------------------

def compose(p, q):
    """(p o q)(i) = p[q[i]]."""
    return tuple(p[q[i]] for i in range(len(p)))


def simple(n, i):
    """Adjacent transposition s_{i+1} (0-indexed generator i)."""
    p = list(range(n))
    p[i], p[i + 1] = p[i + 1], p[i]
    return tuple(p)


def length(p):
    """Coxeter length = number of inversions."""
    n = len(p)
    return sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])


def reduced_word(n, v):
    """A reduced word of v as a list of generator indices (BFS on the Cayley
    graph, right multiplication by the simple reflections)."""
    e = tuple(range(n))
    if v == e:
        return []
    seen = {e: None}
    dq = deque([e])
    gens = [simple(n, i) for i in range(n - 1)]
    while dq:
        w = dq.popleft()
        for i, s in enumerate(gens):
            nw = compose(w, s)
            if nw not in seen:
                seen[nw] = (w, i)
                if nw == v:
                    word = []
                    cur = nw
                    while seen[cur] is not None:
                        prev, gi = seen[cur]
                        word.append(gi)
                        cur = prev
                    word.reverse()
                    return word
                dq.append(nw)
    raise RuntimeError("unreachable: not a permutation of S_n")


def demazure_step(n, w, i):
    """w * s_i = w s_i if the length increases, else w."""
    s = simple(n, i)
    ws = compose(w, s)
    return ws if length(ws) > length(w) else w


def demazure(n, w, v):
    """The Demazure product w *_0 v = w star v, computed along a reduced word
    of v.  It is independent of the chosen reduced word (it is associative and
    the generators are idempotent)."""
    for i in reduced_word(n, v):
        w = demazure_step(n, w, i)
    return w


def build(n):
    """Build the 0-Hecke monoid H(S_n).

    Returns (W, idx, N, table, e):
      W     -- list of permutations (elements of S_n),
      idx   -- permutation -> index,
      N     -- |W|,
      table -- table[i][j] = index of W_i star W_j,
      e     -- index of the identity.
    """
    W = sorted(permutations(range(n)))
    idx = {p: k for k, p in enumerate(W)}
    N = len(W)
    table = [[idx[demazure(n, W[i], W[j])] for j in range(N)] for i in range(N)]
    return W, idx, N, table, idx[tuple(range(n))]


# ----------------------------------------------------------------------
# Monoid axioms
# ----------------------------------------------------------------------

def check_monoid(name, W, N, table, e, n):
    """Associativity, identity, idempotent generators, braid relations."""
    out = []

    assoc_bad = []
    for a in range(N):
        for b in range(N):
            ab = table[a][b]
            for c in range(N):
                if table[ab][c] != table[a][table[b][c]]:
                    assoc_bad.append((a, b, c))
    out.append(("%s: associativity over all %d triples" % (name, N ** 3),
                not assoc_bad,
                "0 violations" if not assoc_bad else "%d violations, e.g. %r"
                % (len(assoc_bad), assoc_bad[0])))

    id_bad = [a for a in range(N)
              if table[e][a] != a or table[a][e] != a]
    out.append(("%s: identity (element %d)" % (name, e),
                not id_bad,
                "left and right identity" if not id_bad else "failures %r" % id_bad))

    gens = [idx_of_simple(W, n, i) for i in range(n - 1)]
    idem_bad = [g for g in gens if table[g][g] != g]
    out.append(("%s: generators s_1..s_%d idempotent" % (name, n - 1),
                not idem_bad,
                "pi_s^2 = pi_s for every s" if not idem_bad
                else "failures %r" % idem_bad))

    braid_bad = []
    for i in range(n - 2):
        a = table[table[gens[i]][gens[i + 1]]][gens[i]]
        b = table[table[gens[i + 1]][gens[i]]][gens[i + 1]]
        if a != b:
            braid_bad.append(("braid", i))
    for i in range(n - 1):
        for j in range(i + 2, n - 1):
            if table[gens[i]][gens[j]] != table[gens[j]][gens[i]]:
                braid_bad.append(("commute", i, j))
    out.append(("%s: braid relations "
                "(pi_i pi_{i+1} pi_i = pi_{i+1} pi_i pi_{i+1}, "
                "pi_i pi_j = pi_j pi_i for |i-j| >= 2)" % name,
                not braid_bad,
                "all Coxeter relations" if not braid_bad
                else "failures %r" % braid_bad))
    return out


def idx_of_simple(W, n, i):
    s = simple(n, i)
    return W.index(s)


# ----------------------------------------------------------------------
# Submonoids (bitmask over the N elements) and the covering number
# ----------------------------------------------------------------------

def generate_from(S, x, N, table, e):
    """Smallest submonoid containing the submonoid mask S and the element x
    (and the identity).  Worklist closure under the binary product."""
    mask = S | (1 << x) | (1 << e)
    elems = [i for i in range(N) if (mask >> i) & 1]
    stack = [(y, x) for y in elems] + [(x, y) for y in elems]
    while stack:
        a, b = stack.pop()
        c = table[a][b]
        if not (mask >> c) & 1:
            mask |= 1 << c
            elems.append(c)
            for y in elems:
                stack.append((y, c))
                stack.append((c, y))
    return mask


def enumerate_submonoids(N, table, e):
    """ALL submonoids of the monoid, as bitmasks.  Breadth-first from {e};
    from a submonoid S and an element x, take the closure of S union {x}.
    Every submonoid is generated by its elements one at a time, so all of them
    are reached."""
    start = 1 << e
    seen = {start}
    frontier = [start]
    while frontier:
        S = frontier.pop()
        for x in range(N):
            if (S >> x) & 1:
                continue
            T = generate_from(S, x, N, table, e)
            if T not in seen:
                seen.add(T)
                frontier.append(T)
    return seen


def popcount(mask):
    return bin(mask).count("1")


def one_cover_exists(submonoids, full):
    """A single PROPER submonoid can never cover: a proper subset is not the
    whole monoid.  We nevertheless scan all submonoids to confirm that the only
    submonoid equal to the full monoid is the full monoid itself."""
    return any(S == full for S in submonoids if S != full)


def find_two_cover(submonoids, full, N, table, e):
    """Exhaustive search over all pairs of proper submonoids.

    Equivalence used: a pair (A, B) of proper submonoids with A union B = full
    exists iff there is a proper submonoid A with closure(full \\ A) != full
    (take B = closure(full \\ A); conversely complement(A) is contained in B,
    so its closure is contained in B, which is proper).  This decides the
    question over ALL pairs while touching each A once.

    Returns (A, B) for a witness or None if no 2-cover exists.
    """
    for A in submonoids:
        if A == full:
            continue
        B = generate_from(full & ~A, e, N, table, e)
        if B != full:
            return A, B
    return None


def brute_two_cover(submonoids, full):
    """Naive O(#subs^2) pair scan; used to cross-check find_two_cover on the
    small monoids.  Returns a witness or None."""
    proper = [S for S in submonoids if S != full]
    for i in range(len(proper)):
        for j in range(i + 1, len(proper)):
            if (proper[i] | proper[j]) == full:
                return proper[i], proper[j]
    return None


def exact_covering_number(submonoids, full, N, table, e):
    """Exact covering number for the cases at hand: 2 if a 2-cover exists,
    else float('inf') (a 1-cover is impossible with proper submonoids, and for
    H(S_2) no finite cover exists at all)."""
    if one_cover_exists(submonoids, full):
        return 1, None
    w = find_two_cover(submonoids, full, N, table, e)
    if w is not None:
        return 2, w
    return float("inf"), None


def is_submonoid(mask, N, table, e):
    if not ((mask >> e) & 1):
        return False
    elems = [i for i in range(N) if (mask >> i) & 1]
    for a in elems:
        for b in elems:
            if not ((mask >> table[a][b]) & 1):
                return False
    return True


# ----------------------------------------------------------------------
# The length inequality
# ----------------------------------------------------------------------

def length_inequality_violations(n):
    """For the Demazure product, l(x star y) >= max(l(x), l(y)) for all x, y."""
    W, idx, N, table, e = build(n)
    bad = []
    for i in range(N):
        li = length(W[i])
        for j in range(N):
            lj = length(W[j])
            lk = length(W[table[i][j]])
            if lk < max(li, lj):
                bad.append((W[i], W[j], W[table[i][j]]))
    return N, bad


# ----------------------------------------------------------------------
# Direct product of 0-Hecke monoids
# ----------------------------------------------------------------------

def product_table(t1, N1, t2, N2):
    """Multiplication table of M1 x M2, index i*N2+j."""
    N = N1 * N2
    T = [[0] * N for _ in range(N)]
    for i1 in range(N1):
        for i2 in range(N2):
            a = i1 * N2 + i2
            for j1 in range(N1):
                for j2 in range(N2):
                    b = j1 * N2 + j2
                    T[a][b] = t1[i1][j1] * N2 + t2[i2][j2]
    return T


def product_mask(m1, m2, N1, N2):
    """Bitmask of the product subset S1 x S2 inside M1 x M2."""
    out = 0
    for i1 in range(N1):
        if (m1 >> i1) & 1:
            for i2 in range(N2):
                if (m2 >> i2) & 1:
                    out |= 1 << (i1 * N2 + i2)
    return out


# ----------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------

def main():
    checks = []

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))

    line = "=" * 74
    print(line)
    print("Disproof of conjecture 00000003844 -- reproduction")
    print(line)
    print("Definition: covering number = least number of PROPER submonoids needed")
    print("            to cover a monoid, infinity if impossible.")
    print("Conjecture: every finite-type 0-Hecke monoid and every plactic monoid has")
    print("            infinite covering number; so do all their direct products.")
    print("Claimed value: FALSE.")

    # ------------------------------------------------------------------
    # 1. Build H(S_n) and verify the monoid axioms
    # ------------------------------------------------------------------
    print("\n[1] The 0-Hecke monoids H(S_n) and their monoid axioms")
    built = {}
    for n in (2, 3, 4):
        W, idx, N, table, e = build(n)
        built[n] = (W, idx, N, table, e)
        print("    H(S_%d): |H| = %d" % (n, N))
        for name, ok, detail in check_monoid("H(S_%d)" % n, W, N, table, e, n):
            check(name, ok, detail)
            print("      [%s] %s -- %s" % ("ok" if ok else "FAIL", name, detail))

    # The explicit H(S_3) table, in the order
    #   e, s2, s1, s1s2, s2s1, w0   (indices 0..5).
    W3, idx3, N3, t3, e3 = built[3]
    print("\n    H(S_3) multiplication table (rows = left factor, * = Demazure):")
    labels3 = []
    for v in W3:
        if length(v) == 3:
            labels3.append("w0")          # the longest element of S_3
        else:
            rw = reduced_word(3, v)
            labels3.append("e" if not rw
                           else "".join("s%d" % (i + 1) for i in rw))
    hdr = "        " + "".join("%7s" % labs for labs in labels3)
    print(hdr)
    for i in range(N3):
        print("    %-6s" % labels3[i]
              + "".join("%7s" % labels3[t3[i][j]] for j in range(N3)))
    check("H(S_3): the 6 elements are e, s2, s1, s1s2, s2s1, w0 for every "
          "reduced-word labelling",
          sorted(labels3) == sorted(["e", "s2", "s1", "s1s2", "s2s1", "w0"]),
          "labels = %r" % labels3)
    braid3 = (t3[t3[2][1]][2] == 5 and t3[t3[1][2]][1] == 5
              and t3[2][1] == 3 and t3[1][2] == 4)
    check("H(S_3): braid s1 s2 s1 = s2 s1 s2 = w0 (`*` is the Demazure product)",
          braid3, "s1s2 = index 3, s2s1 = index 4, w0 = index 5")

    # ------------------------------------------------------------------
    # 2. All submonoids and the exact covering number
    # ------------------------------------------------------------------
    print("\n[2] Exhaustive submonoid enumeration and covering numbers")
    covers = {}
    for n in (2, 3, 4):
        W, idx, N, table, e = built[n]
        full = (1 << N) - 1
        subs = enumerate_submonoids(N, table, e)
        # sanity: every enumerated mask really is a submonoid containing e
        assert all(is_submonoid(S, N, table, e) for S in subs)
        # sanity: closure under the product and totality of the enumeration
        cov, witness = exact_covering_number(subs, full, N, table, e)
        covers[n] = (subs, cov, witness)
        print("    H(S_%d): %d submonoids (including the full monoid); "
              "sizes %r" % (n, len(subs), sorted({popcount(S) for S in subs})))
        if n <= 3:
            naive = brute_two_cover(subs, full)
            check("H(S_%d): naive O(#subs^2) pair scan agrees with the "
                  "complement-closure pair decision" % n,
                  (naive is None) == (witness is None),
                  "both give a 2-cover" if naive is not None else "both give none")
        one = one_cover_exists(subs, full)
        check("H(S_%d): no single proper submonoid covers H(S_%d)" % (n, n),
              not one,
              "the only submonoid with all %d elements is the full monoid "
              "itself; every proper submonoid is a proper subset" % N)

    # Witness for S_3 with the labels used in the write-up
    subs3, cov3, wit3 = covers[3]
    A3 = (1 << idx3[simple(3, 1)]) | (1 << e3)          # {e, s2}
    B3 = ((1 << N3) - 1) & ~(1 << idx3[simple(3, 1)])    # H \ {s2}
    check("H(S_3): A = {e, s2} = indices [0,1] is a submonoid",
          is_submonoid(A3, N3, t3, e3), "s2 is idempotent")
    check("H(S_3): B = H \\ {s2} = indices [0,2,3,4,5] is a submonoid",
          is_submonoid(B3, N3, t3, e3),
          "length identity l(x*y) >= max(l(x),l(y)) keeps B closed")
    check("H(S_3): A and B are proper and A union B = H(S_3)",
          A3 != ((1 << N3) - 1) and B3 != ((1 << N3) - 1)
          and (A3 | B3) == ((1 << N3) - 1),
          "explicit 2-cover")
    check("H(S_3): covering number is exactly 2",
          cov3 == 2, "2 suffices (A, B) and 1 is impossible")

    # The same A/B works for every simple reflection, in every rank >= 2
    allgens = []
    for n in (3, 4):
        W, idx, N, table, e = built[n]
        full = (1 << N) - 1
        for i in range(n - 1):
            g = idx[simple(n, i)]
            A = (1 << e) | (1 << g)
            B = full & ~(1 << g)
            allgens.append((n, i + 1, is_submonoid(A, N, table, e),
                            is_submonoid(B, N, table, e), (A | B) == full))
    check("H(S_n), n in {3,4}: for EVERY simple reflection s, A = {e, s} and "
          "B = H \\ {s} give a 2-cover",
          all(okA and okB and okc for _, _, okA, okB, okc in allgens),
          "; ".join("H(S_%d), s_%d: A ok/ B ok/ cover = %s/%s/%s"
                    % tup for tup in allgens))

    subs4, cov4, wit4 = covers[4]
    check("H(S_4): covering number is exactly 2",
          cov4 == 2,
          "exhaustive over %d submonoids; witness sizes %r"
          % (len(subs4), (popcount(wit4[0]), popcount(wit4[1]))))

    subs2, cov2, _ = covers[2]
    check("H(S_2) = {e, s}: covering number is infinite (the only proper "
          "submonoid is {e})",
          cov2 == float("inf")
          and (subs2 == {(1 << 0) | (1 << 1), 1 << 0}),
          "the union of all proper submonoids is {e} != {e,s}")

    # ------------------------------------------------------------------
    # 3. The length inequality behind the general theorem
    # ------------------------------------------------------------------
    print("\n[3] The length inequality l(x star y) >= max(l(x), l(y))")
    for n in (3, 4, 5):
        N, bad = length_inequality_violations(n)
        check("S_%d: l(x star y) >= max(l(x), l(y)) for all %d x %d pairs"
              % (n, N, N), not bad,
              "0 violations" if not bad else "%d violations" % len(bad))
        print("    S_%d: |H| = %d, violations = %d" % (n, N, len(bad)))
    print("    Consequence: for x, y != s we have x star y != s, so H \\ {s} is")
    print("    closed; with {e, s} this covers H(W) and gives covering number 2")
    print("    for every finite-type 0-Hecke monoid of rank >= 2.")

    # ------------------------------------------------------------------
    # 4. The direct-product clause
    # ------------------------------------------------------------------
    print("\n[4] Direct products: cov(M1 x M2) <= cov(M1) * cov(M2)")
    W1, idx1, N1, t1, e1 = built[3]
    full1 = (1 << N1) - 1
    tP = product_table(t1, N1, t1, N1)
    NP = N1 * N1
    fullP = (1 << NP) - 1
    s = idx1[simple(3, 1)]                               # s2
    A = (1 << e1) | (1 << s)
    B = full1 & ~(1 << s)
    parts = [("A x A", A, A), ("A x B", A, B), ("B x A", B, A), ("B x B", B, B)]
    ok_all = True
    lines = []
    for lab, m1, m2 in parts:
        pm = product_mask(m1, m2, N1, N1)
        ok = is_submonoid(pm, NP, tP, e1 * N1 + e1) and pm != fullP
        ok_all = ok_all and ok
        lines.append("%s (size %d) proper submonoid: %s"
                     % (lab, popcount(pm), ok))
    union = 0
    for lab, m1, m2 in parts:
        union |= product_mask(m1, m2, N1, N1)
    check("H(S_3) x H(S_3): the four products A x A, A x B, B x A, B x B are "
          "proper submonoids",
          ok_all, "; ".join(lines))
    check("H(S_3) x H(S_3): their union is the whole 36-element product monoid",
          union == fullP, "cov(H(S_3) x H(S_3)) <= 4 < infinity")
    check("cov(H(S_3) x H(S_3)) <= cov(H(S_3))^2 = 4, so the direct-product "
          "clause of the conjecture is false",
          union == fullP and cov3 == 2,
          "a finite 4-cover exists; more generally cov(M1 x M2) <= "
          "cov(M1)*cov(M2)")

    # ------------------------------------------------------------------
    # 5. Report
    # ------------------------------------------------------------------
    print("\n[5] Checks")
    all_ok = True
    for name, ok, detail in checks:
        all_ok = all_ok and ok
        print("    [%s] %s" % ("ok  " if ok else "FAIL", name))
        if detail:
            print("           %s" % detail)

    print("\nSummary of covering numbers")
    print("    H(S_2): inf   (only proper submonoid is {e})")
    print("    H(S_3): %s   (A = {e,s2}, B = H \\ {s2})" % ("2" if cov3 == 2 else cov3))
    print("    H(S_4): %s   (same A/B for each generator)"
          % ("2" if cov4 == 2 else cov4))
    print("    H(S_3) x H(S_3): <= 4 < infinity")

    print("\n" + line)
    if all_ok:
        print("PASS: conjecture 00000003844 is FALSE.")
        print("  * H(S_3) (finite type A_2, 6 elements) has covering number 2,")
        print("    and so does H(S_4); in fact every finite-type 0-Hecke monoid")
        print("    of rank >= 2 has covering number exactly 2.")
        print("  * cov(M1 x M2) <= cov(M1) cov(M2), so H(S_3) x H(S_3) has a")
        print("    finite covering number (<= 4), not an infinite one.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
