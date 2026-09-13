#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001006.

Conjecture (as filed, English and Chinese):

    Definition: An m-ovoid (meeting every generating line in exactly m points).
    Conjecture: m-ovoids of Q(4,q) exist only when m | (q+1) (an existence
    criterion for m-ovoids).

    定义：m-ovoid(每条生成线恰交 m 点)。猜想：Q(4, q) 的 m-ovoid 仅在
    m | (q+1) 存在(m-ovoid 存在判据)。

The conjecture is FALSE.  This script produces a concrete counterexample at the
smallest case q = 2, m = 2:

  * Q(4,2) is the parabolic quadric in PG(4,2).  Model it by the 15 nonzero
    vectors x in F_2^5 with Q(x) = x0 + x1*x2 + x3*x4 = 0.  Its generating
    lines are the triples {a, b, a+b} of distinct points a, b with
    B(a,b) = a1*b2 + a2*b1 + a3*b4 + a4*b3 = 0.

  * Q(4,2) has ovoids (1-ovoids): 5-point sets meeting every one of its 15
    lines in exactly 1 point.  There are exactly 6 of them.

  * If O is an ovoid then its complement O^c has 15 - 5 = 10 points and meets
    every line in exactly (q+1) - 1 = 3 - 1 = 2 points, so O^c is a 2-ovoid.

  * But m = 2 does NOT divide q + 1 = 3.  Hence the necessary condition
    "m | (q+1)" fails for an m-ovoid that provably exists: the conjecture is
    false as stated.

Everything is exact and exhaustive (no sampling).  Standard library only.
Exits 0 on PASS and non-zero on FAIL.
"""

from itertools import combinations

# ----------------------------------------------------------------------------
# The vector model of Q(4,2)
#
# A point is encoded by an integer n in {0,...,31}; bit i of n is coordinate i
# of the vector x in F_2^5 (i = 0,...,4).  This is a bijection between the 32
# vectors and the integers 0,...,31.
# ----------------------------------------------------------------------------


def bit(n, i):
    """Coordinate i of the vector encoded by n."""
    return (n >> i) & 1


def vec(n):
    """The vector (x0, x1, x2, x3, x4) encoded by n."""
    return tuple(bit(n, i) for i in range(5))


def Q_vec(x):
    """Q(x) = x0^2 + x1*x2 + x3*x4 over F_2 (so x0^2 = x0)."""
    return (x[0] ^ (x[1] & x[2]) ^ (x[3] & x[4])) & 1


def Q(n):
    return Q_vec(vec(n))


def is_point(n):
    """Nonzero vector with Q(x) = 0."""
    return 0 < n < 32 and Q(n) == 0


def B_vec(x, y):
    """Polar bilinear form B(x,y) = x1*y2 + x2*y1 + x3*y4 + x4*y3 (mod 2)."""
    return ((x[1] & y[2]) ^ (x[2] & y[1]) ^ (x[3] & y[4]) ^ (x[4] & y[3])) & 1


def B(a, b):
    return B_vec(vec(a), vec(b))


def is_line_pair(a, b):
    """a, b are two distinct points whose spanned PG(4,2)-line lies in Q."""
    return is_point(a) and is_point(b) and a != b and B(a, b) == 0


def xor(a, b):
    """Coordinatewise sum in F_2^5; encodes a + b."""
    return a ^ b


def is_line(a, b, c):
    """{a,b,c} is a generating line in the normal form c = a + b."""
    return is_line_pair(a, b) and c == xor(a, b)


# ----------------------------------------------------------------------------
# Enumerations
# ----------------------------------------------------------------------------


def all_points():
    return [n for n in range(32) if is_point(n)]


def all_lines():
    """All generating lines, each represented once as a sorted triple."""
    pts = all_points()
    lines = set()
    for a, b in combinations(pts, 2):
        if is_line_pair(a, b) and is_point(xor(a, b)):
            lines.add(tuple(sorted((a, b, xor(a, b)))))
    return sorted(lines)


def hit_count(S, L):
    """Number of points of the line L that lie in the point set S."""
    S = set(S)
    return sum(1 for x in L if x in S)


def all_ovoids():
    """Every 5-subset meeting each line in exactly one point."""
    pts = all_points()
    lines = all_lines()
    return [tuple(S) for S in combinations(pts, 5)
            if all(hit_count(S, L) == 1 for L in lines)]


def vecs(encs):
    return [vec(n) for n in encs]


# ----------------------------------------------------------------------------
# The counterexample
# ----------------------------------------------------------------------------

# A canonically chosen ovoid (5 points of Q(4,2)).
OVOID = (2, 4, 15, 23, 30)

# The expected complete line list (sorted triples of encodings).
LINES15 = [
    [2, 8, 10], [2, 16, 18], [2, 25, 27],
    [4, 8, 12], [4, 16, 20], [4, 25, 29],
    [7, 8, 15], [7, 16, 23], [7, 25, 30],
    [10, 20, 30], [10, 23, 29],
    [12, 18, 30], [12, 23, 27],
    [15, 18, 29], [15, 20, 27],
]

POINTS15 = [2, 4, 7, 8, 10, 12, 15, 16, 18, 20, 23, 25, 27, 29, 30]


def main():
    checks = []
    ok_all = True

    def check(name, ok, detail=""):
        nonlocal ok_all
        ok_all = ok_all and bool(ok)
        checks.append((name, bool(ok), detail))

    q, m = 2, 2

    # 1. Rebuild Q(4,2) -------------------------------------------------------
    pts = all_points()
    lines = all_lines()

    check("Q(4,2) has 15 points", len(pts) == 15, f"points = {pts}")
    check("point set equals the canonical list", pts == POINTS15,
          f"{pts}")
    per_line = set(len(L) for L in lines)
    check("Q(4,2) has 15 lines", len(lines) == 15, f"|lines| = {len(lines)}")
    check("every line has exactly 3 points (= q+1)", per_line == {3},
          f"line sizes = {sorted(per_line)}")
    line_set = [list(L) for L in lines]
    check("line list equals the canonical list", line_set == LINES15,
          f"{line_set}")
    pcount = {p: sum(1 for L in lines if p in L) for p in pts}
    check("every point lies on exactly 3 lines (= q+1)",
          set(pcount.values()) == {3}, f"per-point line counts = {sorted(set(pcount.values()))}")
    # every pair of distinct points spans a line of the GQ iff B = 0:
    # closure check: the third point of every line is a point
    check("every line is closed: a+b is a point for all pairs with B=0",
          all(is_point(xor(a, b)) for a, b in combinations(pts, 2)
              if is_line_pair(a, b)),
          "verified pairwise")

    # 2. Enumerate ALL ovoids -------------------------------------------------
    ovoids = all_ovoids()
    check("exactly 6 ovoids (= 1-ovoids) exist", len(ovoids) == 6,
          f"ovoids = {[list(O) for O in ovoids]}")
    # brute force cross-check (C(15,5) = 3003 subsets)
    bf = sum(1 for S in combinations(pts, 5)
             if all(hit_count(S, L) == 1 for L in lines))
    check("brute-force ovoid count agrees", bf == len(ovoids),
          f"brute force = {bf}")

    # 3. The explicit ovoid and its complement --------------------------------
    O = OVOID
    check("chosen O is one of the ovoids", O in ovoids, f"O = {list(O)}")
    check("O has 5 points (= q^2+1)", len(O) == 5, f"|O| = {len(O)}")
    check("all points of O lie on Q(4,2)", all(is_point(n) for n in O),
          f"O vectors = {vecs(O)}")

    O_hits = [hit_count(O, L) for L in lines]
    check("O meets every line in exactly 1 point (O is an ovoid)",
          set(O_hits) == {1}, f"hit counts = {O_hits}")

    comp = tuple(n for n in pts if n not in O)
    check("complement has 10 points (= q^2+q)", len(comp) == 10,
          f"|O^c| = {len(comp)}")
    check("complement consists of points of Q(4,2)",
          all(is_point(n) for n in comp), f"O^c = {list(comp)}")
    comp_hits = [hit_count(comp, L) for L in lines]
    check("complement meets every line in exactly 2 points (2-ovoid)",
          set(comp_hits) == {2}, f"hit counts = {comp_hits}")

    # complement count is consistent: 3 - 1 = 2
    check("per-line accounting: 1 (ovoid) + 2 (complement) = 3 (line size)",
          all(h1 + h2 == 3 for h1, h2 in zip(O_hits, comp_hits)),
          "holds line by line")

    # 4. The divisibility criterion -------------------------------------------
    check("m = 2 does NOT divide q + 1 = 3", (q + 1) % m != 0,
          f"3 mod 2 = {3 % 2} (q+1 = 3, m = 2)")

    # hard assertions
    assert len(pts) == 15 and len(lines) == 15
    assert len(ovoids) == 6
    assert len(O) == 5 and set(O_hits) == {1}
    assert len(comp) == 10 and set(comp_hits) == {2}
    assert (q + 1) % m != 0
    assert ok_all

    # 5. Report ---------------------------------------------------------------
    bar = "=" * 74
    print(bar)
    print("Disproof of conjecture 00000001006 -- reproduction")
    print(bar)
    print(f"\nQ(4,{q}): {len(pts)} points, {len(lines)} lines, "
          f"{lines[0].__len__()} points per line, "
          f"{sorted(set(pcount.values()))[0]} lines per point.")
    print(f"Ovoids (1-ovoids) of Q(4,{q}): {len(ovoids)} in total.")
    print(f"\nExplicit ovoid O (enc : vector):")
    for n in O:
        print(f"    {n:>2} : {vec(n)}")
    print(f"  |O| = {len(O)} = q^2 + 1")
    print(f"\nO meets each line in exactly 1 point; line-hit counts:")
    print(f"    {O_hits}")
    print(f"\nComplement O^c (enc : vector), {len(comp)} points:")
    for n in comp:
        print(f"    {n:>2} : {vec(n)}")
    print(f"  |O^c| = {len(comp)} = q^2 + q")
    print(f"\nO^c meets each line in exactly 2 points; line-hit counts:")
    print(f"    {comp_hits}")
    print(f"\nTherefore O^c is a 2-ovoid of Q(4,2).")
    print(f"But m = 2 does not divide q+1 = 3 (3 mod 2 = {3 % 2}).")
    print(f"=> the existence criterion 'm-ovoids exist only when m | (q+1)'")
    print(f"   is FALSE.")

    print("\n[line-by-line table]")
    print(f"    {'line (enc)':<16} {'line (vectors)':<34} "
          f"{'|L n O|':>7} {'|L n O^c|':>9}")
    for L, h1, h2 in zip(lines, O_hits, comp_hits):
        ls = "{" + ",".join(f"{v}" for v in vecs(L)) + "}"
        print(f"    {str(list(L)):<16} {ls:<34} {h1:>7} {h2:>9}")

    print("\n[checks]")
    for name, ok, detail in checks:
        print(f"    [{'ok  ' if ok else 'FAIL'}] {name}")
        if detail:
            print(f"           {detail}")

    print("\n" + bar)
    if ok_all:
        print("PASS: Q(4,2) has a 2-ovoid (complement of an ovoid resp. an")
        print("      explicit 2-ovoid), yet 2 does not divide q+1 = 3;")
        print("      conjecture 00000001006 is FALSE.")
        print(bar)
        return 0
    print("FAIL: at least one check did not verify.")
    print(bar)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
