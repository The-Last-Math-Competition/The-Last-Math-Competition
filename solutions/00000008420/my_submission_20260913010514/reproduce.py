#!/usr/bin/env python3
"""Independent verification script for the disproof of TLMC conjecture 00000008420.

Conjecture clause under attack:
    "the smallest order of a KTS with a transitive automorphism is the
     point-transitive type of order 15"

Counterexample: KTS(9), the line system of the affine plane AG(2,3).
It is a resolvable Steiner triple system on 9 points whose translation
group F_3^2 acts transitively on the points.  Since 9 < 15, the clause
is FALSE.

This script builds the 12 lines explicitly and checks:
  (a) it is a Steiner triple system: each of the 36 unordered point pairs
      lies in exactly one of the 12 lines;
  (b) it is resolvable: the 12 lines split into 4 parallel classes, each
      of 3 pairwise disjoint lines covering all 9 points (4 = (9-1)/2);
  (c) each of the 9 translations t_v(p) = p + v maps the line set to itself;
  (d) the translation group acts transitively: for all p, q there is v
      with t_v(p) = q (namely v = q - p).

No external dependencies.  Run:  python3 reproduce.py
"""

from itertools import combinations

F = [0, 1, 2]  # the field F_3


def add(a: int, b: int) -> int:
    return (a + b) % 3


def mul(a: int, b: int) -> int:
    return (a * b) % 3


# Points are elements of F_3 x F_3.
pts = [(x, y) for x in F for y in F]
assert len(pts) == 9

# Lines, indexed 0..11:
#   k = 3*m + b  (0..8):  L_k = {(x, m*x + b) : x in F_3}   (9 non-vertical lines)
#   k = 9 + c    (9..11): L_k = {(c, y) : y in F_3}          (3 vertical lines)
lines = []
for m in F:
    for b in F:
        lines.append(tuple((x, (mul(m, x) + b) % 3) for x in F))
for c in F:
    lines.append(tuple((c, y) for y in F))

assert len(lines) == 12
assert len(set(lines)) == 12, "lines must be pairwise distinct"

# Parallel classes: C_m = {L_{3m}, L_{3m+1}, L_{3m+2}} for m = 0,1,2 and
# C_3 = {L_9, L_10, L_11} (the vertical class).
classes = [[lines[3 * m + b] for b in F] for m in F] + [[lines[9 + c] for c in F]]


def t(v, p):
    """Translation t_v(p) = p + v."""
    return (add(p[0], v[0]), add(p[1], v[1]))


def main() -> None:
    # (a) Steiner triple system: 36 pairs, each covered exactly once.
    all_pairs = sorted(tuple(sorted(pr)) for pr in combinations(pts, 2))
    assert len(all_pairs) == 36
    cover = {pr: 0 for pr in all_pairs}
    for L in lines:
        for pr in combinations(L, 2):
            cover[tuple(sorted(pr))] += 1
    assert all(c == 1 for c in cover.values()), "STS property failed"
    print("(a) STS: each of the 36 point pairs lies in exactly one of the 12 lines  [OK]")

    # (b) Resolvability: 4 parallel classes.
    assert len(classes) == 4
    seen = []
    for cls in classes:
        assert len(cls) == 3
        s = [set(L) for L in cls]
        assert not (s[0] & s[1]) and not (s[0] & s[2]) and not (s[1] & s[2]), "not disjoint"
        assert s[0] | s[1] | s[2] == set(pts), "class does not cover all 9 points"
        seen.extend(cls)
    assert len(seen) == 12 and set(seen) == set(lines), "classes must partition the line set"
    print("(b) resolvable: 4 parallel classes, each 3 pairwise disjoint lines covering"
          " all 9 points; 4 = (9-1)/2  [OK]")

    # (c) Every translation maps the line set onto itself.
    line_set = set(lines)
    for v in pts:
        image = {tuple(sorted(t(v, p) for p in L)) for L in lines}
        assert image == line_set, f"translation by {v} does not preserve the line set"
    print("(c) all 9 translations t_v(p) = p + v map the 12-line set onto itself  [OK]")

    # (d) Transitivity of the translation group.
    for p in pts:
        for q in pts:
            v = ((q[0] - p[0]) % 3, (q[1] - p[1]) % 3)
            assert t(v, p) == q
    print("(d) the translation group acts transitively on the 9 points  [OK]")

    print()
    print("KTS(9) is a point-transitive Kirkman triple system of order 9 < 15")


if __name__ == "__main__":
    main()
