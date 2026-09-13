#!/usr/bin/env python3
"""
Reproduction script for the disproof of conjecture 00000005626.

Claim under test
----------------
"Every 6-point subset of the plane in general position contains an empty
pentagon, with Horton-type sets the unique counterexample family."

Definition used
---------------
A 5-element subset S of a finite point set is an EMPTY PENTAGON if
  (1) S is in strictly convex position (all five points are extreme points
      of conv(S)), and
  (2) conv(S) contains no point of the ambient set outside S.

Counterexample
--------------
The five vertices of the convex pentagon
    P1=(0,0) P2=(4,0) P3=(5,2) P4=(2,4) P5=(-1,2)
together with the interior lattice point C=(2,1).

We verify with exact integer arithmetic:
  * the six points are in general position (no three collinear);
  * the five outer points are strictly convex;
  * C is strictly interior to the pentagon;
  * among all C(6,5)=6 five-subsets the number of empty pentagons is 0.

Remarks
-------
The "obvious" centre (2,2) is NOT in general position: it is collinear with
P3=(5,2) and P5=(-1,2).  Among all interior lattice points, (2,1) is the
unique one that is strictly inside the hull of every four of the five outer
vertices and keeps the six points in general position.

We also repeat the count for the regular pentagon plus its centre (using
sympy when available) as a sanity check.

Only the Python standard library is required for the integer part.
Exits 0 on success, 1 on any failure.
"""

import sys
from itertools import combinations

# --------------------------------------------------------------------------
# Exact integer geometry
# --------------------------------------------------------------------------

def cross(o, a, b):
    """Oriented area of the turn o -> a -> b (exact for integer points)."""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def in_tri(u, v, w, p, eps=0):
    """p in closed triangle uvw (either orientation), duplicate-test free."""
    s1, s2, s3 = cross(u, v, p), cross(v, w, p), cross(w, u, p)
    left = s1 >= -eps and s2 >= -eps and s3 >= -eps
    right = s1 <= eps and s2 <= eps and s3 <= eps
    return left or right


def in_hull(points, p, eps=0):
    """p in conv(points) via Caratheodory (some triangle contains it)."""
    for u, v, w in combinations(points, 3):
        if in_tri(u, v, w, p, eps):
            return True
    return False


def in_convex_position(points, eps=0):
    """True iff every point is an extreme point of conv(points)."""
    pts = list(points)
    for i, p in enumerate(pts):
        others = [q for j, q in enumerate(pts) if j != i]
        if in_hull(others, p, eps):
            return False
    return True


def empty_pentagons(ambient):
    """Return (count, list of empty 5-subsets)."""
    found = []
    for S in combinations(ambient, 5):
        if not in_convex_position(S):
            continue
        outside = [q for q in ambient if q not in S]
        if any(in_hull(S, q) for q in outside):
            continue
        found.append(S)
    return len(found), found


# --------------------------------------------------------------------------
# The integer counterexample
# --------------------------------------------------------------------------

P1, P2, P3, P4, P5 = (0, 0), (4, 0), (5, 2), (2, 4), (-1, 2)
C = (2, 1)
OUTER = [P1, P2, P3, P4, P5]
POINTS = OUTER + [C]

failures = []


def check(name, ok, detail=""):
    status = "PASS" if ok else "FAIL"
    print(f"[{status}] {name}" + (f" :: {detail}" if detail else ""))
    if not ok:
        failures.append(name)


def main():
    print("=" * 72)
    print("Counterexample: pentagon (0,0),(4,0),(5,2),(2,4),(-1,2) + (2,1)")
    print("=" * 72)

    # 1. General position: all 20 triples non-collinear.
    bad = [t for t in combinations(range(6), 3)
           if cross(POINTS[t[0]], POINTS[t[1]], POINTS[t[2]]) == 0]
    check("general position (no 3 of 6 collinear, 20 triples)",
          not bad, f"{len(bad)} collinear triples")

    # The naive centre (2,2) is collinear with P3 and P5.
    c22 = (2, 2)
    c22_coll = [t for t in combinations(OUTER + [c22], 3)
                if cross(t[0], t[1], t[2]) == 0]
    print(f"[info] centre (2,2) would give {len(c22_coll)} collinear triple(s): "
          f"{c22_coll} -> rejected")

    # 2. Strict convexity of the five outer vertices.
    turns = [cross(OUTER[i], OUTER[(i + 1) % 5], OUTER[(i + 2) % 5])
             for i in range(5)]
    same_sign = all(t > 0 for t in turns) or all(t < 0 for t in turns)
    check("five outer points strictly convex (consecutive cross products "
          "same nonzero sign)", same_sign, f"cross products = {turns}")

    # 3. Centre strictly interior to the pentagon.
    edges = [cross(OUTER[i], OUTER[(i + 1) % 5], C) for i in range(5)]
    if all(t > 0 for t in turns):
        inside = all(e > 0 for e in edges)
    else:
        inside = all(e < 0 for e in edges)
    check("centre (2,1) strictly interior to pentagon hull", inside,
          f"edge cross products = {edges}")

    # 3b. Centre strictly inside hull of every four outer vertices.
    quads_ok = True
    for omit in range(5):
        quad = [OUTER[j] for j in range(5) if j != omit]
        # order the remaining four cyclically
        order = [OUTER[j] for j in [0, 1, 2, 3, 4] if j != omit]
        if not all(cross(order[i], order[(i + 1) % 4], C) > 0
                   for i in range(4)):
            quads_ok = False
    check("centre strictly inside hull of every 4 of the 5 outer vertices",
          quads_ok)

    # 4. Enumerate all five-subsets: none is an empty pentagon.
    count, found = empty_pentagons(POINTS)
    check("number of empty pentagons among all C(6,5)=6 subsets is 0",
          count == 0, f"count = {count}")
    for S in combinations(POINTS, 5):
        missing = [q for q in POINTS if q not in S]
        convex = in_convex_position(S)
        if convex:
            reason = ("not empty: omitted point " + str(missing[0])
                      + " lies in hull")
        else:
            reason = "not in convex position (interior/non-extreme point)"
        print(f"       subset {S} -> {reason}")

    # 5. Regular pentagon + centre (sympy, optional).
    try:
        import sympy as sp
        t = sp.Rational(2, 1) * sp.pi / 5
        reg = [(sp.cos(k * t), sp.sin(k * t)) for k in range(5)]
        regc = (sp.Integer(0), sp.Integer(0))
        regall = reg + [regc]

        def ncross(o, a, b):
            return sp.N((a[0] - o[0]) * (b[1] - o[1])
                        - (a[1] - o[1]) * (b[0] - o[0]), 30)

        def nin_tri(u, v, w, p):
            s1, s2, s3 = ncross(u, v, p), ncross(v, w, p), ncross(w, u, p)
            eps = sp.Float("1e-20")
            return (s1 >= -eps and s2 >= -eps and s3 >= -eps) or \
                   (s1 <= eps and s2 <= eps and s3 <= eps)

        def nin_hull(pts, p):
            return any(nin_tri(u, v, w, p)
                       for u, v, w in combinations(pts, 3))

        def nconvex(pts):
            return all(not nin_hull([q for j, q in enumerate(pts) if j != i], p)
                       for i, p in enumerate(pts))

        rcount = 0
        for S in combinations(regall, 5):
            if not nconvex(S):
                continue
            if any(nin_hull(S, q) for q in regall if q not in S):
                continue
            rcount += 1
        check("regular pentagon + centre (sympy): 0 empty pentagons",
              rcount == 0, f"count = {rcount}")
    except ImportError:
        print("[info] sympy not available; skipping regular-pentagon check")
    except Exception as exc:  # pragma: no cover
        print(f"[info] sympy regular-pentagon check raised: {exc!r}")

    print("=" * 72)
    if failures:
        print("RESULT: FAIL (" + ", ".join(failures) + ")")
        return 1
    print("RESULT: PASS - conjecture 00000005626 is FALSE")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    sys.exit(main())
