#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001556.

    Conjecture: the chromatic number of the planar distance graph G(Z^2, D)
    with D = {1, 2, 4} is 7.

The conjecture is FALSE.  The file writes three scalars, so D is a set of
distances, and lattice-colouring work also states distance sets as SQUARED
norms; we cover BOTH standard readings:

    squared reading   Dsq  : dx^2 + dy^2 in {1, 2, 4}      (12 vectors)
    Euclidean reading Deuc : sqrt(dx^2 + dy^2) in {1, 2, 4} (12 axis vectors)

The map c5(x, y) = (x + 2y) mod 5 is a proper 5-colouring of the UNION graph
Dsq + Deuc, because no displacement d of the union has d_x + 2 d_y = 0 (mod 5).
Hence chi <= 5 < 7 under both readings: the claimed value 7 is false.

Exact values (clique lower bounds + colouring upper bounds):
    squared reading   chi = 5   (5-clique C5, colouring c5)
    Euclidean reading chi = 3   (3-clique C3, colouring c3)
    union graph       chi = 5   (5-clique C5, colouring c5)

A non-standard Manhattan (L1) reading has an explicit 9-clique, so chi >= 9
there and 7 is false as well.

Standard library only, Python 3.8+.  Exits non-zero if any check fails.
"""

import sys

# ----------------------------------------------------------------------
# Displacement sets (exact integer arithmetic)
# ----------------------------------------------------------------------

R = 4  # search radius large enough to contain all displacements of interest


def build_squared_reading():
    """dsq: dx^2 + dy^2 in {1, 2, 4}."""
    out = []
    for dx in range(-R, R + 1):
        for dy in range(-R, R + 1):
            if dx == 0 and dy == 0:
                continue
            if dx * dx + dy * dy in (1, 2, 4):
                out.append((dx, dy))
    return sorted(out)


def build_euclidean_reading():
    """deuc: dx^2 + dy^2 in {1, 4, 16} (Euclidean length 1, 2 or 4)."""
    out = []
    for dx in range(-R, R + 1):
        for dy in range(-R, R + 1):
            if dx == 0 and dy == 0:
                continue
            if dx * dx + dy * dy in (1, 4, 16):
                out.append((dx, dy))
    return sorted(out)


def build_manhattan_reading():
    """dman: |dx| + |dy| in {1, 2, 4} (non-standard L1 reading)."""
    out = []
    for dx in range(-R, R + 1):
        for dy in range(-R, R + 1):
            if dx == 0 and dy == 0:
                continue
            if abs(dx) + abs(dy) in (1, 2, 4):
                out.append((dx, dy))
    return sorted(out)


DSQ = build_squared_reading()
DEUC = build_euclidean_reading()
DMAN = build_manhattan_reading()
DUNION = sorted(set(DSQ) | set(DEUC))

# ----------------------------------------------------------------------
# Colourings
# ----------------------------------------------------------------------


def c5(p):
    """c5(x, y) = (x + 2y) mod 5."""
    return (p[0] + 2 * p[1]) % 5


def c3(p):
    """c3(x, y) = (x + y) mod 3."""
    return (p[0] + p[1]) % 3


# ----------------------------------------------------------------------
# Checks
# ----------------------------------------------------------------------


def main():
    checks = []
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    # ------------------------------------------------------------------
    # 1. The two standard displacement sets and their union
    # ------------------------------------------------------------------
    check("squared reading Dsq (dx^2+dy^2 in {1,2,4}) has 12 vectors",
          len(DSQ) == 12, f"{len(DSQ)} vectors")
    check("Euclidean reading Deuc (dx^2+dy^2 in {1,4,16}) has 12 vectors",
          len(DEUC) == 12, f"{len(DEUC)} vectors")
    check("union Dsq | Deuc has 16 vectors (the extra ones are (+-4,0),(0,+-4))",
          len(DUNION) == 16,
          f"{len(DUNION)} vectors; euclid-only extras = "
          f"{sorted(set(DUNION) - set(DSQ))}")
    check("Dsq is a subset of the union and Deuc is a subset of the union",
          set(DSQ) <= set(DUNION) and set(DEUC) <= set(DUNION),
          "Dsq, Deuc contained in DUNION")

    # ------------------------------------------------------------------
    # 2. Forbidden residue: no union displacement has dx + 2 dy = 0 (mod 5)
    # ------------------------------------------------------------------
    bad = [d for d in DUNION if c5(d) == 0]
    check("for every one of the 16 union displacements, "
          "(dx + 2*dy) mod 5 != 0",
          not bad, "all 16 residues nonzero" if not bad else f"zero at {bad}")

    # every displacement of each individual reading is covered
    check("hence c5 is a proper 5-colouring of BOTH readings",
          not [d for d in DSQ if c5(d) == 0] and not [d for d in DEUC if c5(d) == 0],
          "no displacement of Dsq or Deuc maps to residue 0")

    # ------------------------------------------------------------------
    # 3. Brute force: c5 is proper on a large box, union graph
    # ------------------------------------------------------------------
    B = 200
    violations = []
    for x in range(-B, B + 1):
        for y in range(-B, B + 1):
            cxy = c5((x, y))
            for (dx, dy) in DUNION:
                if c5((x + dx, y + dy)) == cxy:
                    violations.append(((x, y), (dx, dy)))
                    break
            if violations:
                break
        if violations:
            break
    check(f"brute force on [-{B},{B}]^2: c5 proper for the 16-vector union "
          f"({(2*B+1)**2} points x 16 vectors)",
          not violations,
          "no monochromatic edge" if not violations
          else f"violation at {violations[0]}")

    # ------------------------------------------------------------------
    # 4. Lower bounds: explicit cliques
    # ------------------------------------------------------------------
    C5 = [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]
    adj_sq = all((q[0] - p[0], q[1] - p[1]) in DSQ
                 for i, p in enumerate(C5) for q in C5[i + 1:])
    check("5-clique C5 = {(0,0),(+-1,0),(0,+-1)}: all pairwise displacements "
          "have squared norm in {1,2,4}",
          len(set(C5)) == 5 and adj_sq,
          "5 distinct points, 10 pairwise differences, all in Dsq")

    C3 = [(0, 0), (1, 0), (2, 0)]
    adj_euc = all((q[0] - p[0], q[1] - p[1]) in DEUC
                  for i, p in enumerate(C3) for q in C3[i + 1:])
    check("3-clique C3 = {(0,0),(1,0),(2,0)}: pairwise displacements have "
          "Euclidean length in {1,2,4}",
          adj_euc, "3 pairwise differences, all in Deuc")

    # ------------------------------------------------------------------
    # 5. The 3-colouring on the Euclidean reading
    # ------------------------------------------------------------------
    bad3 = [d for d in DEUC if c3(d) == 0]
    check("c3(x,y) = (x+y) mod 3: no Euclidean displacement has "
          "(dx+dy) mod 3 == 0",
          not bad3, "all 12 residues nonzero" if not bad3 else f"zero at {bad3}")

    B2 = 100
    viol3 = []
    for x in range(-B2, B2 + 1):
        for y in range(-B2, B2 + 1):
            cxy = c3((x, y))
            for (dx, dy) in DEUC:
                if c3((x + dx, y + dy)) == cxy:
                    viol3.append(((x, y), (dx, dy)))
                    break
            if viol3:
                break
        if viol3:
            break
    check(f"brute force on [-{B2},{B2}]^2: c3 proper for the Euclidean reading",
          not viol3, "no monochromatic edge" if not viol3
          else f"violation at {viol3[0]}")

    # ------------------------------------------------------------------
    # 6. Manhattan (non-standard L1) reading: explicit 9-clique
    # ------------------------------------------------------------------
    # Shifted from a symmetric search box: an explicit 9-clique exists.
    M9 = [(0, 0), (1, -1), (1, 1), (2, -2), (2, 0), (2, 2),
          (3, -1), (3, 1), (4, 0)]
    man_ok = all((abs(q[0] - p[0]) + abs(q[1] - p[1])) in (1, 2, 4)
                 for i, p in enumerate(M9) for q in M9[i + 1:])
    check("Manhattan reading |dx|+|dy| in {1,2,4}: the 9 points "
          "{(0,0),(1,+-1),(2,0),(2,+-2),(3,+-1),(4,0)} form a clique",
          man_ok,
          "36 pairwise L1 distances, all in {1,2,4}" if man_ok
          else "not a clique")

    # Independent bounded clique search to confirm size >= 9 is attainable.
    box = 3
    pts = [(x, y) for x in range(-box, box + 1) for y in range(-box, box + 1)]

    def man_adj(p, q):
        return (abs(p[0] - q[0]) + abs(p[1] - q[1])) in (1, 2, 4)

    best = [[]]

    def expand(cand, cur):
        if len(cur) > len(best[0]):
            best[0] = list(cur)
        if not cand:
            return
        for i, p in enumerate(cand):
            rest = [q for q in cand[i + 1:] if man_adj(p, q)]
            expand(rest, cur + [p])

    sys.setrecursionlimit(100000)
    expand(pts, [])
    check("independent clique search on [-3,3]^2 finds a Manhattan clique "
          "of size >= 9",
          len(best[0]) >= 9, f"maximum clique found has size {len(best[0])}: "
          f"{sorted(best[0])}")

    # c5 fails on the Manhattan reading, as it must (9-clique > 5 colours).
    witness = [d for d in DMAN if c5(d) == 0]
    check("c5 is NOT proper for the Manhattan reading (witness displacement "
          "(3,1) with (3 + 2*1) mod 5 = 0)",
          (3, 1) in witness and len(DMAN) > len(DUNION),
          f"witnesses {witness[:4]}...; |Dman| = {len(DMAN)} > 16")

    # ------------------------------------------------------------------
    # 7. Chromatic numbers
    # ------------------------------------------------------------------
    chi_union_lower = 5   # C5 clique
    chi_union_upper = 5   # c5 colouring
    chi_sq_lower = 5      # C5 clique
    chi_sq_upper = 5      # c5 colouring
    chi_euc_lower = 3     # C3 clique
    chi_euc_upper = 3     # c3 colouring

    check("chi(union graph) = 5 exactly: lower 5 (clique C5), upper 5 (c5)",
          chi_union_lower == chi_union_upper == 5,
          "5 <= chi <= 5")
    check("chi(squared reading) = 5 exactly: lower 5 (clique C5), "
          "upper 5 (c5)",
          chi_sq_lower == chi_sq_upper == 5,
          "5 <= chi <= 5, so chi = 5")
    check("chi(Euclidean reading) = 3 exactly: lower 3 (clique C3), "
          "upper 3 (c3)",
          chi_euc_lower == chi_euc_upper == 3,
          "3 <= chi <= 3, so chi = 3")
    check("chi(Manhattan reading) >= 9 (explicit 9-clique M9)",
          len(M9) == 9 and man_ok, "9 <= chi")
    check("the conjectured value 7 is wrong under every standard reading: "
          "5 < 7, 3 < 7, and 9 > 7",
          chi_sq_upper < 7 and chi_euc_upper < 7 and len(M9) > 7,
          "squared -> 5, Euclidean -> 3, Manhattan -> >= 9")

    # ------------------------------------------------------------------
    # 8. Report
    # ------------------------------------------------------------------
    line = "=" * 74
    print(line)
    print("Disproof of conjecture 00000001556 -- reproduction")
    print(line)
    print("\nConjecture: the chromatic number of the planar distance graph")
    print("            G(Z^2, D) with D = {1, 2, 4} is 7.")
    print("Claimed value: 7.  Verdict: FALSE.")
    print("\nDefinitional ambiguity: D is a set of distances.  Two standard")
    print("readings, both covered by the same witness colouring:")
    print("  * squared reading   Dsq : dx^2 + dy^2 in {1,2,4}  (12 vectors)")
    print("  * Euclidean reading Deuc: dx^2 + dy^2 in {1,4,16} (12 vectors)")
    print("  * union Dsq | Deuc                                     (16 vectors)")

    print("\n[1] Forbidden-residue table: c5(x,y) = (x + 2y) mod 5")
    print(f"    {'d=(dx,dy)':>10}  {'reading':>10}  {'dx+2dy':>7}  "
          f"{'mod 5':>5}  {'sq norm':>7}  {'euc len':>7}")
    for (dx, dy) in DUNION:
        in_sq = (dx, dy) in DSQ
        in_eu = (dx, dy) in DEUC
        rd = "both" if in_sq and in_eu else ("squared" if in_sq else "euclid")
        sqn = dx * dx + dy * dy
        euc = {1: "1", 2: "sqrt2", 4: "2", 16: "4"}.get(sqn, "?")
        print(f"    {str((dx, dy)):>10}  {rd:>10}  {dx + 2*dy:>7}  "
              f"{(dx + 2*dy) % 5:>5}  {sqn:>7}  {euc:>7}")
    print("    All 16 residues are nonzero: c5 is proper for the union graph,")
    print("    hence for each reading.  So chi <= 5 < 7.")

    print("\n[2] Brute force: c5 proper on [-200,200]^2 for the union graph,")
    print("    and c3 proper on [-100,100]^2 for the Euclidean reading.")

    print("\n[3] Exact values (clique lower bounds + colouring upper bounds)")
    print("    squared reading   : 5-clique C5 = {(0,0),(+-1,0),(0,+-1)}")
    print("                        + c5 colouring            => chi = 5")
    print("    Euclidean reading : 3-clique C3 = {(0,0),(1,0),(2,0)}")
    print("                        + c3 colouring            => chi = 3")
    print("    union graph       : C5 + c5                    => chi = 5")
    print("    Manhattan (L1)    : 9-clique M9                => chi >= 9")
    print("    In every reading the claimed value 7 is wrong.")

    print("\n[4] Caveats")
    print("    * Reading Z^2 as the continuum R^2 instead of the lattice would")
    print("      change the problem: chi(R^2, {1,2,4}) is not settled by this")
    print("      argument (the chromatic number of the plane is in {5,6,7}).")
    print("      The conjecture is written G(Z^2, D) -- lattice points -- so the")
    print("      refutation applies; the periodic colouring extends to all Z^2")
    print("      by the de Bruijn-Erdos compactness argument, under which the")
    print("      chromatic number of a lattice graph is the sup over finite")
    print("      subgraphs (a finite clique is already a finite subgraph).")
    print("    * 'planar distance graph' names a graph drawn on lattice points,")
    print("      not a planar graph in the graph-theoretic sense.")

    print("\n[5] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000001556 is FALSE.")
        print("  c5(x,y) = (x + 2y) mod 5 is a proper 5-colouring of the union")
        print("  of both standard readings, so chi <= 5 < 7; the exact values")
        print("  are chi = 5 (squared), chi = 3 (Euclidean), and chi >= 9")
        print("  (non-standard Manhattan).  The claimed value 7 fails.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
