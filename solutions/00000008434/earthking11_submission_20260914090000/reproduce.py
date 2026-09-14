#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000008434.

    Definition: The intersection structure of a combinatorial geometry: the
                intersection spectrum of its blocks.
    Conjecture: The intersection spectrum is exactly the set of all integer
                values in the interval [s_0, s_1]; and s_0 = s_1 if and only
                if the design is symmetric.

The conjecture is FALSE.

Reading pinned (the file defines none of its terms; this is the only standard
reading consistent with the wording):

    * "combinatorial geometry" is read as a block design on a finite point
      set, "blocks" as its blocks;
    * the intersection spectrum is the SET
          S = { |B ∩ B'| : B, B' distinct blocks },
      and s_0 = min S, s_1 = max S.

Witness for the failure of clause 1: AG(3,2), the unique 3-(8,4,1) Steiner
quadruple system, i.e. the 14 affine planes {x in F_2^3 : a.x = b}, a != 0,
b in {0,1}.  All C(8,3) = 56 triples lie in exactly one plane, so it is a
genuine 3-design.  Over the C(14,2) = 91 pairs of distinct planes the
intersection sizes are only 0 (7 pairs) and 2 (84 pairs), so S = {0,2}, while
the interval [s_0,s_1] = [0,2] also contains 1, which never occurs.  The
interval is strictly larger than the spectrum.

Bonus: clause 2 fails for 1-designs.  The Pasch configuration is a 1-(6,3,2)
design in which every two blocks meet in exactly one point, so s_0 = s_1 = 1,
yet b = 4 != 6 = v: it is not symmetric.  (For genuine 2-designs clause 2 is a
theorem: a constant pairwise intersection force b = v.)

Python 3 standard library only.  Exits non-zero if any check fails.
"""

from itertools import combinations


# ----------------------------------------------------------------------
# The affine geometry AG(3,2)
# ----------------------------------------------------------------------

def dot(a, x):
    """Dot product in F_2^3, with points/vectors encoded as 3-bit integers."""
    return bin(a & x).count("1") % 2


def affine_planes():
    """The 14 affine 2-planes of F_2^3 as 8-bit point masks."""
    planes = []
    for a in range(1, 8):          # a != 0: seven normal vectors
        for b in (0, 1):
            mask = 0
            for x in range(8):
                if dot(a, x) == b:
                    mask |= 1 << x
            planes.append(mask)
    return planes


def popcount(m):
    return bin(m).count("1")


# The masks pinned in the Lean formalisation, for cross-checking.
PINNED_BLOCKS = [15, 51, 60, 85, 90, 102, 105, 150, 153, 165, 170, 195, 204, 240]

# The Pasch configuration on the 6 points 1..6.
PASCH = [frozenset({1, 2, 3}), frozenset({1, 4, 5}),
         frozenset({2, 4, 6}), frozenset({3, 5, 6})]
PASCH_POINTS = frozenset({1, 2, 3, 4, 5, 6})


def main():
    checks = []
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    # ------------------------------------------------------------------
    # 1. The 14 affine planes of F_2^3
    # ------------------------------------------------------------------
    planes = affine_planes()
    check("AG(3,2) has 14 affine planes",
          len(planes) == 14, f"len = {len(planes)}")
    check("the 14 generated masks equal the pinned list (sorted)",
          sorted(planes) == sorted(PINNED_BLOCKS),
          f"{sorted(planes)}")
    check("all 14 planes have exactly 4 points",
          all(popcount(m) == 4 for m in planes),
          f"sizes = {sorted(set(popcount(m) for m in planes))}")
    check("the 14 planes are pairwise distinct",
          len(set(planes)) == 14, f"distinct = {len(set(planes))}")

    # ------------------------------------------------------------------
    # 2. The 3-(8,4,1) property: every triple is in exactly one plane
    # ------------------------------------------------------------------
    triples = [m for m in range(256) if popcount(m) == 3]
    check("there are C(8,3) = 56 triples of points",
          len(triples) == 56, f"len = {len(triples)}")

    counts = {}
    bad = []
    for T in triples:
        c = sum(1 for B in planes if (T & B) == T)
        counts[c] = counts.get(c, 0) + 1
        if c != 1:
            bad.append((T, c))
    check("every triple lies in exactly one plane (3-(8,4,1) design)",
          not bad,
          "all 56 triples have containment count 1"
          if not bad else f"violations: {bad}")
    check("containment-count distribution over the 56 triples is {1: 56}",
          counts == {1: 56}, f"{counts}")
    # A 3-(8,4,1) design with b = 14 blocks: consistency of the parameters
    # lambda_3 = 1, lambda_2 = (v-2)/(k-2) = 3, lambda_1 = (v-1)(v-2)/((k-1)(k-2)) = 7.
    point_masks = [1 << i for i in range(8)]
    pair_masks = [m for m in range(256) if popcount(m) == 2]
    rep_point = {P: sum(1 for B in planes if (P & B) == P) for P in point_masks}
    rep_pair = {T: sum(1 for B in planes if (T & B) == T) for T in pair_masks}
    check("1-design/2-design parameter consistency: each point in "
          "(8-1)(8-2)/((4-1)(4-2)) = 7 planes, each pair in "
          "(8-2)/(4-2) = 3",
          set(rep_point.values()) == {7} and set(rep_pair.values()) == {3},
          f"point replication {sorted(set(rep_point.values()))}, "
          f"pair replication {sorted(set(rep_pair.values()))}")

    # ------------------------------------------------------------------
    # 3. The intersection spectrum of AG(3,2)
    # ------------------------------------------------------------------
    pairs = list(combinations(range(14), 2))
    check("there are C(14,2) = 91 pairs of distinct blocks",
          len(pairs) == 91, f"len = {len(pairs)}")

    spectrum = []
    for i, j in pairs:
        spectrum.append(popcount(planes[i] & planes[j]))

    hist = {}
    for s in spectrum:
        hist[s] = hist.get(s, 0) + 1

    s0 = min(spectrum)
    s1 = max(spectrum)
    S = set(spectrum)

    check("the spectrum has 91 entries", len(spectrum) == 91,
          f"len = {len(spectrum)}")
    check("the spectrum is exactly {0,2}", S == {0, 2},
          f"S = {sorted(S)}, multiplicities = {dict(sorted(hist.items()))}")
    check("intersection multiplicities are 0:7 and 2:84",
          hist.get(0) == 7 and hist.get(2) == 84 and hist.get(1, 0) == 0,
          f"0:{hist.get(0)}  1:{hist.get(1, 0)}  2:{hist.get(2)}")
    check("s_0 = 0 and s_1 = 2", (s0, s1) == (0, 2),
          f"s_0 = {s0}, s_1 = {s1}")

    interval = set(range(s0, s1 + 1))
    check("the interval [s_0,s_1] = {0,1,2} is strictly larger than the "
          "spectrum: 1 lies in the interval but not in the spectrum",
          interval == {0, 1, 2} and 1 in interval and 1 not in S,
          f"interval = {sorted(interval)}, spectrum = {sorted(S)}, "
          f"missing = {sorted(interval - S)}")
    check("CLAUSE 1 IS FALSE: the spectrum is NOT the set of all integers "
          "in [s_0,s_1]",
          S != interval,
          f"|spectrum| = {len(S)} but |[s_0,s_1]| = {len(interval)}")
    check("the witness is a genuine 3-design, not a degenerate reading",
          len(planes) == 14 and all(popcount(m) == 4 for m in planes)
          and not bad,
          "AG(3,2) is a 3-(8,4,1) design; the refutation does not depend on "
          "reading the conjecture loosely")

    # ------------------------------------------------------------------
    # 4. Bonus: clause 2 fails for 1-designs (Pasch)
    # ------------------------------------------------------------------
    check("Pasch has b = 4 blocks of size 3 on v = 6 points",
          len(PASCH) == 4 and all(len(B) == 3 for B in PASCH)
          and set().union(*PASCH) == PASCH_POINTS,
          f"b = {len(PASCH)}, v = {len(PASCH_POINTS)}")
    r = {P: sum(1 for B in PASCH if P in B) for P in sorted(PASCH_POINTS)}
    check("Pasch is a 1-(6,3,2) design: every point lies in exactly 2 blocks",
          set(r.values()) == {2}, f"replication numbers = {r}")
    pspectrum = [len(A & B) for A, B in combinations(PASCH, 2)]
    check("every pair of Pasch blocks meets in exactly one point",
          set(pspectrum) == {1},
          f"pairwise intersection sizes = {pspectrum}")
    ps0 = min(pspectrum)
    ps1 = max(pspectrum)
    check("Pasch has s_0 = s_1 = 1 (constant intersection)",
          (ps0, ps1) == (1, 1), f"s_0 = {ps0}, s_1 = {ps1}")
    check("Pasch is NOT symmetric: b = 4 != 6 = v",
          len(PASCH) != len(PASCH_POINTS),
          f"b = {len(PASCH)}, v = {len(PASCH_POINTS)}")
    check("CLAUSE 2 IS FALSE for 1-designs: s_0 = s_1 yet the design is not "
          "symmetric",
          ps0 == ps1 and len(PASCH) != len(PASCH_POINTS),
          "s_0 = s_1 = 1, b = 4, v = 6 (a 2-design analogue is a theorem, "
          "so clause 2 only fails in the 1-design generality of the wording)")

    # ------------------------------------------------------------------
    # 5. Report
    # ------------------------------------------------------------------
    line = "=" * 76
    print(line)
    print("Disproof of conjecture 00000008434 -- reproduction")
    print(line)
    print("\nReading pinned: spectrum S = { |B n B'| : B != B' distinct blocks },")
    print("                s_0 = min S, s_1 = max S.")
    print("Claimed value: FALSE.")

    print("\n[1] AG(3,2): the 14 affine planes {x in F_2^3 : a.x = b}, a != 0, b in {0,1}")
    print("    as 8-bit masks (sorted):")
    print(f"    {sorted(planes)}")
    print("    each has 4 points; 3-(8,4,1): all 56 triples in exactly one plane.")

    print("\n[2] The 91-pair intersection spectrum of AG(3,2):")
    print(f"    {'intersection size m':>20}  {'# pairs':>8}  {'in [0,2]?':>9}")
    for m in range(0, 3):
        print(f"    {m:>20}  {hist.get(m, 0):>8}  {'yes':>9}")
    print(f"    {'TOTAL':>20}  {len(spectrum):>8}")
    print(f"    s_0 = min S = {s0},  s_1 = max S = {s1};  S = {sorted(S)};  "
          f"[s_0,s_1] = {sorted(interval)}")
    print("    The value 1 belongs to [0,2] but never occurs: S is a strict")
    print("    subset of [s_0,s_1], so clause 1 of the conjecture is FALSE.")

    print("\n[3] Bonus, clause 2 for 1-designs: the Pasch configuration")
    print("    B = {{1,2,3},{1,4,5},{2,4,6},{3,5,6}} on v = 6 points:")
    print(f"    replication numbers r = {r}  (a 1-(6,3,2) design)")
    print(f"    pairwise intersections = {pspectrum}  =>  s_0 = s_1 = 1")
    print(f"    b = {len(PASCH)} != {len(PASCH_POINTS)} = v  =>  NOT symmetric")
    print("    So 's_0 = s_1 iff symmetric' fails for 1-designs.")

    print("\n[4] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000008434 is FALSE.")
        print("  AG(3,2) is a genuine 3-(8,4,1) design whose intersection")
        print("  spectrum is {0,2}, but [s_0,s_1] = [0,2] also contains 1.")
        print("  Clause 2 additionally fails for 1-designs (Pasch).")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
