#!/usr/bin/env python3
"""Reproduce the refutation of conjecture 00000008419.

    Conjecture (as filed):
      "For a code with dual distance d^perp at least t+1, all minimal codewords
       form t-(n,w,lambda) designs; the converse of the Assmus-Mattson theorem
       holds at weight 4, and the minimal failure of the converse occurs at
       d^perp = 5."

The conjecture is FALSE.  This script builds binary linear codes from their
generator matrices over F_2 (integer bitsets), computes the minimum distance and
the dual distance, enumerates the minimum-weight codewords and their supports,
and tests the t-design property (all t-subsets contained in the same number of
blocks).

Main witness (W1): the binary [5,2,3] code

    C = {00000, 01101, 10011, 11110},   generator rows 01101, 10011,

with minimum distance d = 3 and dual distance d^perp = 2.  Taking t = 1 the
hypothesis d^perp >= t+1 reads 2 >= 2 and holds, but the two minimum-weight
codewords have supports {2,3,5} and {1,4,5}; coordinate 5 lies in both blocks
(multiplicity 2) while coordinates 1,2,3,4 lie in one block each (multiplicity
1).  Hence they do NOT form a 1-(5,3,lambda) design, and the first clause of the
conjecture fails already at d^perp = 2.  In particular the claimed "minimal
failure at d^perp = 5" is false: failures occur at d^perp = 2.

Further witnesses:
    W2  binary [7,2,4] code, d = 4 (minimum weight 4), d^perp = 2: the two
        weight-4 minimum-weight codewords fail to form a 1-design.  This shows
        the failure is not an artefact of minimum weight 3 and persists under
        the "weight 4" reading.
    W3  the Hamming [7,4,3] code, d^perp = 4: the 7 minimum-weight codewords
        form 1- and 2-designs but not a 3-design, although d^perp = 4 >= 3+1.
        This is a failure at d^perp = 4.
    W4  a binary [6,3,3] code, d^perp = 3: the 4 minimum-weight codewords form a
        1-design but not a 2-design, although d^perp = 3 >= 2+1.  Failure at
        t = 2.
    W5  the extended Hamming [8,4,4] code (d^perp = 4): its 14 minimum-weight
        codewords DO form a 3-design.  This is a control showing the design
        tester is not vacuously negative.

Standard library only.  Python 3.8+.  Exits non-zero if any check fails.
"""

from itertools import combinations


# ----------------------------------------------------------------------
# linear algebra over F_2 on integer bitsets
# ----------------------------------------------------------------------

def parse_word(s):
    """Parse a coordinate-first binary string into an integer bitset.

    The i-th character (0-based) is coordinate i+1 and corresponds to bit
    (n-1-i), so that bit 0 is the last coordinate.  `support` inverts this.
    """
    n = len(s)
    x = 0
    for i, ch in enumerate(s):
        if ch == "1":
            x |= 1 << (n - 1 - i)
    return x


def span(gens):
    """The F_2-span of a list of integer bitsets."""
    C = [0]
    for g in gens:
        C = C + [c ^ g for c in C]
    return sorted(set(C))


def weight(x):
    return bin(x).count("1")


def support(x, n):
    """Support of a word as a sorted list of 1-based coordinates."""
    return sorted(i + 1 for i in range(n) if (x >> (n - 1 - i)) & 1)


def dual_code(C, n):
    """All nonzero words orthogonal (mod 2) to every word of C."""
    return [y for y in range(1, 1 << n)
            if all(((y & c).bit_count() & 1) == 0 for c in C)]


def min_distance(C):
    return min(weight(x) for x in C if x != 0)


def design_counts(blocks, n, t):
    """For every t-subset of coordinates, the number of blocks containing it."""
    return {(T): sum(1 for b in blocks if set(T) <= set(b))
            for T in combinations(range(1, n + 1), t)}


def is_t_design(blocks, n, t):
    """All t-subsets contained in the same number of blocks (constant block size)."""
    if not blocks:
        return False
    if len({len(b) for b in blocks}) != 1:
        return False
    return len(set(design_counts(blocks, n, t).values())) == 1


def analyse(name, gen_strings, expected):
    """Analyse one code and check it against `expected`; return (facts, checks)."""
    n = len(gen_strings[0])
    gens = [parse_word(s) for s in gen_strings]
    C = span(gens)
    nonzero = [x for x in C if x]
    d = min_distance(C)
    D = dual_code(C, n)
    dperp = min(weight(y) for y in D) if D else None

    min_words = [x for x in nonzero if weight(x) == d]
    blocks = [support(x, n) for x in min_words]
    mult = [sum(1 for b in blocks if i in b) for i in range(1, n + 1)]

    # design verdict for every t permitted by the hypothesis d^perp >= t+1
    design = {}
    for t in range(1, dperp):
        design[t] = is_t_design(blocks, n, t)

    facts = dict(name=name, n=n, k=len(gens), gens=gen_strings, C=C, d=d,
                 dperp=dperp, min_words=min_words, blocks=blocks, mult=mult,
                 design=design)

    checks = []

    def check(label, ok, detail=""):
        checks.append((f"{name}: {label}", bool(ok), detail))

    check("minimum distance d", d == expected["d"], f"d = {d}")
    check("dual distance d^perp", dperp == expected["dperp"], f"d^perp = {dperp}")
    if expected["blocks"] is None:
        check("minimum-weight codewords (multiplicity only)",
              len(min_words) == sum(mult) // d if d else True,
              f"{len(min_words)} blocks, supports = {[sorted(b) for b in blocks]}")
    else:
        check("minimum-weight codewords",
              sorted(tuple(sorted(b)) for b in blocks) ==
              sorted(tuple(sorted(b)) for b in expected["blocks"]),
              f"supports = {[sorted(b) for b in blocks]}")
    check("point multiplicities",
          mult == expected["mult"], f"multiplicities = {mult}")
    for t, want in expected["design"].items():
        got = design[t]
        check(f"t={t}: hypothesis d^perp={dperp} >= t+1={t + 1} holds",
              dperp >= t + 1, f"{dperp} >= {t + 1}")
        check(f"t={t}: t-design property", got == want,
              f"{t}-design = {got} (expected {want})")
    return facts, checks


# ----------------------------------------------------------------------
# the codes
# ----------------------------------------------------------------------

CODES = [
    # W1: primary witness, the binary [5,2,3] code
    ("W1 [5,2,3] C={00000,01101,10011,11110}", ["01101", "10011"],
     dict(d=3, dperp=2, blocks=[(2, 3, 5), (1, 4, 5)], mult=[1, 1, 1, 1, 2],
          design={1: False})),
    # W2: minimum weight 4
    ("W2 [7,2,4] span{1110001,1001110}", ["1110001", "1001110"],
     dict(d=4, dperp=2, blocks=[(1, 4, 5, 6), (1, 2, 3, 7)],
          mult=[2, 1, 1, 1, 1, 1, 1], design={1: False})),
    # W3: Hamming [7,4,3]
    ("W3 Hamming [7,4,3]", ["1000011", "0100101", "0010110", "0001111"],
     dict(d=3, dperp=4,
          blocks=[(3, 5, 6), (3, 4, 7), (2, 5, 7), (2, 4, 6), (1, 6, 7),
                  (1, 4, 5), (1, 2, 3)],
          mult=[3, 3, 3, 3, 3, 3, 3], design={1: True, 2: True, 3: False})),
    # W4: [6,3,3]
    ("W4 [6,3,3] span{110001,101010,011100}", ["110001", "101010", "011100"],
     dict(d=3, dperp=3,
          blocks=[(4, 5, 6), (2, 3, 4), (1, 3, 5), (1, 2, 6)],
          mult=[2, 2, 2, 2, 2, 2], design={1: True, 2: False})),
    # W5: control
    ("W5 ext. Hamming [8,4,4] (control)",
     ["11111111", "00001111", "00110011", "01010101"],
     dict(d=4, dperp=4, mult=[7] * 8, design={1: True, 2: True, 3: True},
          blocks=None)),
]

# W5 expected blocks are checked only by multiplicity (14 blocks, each point 7x).
CODES[4][2]["blocks"] = None


def main():
    line = "=" * 74
    print(line)
    print("Refutation of conjecture 00000008419 -- reproduction")
    print(line)

    all_checks = []
    facts_by_name = {}

    for name, gens, expected in CODES:
        facts, checks = analyse(name, gens, expected)
        facts_by_name[name] = facts
        all_checks.extend(checks)

        print(f"\n{name}")
        print(f"  n = {facts['n']}, k = {facts['k']}, "
              f"|C| = {len(facts['C'])}, d = {facts['d']}, d^perp = {facts['dperp']}")
        print(f"  generator rows: {facts['gens']}")
        print(f"  codewords: {[format(x, '0%db' % facts['n']) for x in facts['C']]}")
        print(f"  minimum-weight codewords ({len(facts['min_words'])}):")
        for x, b in zip(facts["min_words"], facts["blocks"]):
            print(f"      {format(x, '0%db' % facts['n'])}  support {b}")
        print(f"  point multiplicities 1..{facts['n']}: {facts['mult']}")
        for t in sorted(facts["design"]):
            counts = sorted(set(design_counts(facts["blocks"], facts["n"], t).values()))
            print(f"      t = {t}: d^perp = {facts['dperp']} >= {t + 1} holds; "
                  f"{t}-design? {facts['design'][t]}  (counts take values {counts})")

    # ------------------------------------------------------------------
    # the refutation
    # ------------------------------------------------------------------
    w1 = facts_by_name["W1 [5,2,3] C={00000,01101,10011,11110}"]
    w2 = facts_by_name["W2 [7,2,4] span{1110001,1001110}"]
    w3 = facts_by_name["W3 Hamming [7,4,3]"]
    w4 = facts_by_name["W4 [6,3,3] span{110001,101010,011100}"]
    w5 = facts_by_name["W5 ext. Hamming [8,4,4] (control)"]

    extra = []

    def check(label, ok, detail=""):
        extra.append((label, bool(ok), detail))

    # W1 is the main witness: the conjecture's hypothesis holds at t = 1 but the
    # minimum-weight codewords do not form a 1-design.
    check("W1 refutes clause 1 at (d^perp, t) = (2, 1): hypothesis holds, "
          "1-design fails",
          w1["dperp"] >= 1 + 1 and w1["design"][1] is False,
          f"d^perp = {w1['dperp']} >= 2, 1-design = {w1['design'][1]}, "
          f"multiplicities = {w1['mult']}")

    # The supports are exactly {2,3,5} and {1,4,5}, and coordinate 5 has
    # multiplicity 2 while the others have multiplicity 1.
    check("W1 supports are {2,3,5} and {1,4,5}",
          sorted(tuple(sorted(b)) for b in w1["blocks"]) == [(1, 4, 5), (2, 3, 5)],
          f"{[sorted(b) for b in w1['blocks']]}")
    check("W1 coordinate 5 has multiplicity 2, coordinates 1-4 have multiplicity 1",
          w1["mult"][4] == 2 and w1["mult"][:4] == [1, 1, 1, 1],
          f"multiplicities = {w1['mult']}")

    # "Minimal failure at d^perp = 5" is false: failures occur at d^perp = 2.
    failures = []
    for facts in (w1, w2, w3, w4):
        for t, ok in sorted(facts["design"].items()):
            if ok is False and facts["dperp"] >= t + 1:
                failures.append((facts["name"], facts["dperp"], t))
                break
    check("failures exist at d^perp < 5, so the minimal failure is not d^perp = 5",
          any(dp < 5 for _, dp, _ in failures),
          f"failures at {failures}")
    check("in particular the minimal failure occurs at d^perp = 2 (W1)",
          min(dp for _, dp, _ in failures) == 2,
          f"smallest failing d^perp = {min(dp for _, dp, _ in failures)}")

    # The failure persists for minimum weight 4 (W2) and at t = 2 (W4) and
    # d^perp = 4 (W3).
    check("failure persists when the minimum weight is 4 (W2)",
          w2["d"] == 4 and w2["dperp"] >= 2 and w2["design"][1] is False,
          f"W2: d = {w2['d']}, d^perp = {w2['dperp']}, 1-design = {w2['design'][1]}")
    check("failure also occurs at t = 2 (W4)",
          w4["dperp"] >= 3 and w4["design"][2] is False,
          f"W4: d^perp = {w4['dperp']}, 2-design = {w4['design'][2]}")
    check("failure also occurs at d^perp = 4 (W3, t = 3)",
          w3["dperp"] == 4 and w3["design"][3] is False,
          f"W3: d^perp = {w3['dperp']}, 3-design = {w3['design'][3]}")

    # Control: the design tester can say "yes".
    check("control W5: extended Hamming [8,4,4] weight-4 words DO form a 3-design",
          all(w5["design"][t] is True for t in (1, 2, 3)),
          f"W5 design verdicts = {w5['design']}")

    # Assmus-Mattson itself is not contradicted: W1 fails AM's extra weight
    # condition for t = 1 (number of weights of C^perp in {1,...,n-t} must be
    # at most d - t).
    n1, d1 = w1["n"], w1["d"]
    D1 = dual_code([parse_word(s) for s in w1["gens"]], n1)
    weight_set = sorted(set(weight(y) for y in D1))
    count_low = sum(1 for w in weight_set if w <= n1 - 1)
    check("W1 violates the Assmus-Mattson weight condition for t = 1, so the "
          "AM theorem itself is not contradicted",
          count_low > d1 - 1,
          f"weights of C^perp = {weight_set}; #{{w <= n-t = {n1 - 1}}} = "
          f"{count_low} > d - t = {d1 - 1}")

    # ------------------------------------------------------------------
    # report
    # ------------------------------------------------------------------
    print("\n" + line)
    print("Checks")
    ok_all = True
    for name, ok, detail in all_checks + extra:
        mark = "ok  " if ok else "FAIL"
        ok_all = ok_all and ok
        print(f"  [{mark}] {name}")
        if detail:
            print(f"          {detail}")
    print(line)
    if ok_all:
        print("PASS: the binary [5,2,3] code refutes conjecture 00000008419.")
        print("  d = 3, d^perp = 2; at t = 1 the hypothesis d^perp >= t+1 holds,")
        print("  yet the minimum-weight supports {2,3,5}, {1,4,5} are not a")
        print("  1-design (coordinate 5 has multiplicity 2, the others 1).")
        print("  Failures also occur at d^perp = 3, 4 and at minimum weight 4, so")
        print("  the claimed minimal failure at d^perp = 5 is false.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
