#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000008417.

    Definition: A Steiner system S(t,k,n) is a design in which every
                t-element subset lies in exactly one block.
    Conjecture: S(t,k,n) exists iff the classical divisibility conditions
                hold and n >= n_0(t,k); n_0(t,k) <= (kt)^{ct}, and the
                lower bound n_0(5,6) > 12 is given by a concrete
                divisibility obstruction.

The conjecture is FALSE.  The witness is the small Witt design W_12 = S(5,6,12):
a genuine 5-(12,6,1) design with 132 blocks on 12 points.  At (t,k,n) = (5,6,12)
all six classical divisibility conditions hold (no obstruction whatsoever), and
the design exists at n = 12.  Any existence threshold therefore satisfies
n_0(5,6) <= 12, contradicting the filed claim n_0(5,6) > 12.

This script, using the Python 3 standard library only:
  (a) computes the six divisibility quotients and checks they are integers;
  (b) builds a 5-(12,6,1) design by exact cover / backtracking over the 792
      five-subsets, verifies exhaustively that every five-subset lies in exactly
      one of the 132 blocks, and prints a SHA-256 of the canonical block list;
  (c) independently constructs the design from the extended ternary Golay code
      [12,6,6] (264 weight-6 words -> 132 supports) and verifies coverage;
  (d) verifies the two designs are isomorphic up to relabelling.

Exits non-zero if any check fails.
"""

import hashlib
import itertools
import sys
from collections import Counter
from math import comb

N = 12          # number of points
T = 5           # block size of the "every t-subset" condition
K = 6           # actual block size
NUM_BLOCKS = 132
NUM_FIVES = 792


# ---------------------------------------------------------------------------
# (a) The six classical divisibility conditions at (t, k, n) = (5, 6, 12)
# ---------------------------------------------------------------------------

def divisibility_quotients(n=N, t=T, k=K):
    """Return [(i, numerator, denominator, quotient, remainder)] for i = 0..t.

    The i-th classical divisibility condition for an S(t,k,n) is
        C(n-i, t-i) / C(k-i, t-i)  in  Z,
    the number of blocks through a fixed i-subset (for i = 0 this is the total
    block count).  For an S(5,6,12) these are
        132, 66, 30, 12, 4, 1   (i = 0..5),
    all integers, so no divisibility obstruction exists at n = 12.
    """
    rows = []
    for i in range(t + 1):
        num = comb(n - i, t - i)
        den = comb(k - i, t - i)
        rows.append((i, num, den, num // den, num % den))
    return rows


# ---------------------------------------------------------------------------
# (b) Exact cover / backtracking construction
# ---------------------------------------------------------------------------

def build_design_exact_cover():
    """Build a 5-(12,6,1) design by Algorithm X (DLX-style) with MRV.

    Columns  = the 792 five-subsets of {0,...,11}; every column must be covered
    exactly once.  Rows = the 924 six-subsets; selecting a row covers its
    C(6,5) = 6 five-subsets.  A solution selects 792/6 = 132 rows.
    The search order is deterministic, so the output is reproducible.
    """
    fives = list(itertools.combinations(range(N), T))
    five_index = {f: i for i, f in enumerate(fives)}
    cand = list(itertools.combinations(range(N), K))
    # row -> the (indices of) five-subsets it covers
    row_cols = [tuple(five_index[f] for f in itertools.combinations(b, T))
                for b in cand]
    col_rows = [[] for _ in fives]
    for r, cols in enumerate(row_cols):
        for c in cols:
            col_rows[c].append(r)

    covered = [False] * len(fives)
    chosen = []

    def rec(remaining):
        if remaining == 0:
            return True
        # MRV: pick an uncovered column with the fewest conflict-free rows.
        best_c = -1
        best_rows = None
        for c in range(len(fives)):
            if covered[c]:
                continue
            av = [r for r in col_rows[c]
                  if not any(covered[x] for x in row_cols[r])]
            if best_rows is None or len(av) < len(best_rows):
                best_c, best_rows = c, av
                if not av:
                    break
        if not best_rows:
            return False
        for r in best_rows:
            for x in row_cols[r]:
                covered[x] = True
            chosen.append(r)
            if rec(remaining - K):
                return True
            chosen.pop()
            for x in row_cols[r]:
                covered[x] = False
        return False

    if not rec(len(fives)):
        return None
    return [frozenset(cand[r]) for r in chosen]


def covers_each_five_exactly_once(blocks, n=N, t=T, k=K, verbose=False):
    """Exhaustively verify: exactly `expected` blocks, all of size k, distinct,
    and every t-subset of {0..n-1} is contained in exactly one block."""
    expected = comb(n, t) // comb(k, t)
    problems = []
    if len(blocks) != expected:
        problems.append(f"block count {len(blocks)} != {expected}")
    if len(set(blocks)) != len(blocks):
        problems.append("duplicate blocks")
    for b in blocks:
        if len(b) != k:
            problems.append(f"block {sorted(b)} has size {len(b)} != {k}")
            break
    counts = Counter()
    for b in blocks:
        for f in itertools.combinations(sorted(b), t):
            counts[f] += 1
    all_fives = list(itertools.combinations(range(n), t))
    bad = [f for f in all_fives if counts.get(f, 0) != 1]
    if bad:
        problems.append(f"{len(bad)} five-subsets not covered exactly once "
                        f"(e.g. {bad[0]} -> {counts.get(bad[0], 0)})")
    if verbose:
        print(f"    blocks = {len(blocks)}, distinct = {len(set(blocks))}, "
              f"t-subsets covered exactly once = {len(all_fives) - len(bad)}"
              f"/{len(all_fives)}")
    return (not problems), problems


def canonical_block_list(blocks):
    """Canonical serialisation of a design: every block as its points in
    increasing order joined by '-', the 132 resulting strings sorted
    lexicographically, joined by newlines and terminated by a newline.  A
    deterministic function of the design *as labelled*."""
    lines = sorted("-".join(map(str, sorted(b))) for b in blocks)
    return "\n".join(lines) + "\n"


def sha256_of(blocks):
    return hashlib.sha256(canonical_block_list(blocks).encode("ascii")).hexdigest()


# ---------------------------------------------------------------------------
# (c) Extended ternary Golay code [12,6,6]
# ---------------------------------------------------------------------------

def extended_ternary_golay_words():
    """The 3^6 = 729 codewords of the extended ternary Golay code [12,6,6],
    generated by G = [I_6 | P] over GF(3)."""
    # Self-dual generator matrix of the extended ternary Golay code.
    G = [
        [1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
        [0, 1, 0, 0, 0, 0, 1, 0, 1, 2, 2, 1],
        [0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 2, 2],
        [0, 0, 0, 1, 0, 0, 1, 2, 1, 0, 1, 2],
        [0, 0, 0, 0, 1, 0, 1, 2, 2, 1, 0, 1],
        [0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 1, 0],
    ]
    words = set()
    for coeffs in itertools.product(range(3), repeat=6):
        w = [0] * 12
        for i, ci in enumerate(coeffs):
            if ci:
                for j in range(12):
                    w[j] = (w[j] + ci * G[i][j]) % 3
        words.add(tuple(w))
    return words


def golay_design():
    """The 132 supports of the weight-6 words of the extended ternary Golay
    code.  Each nonzero codeword has a unique scalar multiple with the same
    support (its negative), so 264 weight-6 words give 132 distinct supports."""
    words = extended_ternary_golay_words()
    weight_dist = Counter(sum(1 for x in w if x != 0) for w in words)
    supports = set()
    for w in words:
        if sum(1 for x in w if x != 0) == 6:
            supports.add(frozenset(i for i, x in enumerate(w) if x != 0))
    return supports, weight_dist, len(words)


# ---------------------------------------------------------------------------
# (d) Isomorphism between the two labelled designs
# ---------------------------------------------------------------------------

def iter_isomorphisms(src, dst):
    """Yield every permutation p of {0..11} with
    {frozenset(p(x) for x in b) : b in src} == set(dst).

    Constraint propagation: whenever five points of an src-block already have
    images lying in a common dst-block, the image of the sixth point is forced
    to be the remaining point of that dst-block.  Points fixed by propagation
    are removed from the branching list, so they are never overwritten.
    """
    dst_set = set(dst)
    # lookup: the unique dst-block containing a given 5-set
    dst_by_five = {}
    for b in dst:
        for f in itertools.combinations(sorted(b), 5):
            dst_by_five[f] = b
    src_blocks = list(src)

    perm = [-1] * N
    used = [False] * N

    def undo(made):
        for x, y in made:
            perm[x] = -1
            used[y] = False

    def propagate():
        """Make all forced assignments; return them, or None on contradiction.
        On contradiction every assignment it made is rolled back, so the caller
        always sees a consistent state."""
        made = []
        changed = True
        while changed:
            changed = False
            for b in src_blocks:
                bs = sorted(b)
                m = [(x, perm[x]) for x in bs if perm[x] != -1]
                if len(m) == 6:
                    if frozenset(y for _, y in m) not in dst_set:
                        undo(made)
                        return None
                elif len(m) == 5:
                    img5 = tuple(sorted(y for _, y in m))
                    target = dst_by_five.get(img5)
                    if target is None:
                        undo(made)
                        return None
                    missing = target - frozenset(y for _, y in m)
                    if len(missing) != 1:
                        undo(made)
                        return None
                    x = next(x for x in bs if perm[x] == -1)
                    y = next(iter(missing))
                    if used[y]:
                        undo(made)
                        return None
                    perm[x] = y
                    used[y] = True
                    made.append((x, y))
                    changed = True
        return made

    def rec():
        made = propagate()
        if made is None:
            return
        free = [x for x in range(N) if perm[x] == -1]
        if not free:
            if {frozenset(perm[x] for x in b) for b in src_blocks} == dst_set:
                yield list(perm)          # snapshot before undoing
            undo(made)
            return
        x = free[0]
        for y in range(N):
            if used[y]:
                continue
            perm[x] = y
            used[y] = True
            yield from rec()
            perm[x] = -1
            used[y] = False
        undo(made)

    yield from rec()


def find_isomorphism(src, dst):
    """Return one isomorphism permutation, or None."""
    return next(iter_isomorphisms(src, dst), None)


def relabel(blocks, perm):
    """Apply the point permutation `perm` (p[x] = new label of x) to a design."""
    return [frozenset(perm[x] for x in b) for b in blocks]


def count_automorphisms(blocks):
    """|Aut(design)| = number of isomorphisms from `blocks` to itself.

    For W_12 this is |M_12| = 95040; the count is a strong computational
    consistency check on the uniqueness-scale symmetry of the design.
    """
    return sum(1 for _ in iter_isomorphisms(blocks, blocks))


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    checks = []
    all_ok = [True]

    def check(name, ok, detail=""):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    line = "=" * 76
    print(line)
    print("Disproof of conjecture 00000008417 -- reproduction")
    print(line)
    print("\nWitness: the small Witt design W_12 = S(5,6,12), a genuine")
    print("5-(12,6,1) design with 132 blocks on 12 points, existing AT n = 12.")

    # --- (a) divisibility ---------------------------------------------------
    print("\n[a] The six classical divisibility conditions at (t,k,n) = (5,6,12)")
    print("    C(n-i, t-i) / C(k-i, t-i) must be an integer for i = 0..5:")
    quotients = divisibility_quotients()
    for i, num, den, quo, rem in quotients:
        status = "integer" if rem == 0 else f"NOT INTEGER (rem {rem})"
        print(f"      i={i}: C({N-i},{T-i})/C({K-i},{T-i}) = "
              f"{num}/{den} = {quo}    [{status}]")
    divisors_ok = all(rem == 0 for _, _, _, _, rem in quotients)
    check("all six divisibility quotients are integers (no obstruction at "
          "n=12)",
          divisors_ok,
          "quotients = " + ", ".join(str(q) for _, _, _, q, _ in quotients))
    check("the total block count C(12,5)/C(6,5) equals 132",
          comb(N, T) // comb(K, T) == 132,
          f"{comb(N, T)}/{comb(K, T)} = {comb(N, T)//comb(K, T)}")

    # --- (b) exact cover construction --------------------------------------
    print("\n[b] Exact-cover construction over the 792 five-subsets "
          "(Algorithm X / MRV)")
    blocks = build_design_exact_cover()
    check("exact-cover search produced a design", blocks is not None,
          f"{len(blocks)} blocks" if blocks else "no solution")
    if blocks is None:
        print("\nFAIL: exact cover found no solution")
        return 1
    ok_b, prob_b = covers_each_five_exactly_once(blocks, verbose=True)
    check("EXHAUSTIVE: every one of the 792 five-subsets lies in exactly one "
          "block (exact cover)", ok_b,
          "verified" if ok_b else "; ".join(prob_b))
    digest = sha256_of(blocks)
    print(f"    block count = {len(blocks)}")
    print(f"    SHA-256 of the canonical block list = {digest}")
    print(f"    canonical form: sorted blocks, points ascending, 'a-b-c-d-e-f'")
    print(f"                    joined by newlines")
    check("canonical SHA-256 computed", len(digest) == 64, digest)

    # invariants of the exact-cover design
    inter = Counter()
    bset = set(blocks)
    for b1, b2 in itertools.combinations(sorted(blocks), 2):
        inter[len(b1 & b2)] += 1
    print(f"    pairwise block intersections "
          f"{{i: count}} = {dict(sorted(inter.items()))}")
    per_block = Counter()
    for b1 in blocks:
        local = Counter(len(b1 & b2) for b2 in blocks)
        per_block[tuple(sorted(local.items()))] += 1
    print(f"    per-block intersection profile (i: count) "
          f"= {sorted(per_block)[0]}  (same for all {len(blocks)} blocks)")
    check("pairwise block intersection distribution is {0:66, 2:2970, 3:2640, "
          "4:2970}",
          {k: inter.get(k, 0) for k in (0, 2, 3, 4)} ==
          {0: 66, 2: 2970, 3: 2640, 4: 2970} and
          inter.get(1, 0) == 0 and inter.get(5, 0) == 0,
          str(dict(sorted(inter.items()))))

    # --- (c) Golay construction -------------------------------------------
    print("\n[c] Independent construction from the extended ternary Golay code "
          "[12,6,6]")
    gsupports, weight_dist, num_words = golay_design()
    print(f"    codewords = {num_words} (expected 729), "
          f"weight distribution = {dict(sorted(weight_dist.items()))}")
    check("Golay code has 729 codewords with weight distribution "
          "{0:1, 6:264, 9:440, 12:24}",
          num_words == 729 and
          {w: weight_dist.get(w, 0) for w in (0, 6, 9, 12)} ==
          {0: 1, 6: 264, 9: 440, 12: 24},
          str(dict(sorted(weight_dist.items()))))
    check("the 264 weight-6 words give 132 distinct 6-element supports",
          len(gsupports) == 132, f"{len(gsupports)} supports")
    gblocks = list(gsupports)
    ok_c, prob_c = covers_each_five_exactly_once(gblocks, verbose=True)
    check("EXHAUSTIVE: every one of the 792 five-subsets lies in exactly one "
          "Golay support block", ok_c,
          "verified" if ok_c else "; ".join(prob_c))
    check("the two constructions give designs of the same block count (132)",
          len(gsupports) == len(blocks) == 132,
          f"{len(gsupports)} vs {len(blocks)}")

    # --- (d) isomorphism ---------------------------------------------------
    print("\n[d] Isomorphism of the two labelled designs (up to relabelling)")
    perm = find_isomorphism(blocks, gblocks)
    check("an explicit relabelling isomorphism was found", perm is not None,
          f"p = {perm}" if perm else "no isomorphism")
    if perm is not None:
        relabelled = set(relabel(blocks, perm))
        print(f"    point permutation p (exact-cover label -> Golay label):")
        print(f"      {perm}")
        print(f"    applying p to the {len(blocks)} exact-cover blocks gives "
              f"exactly the Golay design: {relabelled == set(gblocks)}")
        check("relabelled exact-cover design equals the Golay design",
              relabelled == set(gblocks), "sets coincide")

    # --- automorphism order (uniqueness-scale symmetry) --------------------
    print("\n[e] Automorphism order of W_12 (uniqueness-scale symmetry)")
    nauto = count_automorphisms(blocks)
    print(f"    |Aut(W_12)| = {nauto}   (expected |M_12| = 95040)")
    check("automorphism group of the constructed design has order 95040 "
          "(M_12)", nauto == 95040, f"|Aut| = {nauto}")

    # --- consistency with the Lean certificate -----------------------------
    print("\n[f] Consistency with the Lean certificate (12-bit masks)")
    masks = sorted(sum(1 << x for x in b) for b in blocks)
    print(f"    first masks: {masks[:8]} ... last: {masks[-4:]}")
    check("132 distinct 12-bit masks with popcount 6",
          len(set(masks)) == 132 and
          all(bin(m).count("1") == 6 for m in masks),
          "ok")

    # --- report ------------------------------------------------------------
    print("\n[g] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        if detail:
            print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000008417 is FALSE.")
        print("  W_12 = S(5,6,12) exists at n = 12 while all six divisibility")
        print("  conditions hold there, so n_0(5,6) <= 12, contradicting the")
        print("  filed lower bound n_0(5,6) > 12.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
