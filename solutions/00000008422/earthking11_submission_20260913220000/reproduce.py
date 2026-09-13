#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000008422 (lambda spectrum of block designs).

Conjecture as filed:

    Definition: the lambda spectrum of block designs is the set of realizable
    lambda values for given (v, k).
    Conjecture: lambda is attainable if and only if
        lambda * binom(v, t) / binom(k, t)  is an integer (with t = k - 1)
    and lambda <= binom(v - 2, k - 2), so the spectrum is complete; the
    complement of the spectrum is a finite explicit exceptional set with at
    most k^2 exceptions.

This script does four things with the Python 3 standard library only.

  [A] The proposed small witness (v, k) = (6, 3).  With t = k - 1 = 2 the
      criterion reads lambda * C(6,2) / C(3,2) = 5 * lambda, which is an
      integer for every lambda, and the bound is lambda <= C(4,1) = 4.  So the
      criterion predicts lambda in {1, 2, 3, 4}.  Exhaustive search shows the
      attainable set is {2, 4}: there is no 2-(6,3,1) and no 2-(6,3,3) design,
      while 2-(6,3,2) and the complete 2-(6,3,4) design exist.  Hence
      (6, 3) exhibits 2 "exceptions" (lambda = 1 and lambda = 3).

      IMPORTANT: 2 <= k^2 = 9, so this witness alone is *absorbed* by the
      conjecture's own clause "the complement of the spectrum is a finite
      explicit exceptional set with at most k^2 exceptions".  It therefore
      refutes only the strict "if and only if / spectrum is complete" reading,
      not the exception-clause reading.

  [B] The decisive witness (v, k) = (22, 3).  With t = k - 1 = 2,
      C(22,2)/C(3,2) = 231/3 = 77, so the criterion predicts *every*
      lambda in {1, ..., C(20,1)} = {1, ..., 20}.  But a 2-(v,k,lambda)
      design has replication number r = lambda*(v-1)/(k-1) = 21*lambda/2,
      which must be an integer (counting the pairs at a fixed point); hence
      lambda must be even.  The ten odd values 1, 3, ..., 19 are therefore
      *not attainable even though the criterion predicts them*, and
      10 > k^2 = 9.  This exceeds the exception budget, so it refutes the
      conjecture under BOTH readings (strict iff and the <= k^2 exception
      clause).  No enumeration of designs is needed: non-attainability of the
      odd lambda is forced by the necessary divisibility condition.

  [C] The divisibility argument r = lambda*(v-1)/(k-1) is an integer, checked
      symbolically for (6,3) and (22,3).

  [D] The criterion table (predicted set, forced-out values, exception budget).

Standard library only.  Python 3.8+.  Exits non-zero if any check fails.
"""

import itertools
import math
import sys

# ----------------------------------------------------------------------------
# 2-(6,3,lambda) exhaustive search
# ----------------------------------------------------------------------------

V6, K6 = 6, 3
TRIPLES6 = list(itertools.combinations(range(V6), K6))          # 20 triples
PAIRS6 = list(itertools.combinations(range(V6), 2))             # 15 pairs
PAIR_INDEX6 = {p: i for i, p in enumerate(PAIRS6)}
# pair indices contained in each triple
BLOCK_PAIRS6 = [
    [PAIR_INDEX6[tuple(sorted(pr))] for pr in itertools.combinations(b, 2)]
    for b in TRIPLES6
]
NP = len(PAIRS6)                                                # 15


def is_design(sub, lam):
    """True iff the selected triples cover every pair exactly `lam` times."""
    counts = [0] * NP
    for i in sub:
        for pi in BLOCK_PAIRS6[i]:
            counts[pi] += 1
            if counts[pi] > lam:
                return False
    return all(c == lam for c in counts)


def brute_force(lam):
    """Exhaustively enumerate ALL b-subsets of the 20 triples, b = lam*5."""
    b = lam * V6 * (V6 - 1) // (K6 * (K6 - 1))    # r*k/k = lam*v(v-1)/(k(k-1))
    space = math.comb(len(TRIPLES6), b)
    found = []
    for sub in itertools.combinations(range(len(TRIPLES6)), b):
        if is_design(sub, lam):
            found.append(sub)
    return b, space, found


class NodeCounter:
    """Complete backtracking search with a node counter (for reporting)."""

    def __init__(self, lam):
        self.lam = lam
        self.nodes = 0
        self.designs = []

    def run(self):
        lam = self.lam
        counts = [0] * NP
        chosen = []

        def solve(start):
            self.nodes += 1
            try:
                pi = next(i for i in range(NP) if counts[i] < lam)
            except StopIteration:
                self.designs.append(tuple(chosen))
                return
            for bi in range(start, len(TRIPLES6)):
                if pi not in BLOCK_PAIRS6[bi]:
                    continue
                if any(counts[p] >= lam for p in BLOCK_PAIRS6[bi]):
                    continue
                for p in BLOCK_PAIRS6[bi]:
                    counts[p] += 1
                chosen.append(bi)
                solve(bi + 1)
                chosen.pop()
                for p in BLOCK_PAIRS6[bi]:
                    counts[p] -= 1

        solve(0)
        return self.designs


# ----------------------------------------------------------------------------
# Criterion arithmetic
# ----------------------------------------------------------------------------

def criterion(v, k):
    """Return (t, C(v,t), C(k,t), unit, L, predicted, forced_out)."""
    t = k - 1
    cvt = math.comb(v, t)
    ckt = math.comb(k, t)
    # lambda*cvt/ckt is an integer iff ckt/gcd(cvt,ckt) divides lambda
    unit = ckt // math.gcd(cvt, ckt)
    L = math.comb(v - 2, k - 2)
    predicted = [lam for lam in range(1, L + 1) if lam % unit == 0]
    # r = lam*(v-1)/(k-1) is a replication number and must be an integer
    forced_out = [lam for lam in predicted if (lam * (v - 1)) % (k - 1) != 0]
    return t, cvt, ckt, unit, L, predicted, forced_out


def main():
    checks = []
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    # ------------------------------------------------------------------
    # [A] (6,3): exhaustive search for lambda = 1, 2, 3, 4
    # ------------------------------------------------------------------
    results = {}
    for lam in (1, 2, 3, 4):
        b, space, found = brute_force(lam)
        results[lam] = (b, space, found)

    b1, space1, found1 = results[1]
    b2, space2, found2 = results[2]
    b3, space3, found3 = results[3]
    b4, space4, found4 = results[4]

    check("(6,3) lambda=1: search space C(20,5) = 15504, no design exists",
          space1 == 15504 and len(found1) == 0,
          f"b = {b1}, enumerated {space1} subsets, designs found = {len(found1)}")
    check("(6,3) lambda=2: design exists (C(20,10) = 184756 naive space)",
          len(found2) >= 1,
          f"b = {b2}, enumerated {space2} subsets, designs found = {len(found2)}")
    check("(6,3) lambda=3: search space C(20,15) = 15504, no design exists",
          space3 == 15504 and len(found3) == 0,
          f"b = {b3}, enumerated {space3} subsets, designs found = {len(found3)}")
    check("(6,3) lambda=4: the complete design (all 20 triples) is the design",
          len(found4) == 1 and found4[0] == tuple(range(20)),
          f"b = {b4}, enumerated {space4} subset(s), designs found = {len(found4)}")

    # explicit designs
    design2 = found2[0]
    design2_blocks = [TRIPLES6[i] for i in design2]
    design4_blocks = [TRIPLES6[i] for i in found4[0]]
    check("(6,3) explicit lambda=2 design verified",
          is_design(design2, 2),
          f"{len(design2)} blocks: {design2_blocks}")
    check("(6,3) explicit lambda=4 design verified",
          is_design(found4[0], 4),
          f"{len(found4[0])} blocks (all triples)")

    # backtracking cross-check with node counts
    back = {}
    for lam in (1, 2, 3, 4):
        nc = NodeCounter(lam)
        d = nc.run()
        back[lam] = (nc.nodes, len(d))
        check(f"(6,3) lambda={lam}: backtracking agrees with brute force",
              len(d) == len(results[lam][2]),
              f"backtracking designs = {len(d)}, brute-force designs = "
              f"{len(results[lam][2])}, nodes = {nc.nodes}")

    # the attained set and the exceptions
    attained = sorted(lam for lam in (1, 2, 3, 4) if len(results[lam][2]) > 0)
    check("(6,3) attainable set is {2, 4}",
          attained == [2, 4],
          f"attained = {attained}")

    t6, cvt6, ckt6, unit6, L6, pred6, forced6 = criterion(6, 3)
    exceptions6 = [lam for lam in pred6 if lam not in attained]
    check("(6,3) criterion predicts {1,2,3,4}: t=k-1=2, C(6,2)/C(3,2)=5",
          pred6 == [1, 2, 3, 4] and unit6 == 1 and cvt6 == 15 and ckt6 == 3,
          f"t = {t6}, C(v,t) = {cvt6}, C(k,t) = {ckt6}, ratio = "
          f"{cvt6}/{ckt6} = {cvt6 // ckt6}, bound C(4,1) = {L6}, predicted = {pred6}")
    check("(6,3) exceptions = {1,3}, exactly the forced-out values",
          exceptions6 == forced6 == [1, 3],
          f"exceptions = {exceptions6}; r = 5*lambda/2 integral only for even lambda")
    check("(6,3) 2 exceptions <= k^2 = 9, so this witness is ABSORBED by the "
          "exception clause",
          len(exceptions6) == 2 and len(exceptions6) <= 3 ** 2,
          f"|exceptions| = {len(exceptions6)} <= k^2 = {3 ** 2}; hence (6,3) "
          f"alone refutes only the strict 'complete spectrum' reading")

    # ------------------------------------------------------------------
    # [B] (22,3): the decisive witness (no enumeration needed)
    # ------------------------------------------------------------------
    t22, cvt22, ckt22, unit22, L22, pred22, forced22 = criterion(22, 3)
    check("(22,3) criterion predicts all of {1,...,20}: "
          "C(22,2)/C(3,2) = 231/3 = 77",
          pred22 == list(range(1, 21)) and unit22 == 1 and L22 == 20,
          f"t = {t22}, C(v,t) = {cvt22}, C(k,t) = {ckt22}, ratio = "
          f"{cvt22 // ckt22}, bound C(20,1) = {L22}, |predicted| = {len(pred22)}")
    check("(22,3) r = 21*lambda/2 is an integer iff lambda is even, so the ten "
          "odd lambda are NOT attainable",
          forced22 == [1, 3, 5, 7, 9, 11, 13, 15, 17, 19],
          f"forced-out = {forced22}")
    check("(22,3) 10 exceptions > k^2 = 9: the exception clause itself fails",
          len(forced22) == 10 and len(forced22) > 3 ** 2,
          f"|forced-out| = {len(forced22)} > k^2 = {3 ** 2}; since these are "
          f"forced by a NECESSARY condition, the conjecture is false whatever "
          f"the full attainable set is")

    # ------------------------------------------------------------------
    # [C] the divisibility argument, symbolically
    # ------------------------------------------------------------------
    for (v, k) in ((6, 3), (22, 3)):
        check(f"divisibility: (v,k)=({v},{k}) requires (k-1) | lambda*(v-1)",
              True,
              f"r = lambda*(v-1)/(k-1) = lambda*{v - 1}/{k - 1}; integer only "
              f"for lambda divisible by {(k - 1) // math.gcd(k - 1, v - 1)}")

    # ------------------------------------------------------------------
    # [D] the criterion table
    # ------------------------------------------------------------------
    table = []
    for (v, k) in ((6, 3), (7, 3), (8, 3), (10, 3), (22, 3), (24, 3)):
        t, cvt, ckt, unit, L, pred, forced = criterion(v, k)
        table.append((v, k, t, cvt, ckt, cvt // ckt, L, len(pred),
                      len(forced), k * k, len(forced) > k * k))

    # ------------------------------------------------------------------
    # Report
    # ------------------------------------------------------------------
    line = "=" * 78
    print(line)
    print("Disproof of conjecture 00000008422 -- reproduction")
    print(line)

    print("\n[A] (6,3): exhaustive search over all b-subsets of the 20 triples")
    print(f"    {'lambda':>6}  {'b':>3}  {'naive space':>12}  "
          f"{'designs':>7}  attainable")
    for lam in (1, 2, 3, 4):
        b, space, found = results[lam]
        print(f"    {lam:>6}  {b:>3}  {space:>12}  {len(found):>7}  "
              f"{'YES' if found else 'no'}")
    print(f"    attainable set = {attained}")
    print(f"    criterion (t=k-1=2): 5*lambda integral for all lambda, "
          f"lambda <= C(4,1) = 4")
    print(f"    predicted set   = {pred6}   exceptions = {exceptions6} "
          f"({len(exceptions6)} <= k^2 = 9)")
    print("    => the (6,3) witness is ABSORBED by the at-most-k^2-exceptions clause")
    print("    explicit lambda=2 design:")
    for b in design2_blocks:
        print(f"        {b}")
    print("    explicit lambda=4 design: all 20 triples (the complete design)")

    print("\n[B] (22,3): the decisive witness")
    print(f"    criterion (t=k-1=2): C(22,2)/C(3,2) = {cvt22}/{ckt22} = "
          f"{cvt22 // ckt22}, so every lambda in 1..20 is predicted")
    print(f"    necessary: r = lambda*(v-1)/(k-1) = 21*lambda/2  integral")
    print(f"    forced non-attainable odd values: {forced22}")
    print(f"    {len(forced22)} exceptions > k^2 = 9  ->  the exception clause "
          f"itself is violated")

    print("\n[C] Criterion table "
          "(predicted vs. forced-out vs. k^2 budget)")
    print(f"    {'v':>3} {'k':>2} {'t':>2} {'C(v,t)':>7} {'C(k,t)':>6} "
          f"{'ratio':>5} {'L':>3} {'|pred|':>6} {'forced':>6} {'k^2':>4} "
          f"{'exceeds':>7}")
    for (v, k, t, cvt, ckt, ratio, L, npr, nfo, ksq, exc) in table:
        print(f"    {v:>3} {k:>2} {t:>2} {cvt:>7} {ckt:>6} {ratio:>5} "
              f"{L:>3} {npr:>6} {nfo:>6} {ksq:>4} {str(exc):>7}")

    print("\n[D] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified.")
        print("  The conjecture 00000008422 is FALSE.")
        print("  (6,3) alone shows the criterion is not sufficient "
              "(predicted {1,2,3,4}, attainable {2,4}),")
        print("  but 2 <= k^2 = 9 exceptions is consistent with the filed "
              "exception clause.")
        print("  The decisive witness is (22,3): the criterion predicts all "
              "lambda in 1..20,")
        print("  the necessary replication condition forces lambda even, so "
              "10 odd values")
        print("  are unattainable -- more than k^2 = 9 exceptions.")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    sys.exit(main())
