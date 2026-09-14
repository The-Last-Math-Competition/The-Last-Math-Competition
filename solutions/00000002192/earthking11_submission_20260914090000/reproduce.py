#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000002192.

    Definition: the dimension of a poset is the minimal number of linear
                extensions whose intersection is the poset.
    Conjecture: the maximal dimension of height-2 posets is
                ceil(log2 log2 n) (exact).

The conjecture is FALSE, already on the smallest non-trivial standard
example.  The file never defines `n`; under the natural reading `n = |P|`:

  * the standard example S_2 on n = 4 elements has height 2 and dimension
    exactly 2, while ceil(log2 log2 4) = 1;
  * the 2-element chain has height 2 and dimension 1, while the formula
    gives ceil(log2 log2 2) = 0;
  * the 3-element "V" poset has height 2 and dimension 2, while the
    formula gives ceil(log2 log2 3) = 1.

The true maximum dimension of a height-2 poset on n elements is
floor(n/2) for n >= 4 (Dushnik-Miller / Hiraguchi), attained by the
standard example S_{floor(n/2)}; this grows linearly, not doubly
logarithmically.  An exhaustive computation over all height-<=2 posets on
n <= 6 elements reproduces the sequence 1,2,2,2,2,3.

Standard library only, Python 3.8+.  Exits non-zero if any check fails.
"""

import itertools
import math
import sys

sys.setrecursionlimit(100000)


# ----------------------------------------------------------------------
# Exact order dimension via search over tuples of linear extensions
# ----------------------------------------------------------------------

class Poset:
    """A finite poset on {0, ..., n-1} given by its strict relations.

    `rels` is a set of ordered pairs (a, b) meaning a < b.  Relations must
    be irreflexive and transitive; the posets built here always are.
    """

    def __init__(self, n, rels):
        self.n = n
        self.rels = frozenset(rels)
        self.pairs = [(x, y) for x in range(n) for y in range(x + 1, n)]
        self.pair_index = {p: i for i, p in enumerate(self.pairs)}
        self.P = len(self.pairs)
        # forward (lower label first) / backward (higher label first) masks
        self.fwd = 0
        self.bwd = 0
        for (a, b) in self.rels:
            if a == b:
                raise ValueError("reflexive relation")
            x, y = (a, b) if a < b else (b, a)
            p = self.pair_index[(x, y)]
            if a < b:
                self.fwd |= 1 << p
            else:
                self.bwd |= 1 << p
        if self.fwd & self.bwd:
            raise ValueError("a pair is related in both directions")

    def is_total(self):
        """True iff the relation is a strict total order (a chain)."""
        full = (1 << self.P) - 1
        return (self.fwd | self.bwd) == full

    def height(self):
        """Number of elements in a longest chain (1 for an antichain)."""
        # longest path in the DAG of relations, counting vertices
        adj = {x: [] for x in range(self.n)}
        for (a, b) in self.rels:
            adj[a].append(b)
        best = [1] * self.n
        for x in self._topo():
            for y in adj[x]:
                if best[x] + 1 > best[y]:
                    best[y] = best[x] + 1
        return max(best) if best else 0

    def _topo(self):
        indeg = [0] * self.n
        adj = {x: [] for x in range(self.n)}
        for (a, b) in self.rels:
            adj[a].append(b)
            indeg[b] += 1
        stack = [x for x in range(self.n) if indeg[x] == 0]
        order = []
        while stack:
            x = stack.pop()
            order.append(x)
            for y in adj[x]:
                indeg[y] -= 1
                if indeg[y] == 0:
                    stack.append(y)
        return order

    def incomparable_pairs(self):
        """Pair indices {x<y} that are incomparable in the poset."""
        inc = []
        for p in range(self.P):
            if not ((self.fwd >> p) & 1) and not ((self.bwd >> p) & 1):
                inc.append(p)
        return inc

    def linear_extensions(self):
        """All linear extensions, as (less_mask, orient_mask) pairs.

        `less_mask` has bit p set iff the lower-labelled element of pair p
        comes first.  `orient_mask` has bit 2p set iff the lower-labelled
        element comes first and bit 2p+1 set iff the higher-labelled one
        does (exactly one bit per pair).
        """
        out = []
        allmask = (1 << self.P) - 1
        for perm in itertools.permutations(range(self.n)):
            pos = [0] * self.n
            for i, v in enumerate(perm):
                pos[v] = i
            less = 0
            for p, (x, y) in enumerate(self.pairs):
                if pos[x] < pos[y]:
                    less |= 1 << p
            # every forward relation must be lower-first ...
            if (self.fwd & (allmask ^ less)) != 0:
                continue
            # ... and every backward relation must be higher-first
            if (self.bwd & less) != 0:
                continue
            orient = 0
            for p in range(self.P):
                if (less >> p) & 1:
                    orient |= 1 << (2 * p)
                else:
                    orient |= 1 << (2 * p + 1)
            out.append((less, orient))
        return out


def order_dimension(poset):
    """Exact order dimension by iterative deepening over tuples of linear
    extensions (bitmask based), with branch and bound.

    A tuple realizes the poset iff for every incomparable pair {x,y} both
    orientations occur: some extension has x before y and some has y before
    x.  Each extension is encoded by the bits it sets on those pairs; we
    search for the smallest number of extensions whose union covers both
    bits of every incomparable pair.  The search is exact: for a given
    length limit it explores *all* tuples unless pruned by a valid bound.
    """
    inc = poset.incomparable_pairs()
    if not inc:
        return 1  # a chain: one linear extension suffices
    inc_count = len(inc)
    # target bits: 2p and 2p+1 for every incomparable pair p
    target = 0
    for p in inc:
        target |= 3 << (2 * p)
    masks = set()
    for _less, orient in poset.linear_extensions():
        m = orient & target
        if m:
            masks.add(m)
    masks = list(masks)

    by_bit = {}
    for m in masks:
        r = m
        while r:
            low = r & -r
            by_bit.setdefault(low.bit_length() - 1, []).append(m)
            r ^= low

    def feasible(limit):
        def dfs(cur, cnt):
            if cur == target:
                return True
            if cnt == limit:
                return False
            rem = target & ~cur
            if rem.bit_count() > (limit - cnt) * inc_count:
                return False
            best = None
            r = rem
            while r:
                low = r & -r
                r ^= low
                cands = [m for m in by_bit.get(low.bit_length() - 1, []) if m & low]
                if not cands:
                    return False
                if best is None or len(cands) < len(best):
                    best = cands
            for m in best:
                if dfs(cur | m, cnt + 1):
                    return True
            return False
        return dfs(0, 0)

    for d in range(1, poset.n + 1):
        if feasible(d):
            return d
    raise AssertionError("no realizer found (impossible)")


def standard_example(k):
    """The standard example S_k: a_0..a_{k-1} < b_i for i != j.

    Elements 0..k-1 are minimal, elements k..2k-1 maximal, and a_j < b_i
    iff i != j.  It has height 2 and dimension k.
    """
    rels = set()
    for i in range(k):
        for j in range(k):
            if i != j:
                rels.add((i, k + j))
    return Poset(2 * k, rels)


def formula(n):
    """The conjectured value ceil(log2 log2 n) for the natural reading
    n = number of elements (n >= 2)."""
    if n < 2:
        raise ValueError("log2 log2 n is undefined for n = 1")
    return math.ceil(math.log2(math.log2(n)))


# ----------------------------------------------------------------------
# Exhaustive enumeration of all height-<=2 posets
# ----------------------------------------------------------------------

def enumerate_height_le_2(n):
    """Yield every labelled poset of height <= 2 on {0, ..., n-1}.

    A poset has height <= 2 iff every element is minimal or maximal and all
    relations run from a minimal element to a maximal one.  Classify each
    element as minimal-only (0), maximal-only (1) or isolated (2), then
    choose an arbitrary set of relations from minimal-only to maximal-only.
    This enumerates (with repetitions) every such poset; duplicates are
    removed by the caller through a relation-set key.
    """
    for assign in itertools.product(range(3), repeat=n):
        A = [i for i in range(n) if assign[i] == 0]
        B = [i for i in range(n) if assign[i] == 1]
        slots = [(a, b) for a in A for b in B]
        for bits in range(1 << len(slots)):
            rels = frozenset(slots[k] for k in range(len(slots)) if (bits >> k) & 1)
            yield rels


def exhaustive_max_dimension(n):
    """Exact maximum dimension over all height-<=2 posets on n elements.

    Returns (max_dimension, count).  Every generated relation set is checked
    to have height <= 2, so the enumeration stays inside the family.
    """
    seen = set()
    best = 0
    for rels in enumerate_height_le_2(n):
        if rels in seen:
            continue
        seen.add(rels)
        P = Poset(n, rels)
        if P.height() > 2:
            raise AssertionError("enumeration escaped height <= 2")
        d = order_dimension(P)
        if d > best:
            best = d
    return best, len(seen)


# ----------------------------------------------------------------------
# Checks
# ----------------------------------------------------------------------

def main():
    checks = []
    all_ok = [True]

    def check(name, ok, detail):
        checks.append((name, bool(ok), detail))
        all_ok[0] = all_ok[0] and bool(ok)

    line = "=" * 74
    print(line)
    print("Disproof of conjecture 00000002192 -- reproduction")
    print(line)
    print("\nDefinition: the dimension of a poset is the minimal number of")
    print("linear extensions whose intersection is the poset.")
    print("Conjecture: the maximal dimension of height-2 posets is")
    print("            ceil(log2 log2 n) (exact).  Claimed value: FALSE.")

    # ------------------------------------------------------------------
    # 1. The dimension of the standard examples S_k
    # ------------------------------------------------------------------
    print("\n[1] Exact order dimension of the standard examples S_k")
    print("    (exact search over tuples of linear extensions, bitmask based)")
    dims = {}
    for k in (2, 3, 4):
        P = standard_example(k)
        d = order_dimension(P)
        dims[k] = d
        check(f"dim(S_{k}) = {k} (standard example on n = {2 * k} elements)",
              d == k, f"computed dim = {d}, height = {P.height()}")

    # S_2 in full detail
    S2 = standard_example(2)
    L1 = [0, 3, 1, 2]   # 0 < 3 < 1 < 2
    L2 = [1, 2, 0, 3]   # 1 < 2 < 0 < 3

    def inter_rels(exts):
        out = set()
        for a in range(S2.n):
            for b in range(S2.n):
                if a != b and all(e.index(a) < e.index(b) for e in exts):
                    out.add((a, b))
        return out

    got = inter_rels([L1, L2])
    check("L1 = [0,3,1,2] and L2 = [1,2,0,3] are linear extensions of S_2 "
          "and their intersection is exactly {(0,3), (1,2)}",
          got == set(S2.rels),
          f"intersection = {sorted(got)}, S_2 relations = {sorted(S2.rels)}")

    single = []
    for perm in itertools.permutations(range(4)):
        r = inter_rels([list(perm)])
        if r == set(S2.rels):
            single.append(perm)
    check("no single linear extension of S_2 realizes S_2, so dim(S_2) >= 2",
          single == [], f"realizing single extensions: {single}")

    check("dim(S_2) = 2 = dims[2]", dims[2] == 2,
          f"dim(S_2) = {dims[2]}")

    # ------------------------------------------------------------------
    # 2. The n-is-undefined remark and the formula on the witnesses
    # ------------------------------------------------------------------
    print("\n[2] The formula ceil(log2 log2 n) on the witnesses")
    chain2 = Poset(2, {(0, 1)})
    V = Poset(3, {(0, 2), (1, 2)})
    d_chain2 = order_dimension(chain2)
    d_V = order_dimension(V)
    check("2-element chain: height 2, dim 1, formula(2) = 0",
          chain2.height() == 2 and d_chain2 == 1 and formula(2) == 0,
          f"height = {chain2.height()}, dim = {d_chain2}, formula(2) = {formula(2)}")
    check("V poset (two minima below one maximum): height 2, dim 2, formula(3) = 1",
          V.height() == 2 and d_V == 2 and formula(3) == 1,
          f"height = {V.height()}, dim = {d_V}, formula(3) = {formula(3)}")
    check("S_2: height 2, dim 2, formula(4) = 1 (mismatch)",
          S2.height() == 2 and dims[2] == 2 and formula(4) == 1,
          f"height = {S2.height()}, dim = {dims[2]}, formula(4) = {formula(4)}")
    print("    NOTE: the conjecture never defines n.  Under n = number of")
    print("    elements the value at n = 4 is ceil(log2 log2 4) = 1, but the")
    print("    height-2 poset S_2 on 4 elements has dimension 2.")

    # ------------------------------------------------------------------
    # 3. The true maximum dimension floor(n/2) for the standard examples
    # ------------------------------------------------------------------
    print("\n[3] The standard example S_k has 2k elements and dimension k")
    for k in (2, 3, 4):
        check(f"2k = {2 * k} elements: dim(S_{k}) = {k} = floor({2 * k}/2)",
              dims[k] == k == (2 * k) // 2,
              f"dim = {dims[k]}, floor(n/2) = {(2 * k) // 2}")

    # ------------------------------------------------------------------
    # 4. Exhaustive enumeration of all height-<=2 posets on n <= 6
    # ------------------------------------------------------------------
    print("\n[4] Exhaustive maximum dimension over all height-<=2 posets,")
    print("    n = 1..6 (all labelled posets enumerated and de-duplicated)")
    expected_all = [1, 2, 2, 2, 2, 3]
    got_all = []
    counts = []
    formula_seq = []
    print(f"    {'n':>2}  {'#posets':>8}  {'max dim':>8}  {'formula(n)':>10}")
    for n in range(1, 7):
        best, cnt = exhaustive_max_dimension(n)
        got_all.append(best)
        counts.append(cnt)
        if n >= 2:
            formula_seq.append(formula(n))
            print(f"    {n:>2}  {cnt:>8}  {best:>8}  {formula(n):>10}")
        else:
            print(f"    {n:>2}  {cnt:>8}  {best:>8}  {'undefined':>10}")
    check("exhaustive max dimension over ALL height-<=2 posets for "
          "n = 1..6 is 1,2,2,2,2,3",
          got_all == expected_all,
          f"computed {got_all}, expected {expected_all}")
    check("the formula 0,1,1,2,2 for n = 2..6 agrees with the true "
          "maximum 2,2,2,2,3 only at n = 5",
          formula_seq == [0, 1, 1, 2, 2] and got_all[1:] == [2, 2, 2, 2, 3],
          f"formula {formula_seq} vs true {got_all[1:]}; matches = "
          f"{[n for n, f, t in zip(range(2, 7), formula_seq, got_all[1:]) if f == t]}")

    # ------------------------------------------------------------------
    # 5. Asymptotics: true growth floor(n/2) versus ceil(log2 log2 n)
    # ------------------------------------------------------------------
    print("\n[5] Asymptotic comparison (n = 8, 16, 1024, 10^6)")
    print(f"    {'n':>10}  {'true max = floor(n/2)':>22}  {'formula':>8}")
    asym_ok = True
    for n in (8, 16, 1024, 10 ** 6):
        true_v = n // 2
        f = formula(n)
        asym_ok = asym_ok and true_v > f
        print(f"    {n:>10}  {true_v:>22}  {f:>8}")
    check("true maximum floor(n/2) exceeds ceil(log2 log2 n) for "
          "n = 8, 16, 1024, 10^6",
          asym_ok, "true = 4,8,512,500000 vs formula = 2,2,4,5")

    # n = 8 is realized by S_4, already computed exactly
    check("n = 8: S_4 attains floor(8/2) = 4, formula(8) = 2",
          dims[4] == 4 == 8 // 2 and formula(8) == 2,
          f"dim(S_4) = {dims[4]}, floor(8/2) = 4, formula(8) = {formula(8)}")

    # ------------------------------------------------------------------
    # Report
    # ------------------------------------------------------------------
    print("\n[6] Checks")
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")

    print("\n" + line)
    if all_ok[0]:
        print("PASS: all checks verified; conjecture 00000002192 is FALSE.")
        print("  S_2 is a height-2 poset on n = 4 elements with dimension")
        print("  exactly 2, while ceil(log2 log2 4) = 1.  The true maximum is")
        print("  floor(n/2) (linear), not ceil(log2 log2 n).")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
