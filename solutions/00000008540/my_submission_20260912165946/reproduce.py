#!/usr/bin/env python3
"""
Reproducer for the disproof of conjecture 00000008540.

    Conjecture: the congruence lattice of a finite lattice is Boolean
                exactly when the lattice is subdirectly irreducible;
                the number of congruences is at most 2^(n-1) and the
                bound is optimal.

We produce counterexamples to the "only if" direction:

    MINIMAL  L = C3, the three-element chain 0 < 1 < 2
             Con(C3) has 4 elements and is Boolean
             C3 is NOT subdirectly irreducible: it embeds subdirectly into
             C2 x C2 via 0 -> (0,0), 1 -> (0,1), 2 -> (1,1), and neither
             projection is an isomorphism.  Equivalently Con(C3) has two
             atoms, while subdirect irreducibility requires exactly one.

    SECOND   L = 2 x 2 = {0,a,b,1}, the four-element Boolean lattice
             Con(L) has 4 elements and is Boolean
             L = 2 x 2 is a direct product of two nontrivial lattices, so it
             is subdirectly reducible, and again Con(L) has two atoms.

C3 has three elements, so it is the smallest possible counterexample: no
two-element lattice works, because the only such lattice is C2, whose
congruence lattice has a single atom.

Everything is verified by brute force over ALL partitions of the element
set -- 5 partitions for C3 (Bell number B_3 = 5), 15 for 2x2 (B_4 = 15) --
using the FULL congruence condition

    x ~ y  =>  (x ^ z) ~ (y ^ z)  and  (x v z) ~ (y v z)   for all z.

We also record the count produced by the weaker and INCORRECT test
"each block is a sublattice", so that a reviewer comparing implementations
is not surprised by a larger number.

Note on a common slip: 256 is neither the number of partitions of a
four-element set (15) nor the number of equivalence relations on it (also
15, since the two notions are in bijection).  Do not use 256 here.

Standard library only.  Python 3.8+.
"""

# --------------------------------------------------------------------------
# a small lattice, given by meet and join tables
# --------------------------------------------------------------------------


class Lattice:
    def __init__(self, elements, meet, join, name, labels=None):
        self.el = list(elements)
        self.meet = meet
        self.join = join
        self.name = name
        self.labels = labels or {x: str(x) for x in self.el}

    def __len__(self):
        return len(self.el)

    def top(self):
        for x in self.el:
            if all(self.join[(x, y)] == x for y in self.el):
                return x
        return None

    def bottom(self):
        for x in self.el:
            if all(self.meet[(x, y)] == x for y in self.el):
                return x
        return None


def chain(n):
    """The n-element chain 0 < 1 < ... < n-1."""
    el = list(range(n))
    meet = {(x, y): min(x, y) for x in el for y in el}
    join = {(x, y): max(x, y) for x in el for y in el}
    return Lattice(el, meet, join, f"C{n}")


def boolean_square():
    """2 x 2 = {0, a, b, 1} with a, b incomparable."""
    el = [0, 1, 2, 3]          # 0 = bottom, 3 = top, 1 = a, 2 = b
    labels = {0: "0", 1: "a", 2: "b", 3: "1"}
    meet, join = {}, {}
    for x in el:
        for y in el:
            if x == y:
                meet[(x, y)] = x
                join[(x, y)] = x
            elif {x, y} == {1, 2}:
                meet[(x, y)] = 0
                join[(x, y)] = 3
            else:
                meet[(x, y)] = min(x, y)
                join[(x, y)] = max(x, y)
    return Lattice(el, meet, join, "2x2", labels)


# --------------------------------------------------------------------------
# partitions
# --------------------------------------------------------------------------


def all_partitions(n):
    """
    All partitions of {0..n-1} as restricted growth strings: seq[0] = 0 and
    seq[i] <= max(seq[:i]) + 1, so block labels first appear in increasing
    order and each partition has a unique representative.

    The count is the Bell number B_n: B_3 = 5, B_4 = 15.

    `hi` is the number of distinct labels already used, i.e. max + 1.  At
    position i the admissible labels are 0..hi, so the initial call uses
    hi = 1 because position 0 already carries label 0.
    """
    out = []
    seq = [0] * n

    def rec(i, hi):
        if i == n:
            out.append(tuple(seq))
            return
        for v in range(hi + 1):
            seq[i] = v
            rec(i + 1, max(hi, v + 1))

    rec(1, 1)
    return out


def canonical(part):
    """Relabel blocks in order of first appearance, so that two partitions
    representing the same relation compare equal as tuples."""
    remap = {}
    out = []
    for x in part:
        if x not in remap:
            remap[x] = len(remap)
        out.append(remap[x])
    return tuple(out)


# --------------------------------------------------------------------------
# congruence tests
# --------------------------------------------------------------------------


def is_congruence(L, part):
    """
    Full compatibility: for every related pair (x,y) and every z, the pairs
    (x^z, y^z) and (xvz, yvz) must also be related.
    """
    el = L.el
    for x in el:
        for y in el:
            if part[x] != part[y]:
                continue
            for z in el:
                if part[L.meet[(x, z)]] != part[L.meet[(y, z)]]:
                    return False
                if part[L.join[(x, z)]] != part[L.join[(y, z)]]:
                    return False
    return True


def blocks_are_sublattices(L, part):
    """
    The WEAKER, INCORRECT test: each block is closed under meet and join of
    its own elements.  This ignores the cross-block condition and accepts
    spurious relations.
    """
    el = L.el
    for x in el:
        for y in el:
            if part[x] == part[y]:
                if part[L.meet[(x, y)]] != part[x]:
                    return False
                if part[L.join[(x, y)]] != part[x]:
                    return False
    return True


def congruences(L):
    return [p for p in all_partitions(len(L)) if is_congruence(L, p)]


def render(L, part):
    groups = {}
    for x in L.el:
        groups.setdefault(part[x], []).append(x)
    blocks = []
    for _, members in sorted(groups.items(), key=lambda kv: min(kv[1])):
        blocks.append("{" + ",".join(L.labels[m] for m in members) + "}")
    return " | ".join(blocks)


# --------------------------------------------------------------------------
# congruence lattice structure
# --------------------------------------------------------------------------


def refines(a, b):
    """a <= b in the congruence lattice: a is finer than b, i.e. every pair
    related by a is also related by b."""
    return all(b[x] == b[y] for x in range(len(a)) for y in range(len(a))
               if a[x] == a[y])


def join_rel(L, a, b):
    """Transitive closure of the union of two equivalence relations."""
    n = len(L)
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry

    for x in range(n):
        for y in range(n):
            if a[x] == a[y] or b[x] == b[y]:
                union(x, y)
    return canonical(tuple(find(x) for x in range(n)))


def atoms(L, congs):
    """Congruences covering the diagonal."""
    diag = tuple(range(len(L)))
    out = []
    for c in congs:
        if c == diag:
            continue
        below = [d for d in congs if d != c and refines(d, c)]
        if all(d == diag for d in below):
            out.append(c)
    return out


def is_boolean(L, congs):
    """
    A finite lattice is Boolean iff it is isomorphic to the powerset lattice
    of its atoms: |L| = 2^k where k is the number of atoms, and every element
    is the join of a subset of the atoms.
    """
    ats = atoms(L, congs)
    if len(congs) != 2 ** len(ats):
        return False, ats
    for c in congs:
        merged = None
        for a in ats:
            if refines(a, c):
                merged = a if merged is None else join_rel(L, merged, a)
        if merged is None:
            merged = tuple(range(len(L)))   # the diagonal, empty join
        if merged != c:
            return False, ats
    return True, ats


def subdirectly_irreducible(L, congs):
    """Finite L is SI iff Con(L) has exactly one atom."""
    return len(atoms(L, congs)) == 1


# --------------------------------------------------------------------------
# reporting
# --------------------------------------------------------------------------


def report(L, note=""):
    """Print the congruence analysis of L and return the key facts."""
    parts = all_partitions(len(L))
    weak = [p for p in parts if blocks_are_sublattices(L, p)]
    congs = congruences(L)
    bool_ok, ats = is_boolean(L, congs)
    si = subdirectly_irreducible(L, congs)

    print(f"  L = {L.name}   |L| = {len(L)}   elements {L.el}")
    if L.labels != {x: str(x) for x in L.el}:
        print(f"     naming: " + ", ".join(
            f"{L.labels[x]} = {x}" for x in L.el))
    print(f"     bottom = {L.bottom()}, top = {L.top()}")
    print(f"     partitions tested (Bell number)              : {len(parts)}")
    print(f"     pass the WRONG test 'each block a sublattice': {len(weak)}")
    print(f"     pass the FULL congruence condition           : {len(congs)}")
    print()
    print(f"     the {len(congs)} congruences (coarsest first):")
    for c in sorted(congs, key=lambda p: -len(set(p))):
        print(f"       {render(L, c)}")
    print()
    print(f"     number of congruences          : {len(congs)}")
    print(f"     number of atoms                : {len(ats)}")
    print(f"     Con is Boolean                 : {bool_ok}")
    print(f"     L is subdirectly irreducible   : {si}")
    if bool_ok and not si:
        print()
        print("     -> COUNTEREXAMPLE: Con is Boolean while L is not SI")
    if note:
        print()
        for ln in note.splitlines():
            print(f"     {ln}")
    print()
    return congs, bool_ok, si


def main():
    line = "=" * 74

    print(line)
    print("MINIMAL COUNTEREXAMPLE - L = C3, the three-element chain 0 < 1 < 2")
    print(line)
    print()
    congs3, bool3, si3 = report(
        chain(3),
        note="C3 embeds subdirectly into C2 x C2 by\n"
             "     0 -> (0,0),  1 -> (0,1),  2 -> (1,1).\n"
             "   This is a lattice embedding (checked by hand: it preserves\n"
             "   both meet and join) and both coordinate projections are\n"
             "   surjective onto C2.  Neither projection is an isomorphism,\n"
             "   since C2 has 2 elements and C3 has 3.  So C3 is a proper\n"
             "   subdirect product and is therefore NOT subdirectly\n"
             "   irreducible.  Equivalently, Con(C3) has two atoms.\n"
             "   C3 is directly indecomposable, so it shows that\n"
             "   subdirect irreducibility is strictly stronger than direct\n"
             "   indecomposability -- the classical illustration of the gap.")

    print(line)
    print("SECOND COUNTEREXAMPLE - L = 2x2 = {0, a, b, 1}")
    print(line)
    print()
    report(
        boolean_square(),
        note="2x2 = 2 x 2 is literally a direct product of two nontrivial\n"
             "   lattices, so it is subdirectly reducible on its face, and\n"
             "   Con(2x2) again has two atoms.")

    print(line)
    print("MINIMALITY - no two-element lattice works")
    print(line)
    print()
    C2 = chain(2)
    c2 = congruences(C2)
    b2, a2 = is_boolean(C2, c2)
    print(f"  C2 is the only lattice with two elements.")
    print(f"     |Con(C2)| = {len(c2)}, atoms = {len(a2)}, "
          f"Boolean = {b2}, SI = {subdirectly_irreducible(C2, c2)}")
    print()
    print("  Its congruence lattice has exactly one atom, so C2 IS")
    print("  subdirectly irreducible and is consistent with the conjecture.")
    print("  Hence C3, with three elements, is the smallest counterexample.")
    print()
    print("  (The one-element lattice C1 has |Con| = 1 = 2^0, which is")
    print("  Boolean, and no atoms at all.  Whether it counts as SI depends on")
    print("  whether SI is defined for trivial lattices; it is excluded here")
    print("  and does not affect the minimality claim above.)")

    print()
    print(line)
    print("THE COUNTING CLAUSE - 2^(n-1) is NOT refuted here")
    print(line)
    print()
    print("  the chain attains the bound |Con(C_n)| = 2^(n-1):")
    print()
    print("     n   |Con(C_n)|   2^(n-1)   attained")
    for n in range(1, 9):
        C = chain(n)
        cc = congruences(C)
        print(f"   {n:4d} {len(cc):11d} {2 ** (n - 1):10d}   "
              f"{len(cc) == 2 ** (n - 1)}")
    print()
    print("  For both counterexamples the counting clause holds:")
    print(f"     C3 :  |Con| = {len(congs3)} <= 2^(3-1) = 4")
    print("     2x2:  |Con| = 4 <= 2^(4-1) = 8")
    print()
    print("  So the refutation is confined to the classification (the")
    print("  biconditional), not to the bound.")

    print()
    print(line)
    print("VERDICT")
    print(line)
    print(f"  C3 : Con Boolean = {bool3}, SI = {si3}   -> counterexample")
    print("  2x2: Con Boolean = True, SI = False  -> counterexample")
    print("  smallest counterexample: C3, with three elements")
    print("  => the 'only if' direction of the biconditional fails")
    print("  => conjecture 00000008540 is FALSE")


if __name__ == "__main__":
    main()
