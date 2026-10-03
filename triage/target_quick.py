#!/usr/bin/env python3
"""
Target A/B/D: three conjectures that are refutable without heavy machinery.

A. 00000001243  Wolfram rule 30 central column is claimed square-free.
B. 00000001016  a "[84,12,12] binary self-dual code" is claimed not to exist.
D. 00000008540  Con(L) Boolean iff L subdirectly irreducible.

Each check is self-contained and prints the evidence.
"""

# --- A: rule 30 central column -------------------------------------------------
def rule30_central(n):
    """Central column of elementary CA rule 30 from a single 1, n terms."""
    width = 2 * n + 3
    row = [0] * width
    row[width // 2] = 1
    out = []
    for _ in range(n):
        out.append(row[width // 2])
        nxt = [0] * width
        for i in range(1, width - 1):
            l, c, r = row[i - 1], row[i], row[i + 1]
            nxt[i] = l ^ (c | r)          # rule 30
        row = nxt
    return out


def first_square(seq):
    """Return (start, period, factor) for the earliest factor uu, else None."""
    n = len(seq)
    for p in range(1, n // 2 + 1):
        for s in range(0, n - 2 * p + 1):
            if seq[s:s + p] == seq[s + p:s + 2 * p]:
                return s, p, seq[s:s + 2 * p]
    return None


print("=" * 74)
print("A. 00000001243 - 'rule 30 central column is square-free'")
print("=" * 74)
seq = rule30_central(64)
print("first 32 terms of the central column:")
print("  " + "".join(map(str, seq[:32])))
sq = first_square(seq)
print(f"  earliest square (factor uu): start={sq[0]}, period={sq[1]}, factor={sq[2]}")
print(f"  -> '11' at positions 0-1" if sq[1] == 1 and sq[0] == 0 else "")
print()
print("  The claim fails for a reason that needs no computation at all:")
print("  every binary word of length >= 4 contains a square.")
print("  proof: if s0=s1 or s1=s2 or s2=s3 we are done; otherwise s2=s0 and s3=s1,")
print("  so s0s1s2s3 = (s0s1)^2. Hence no binary word of length >= 4 is square-free.")

# --- B: [84,12,12] self-dual code ---------------------------------------------
print()
print("=" * 74)
print("B. 00000001016 - 'the [84,12,12] binary extremal self-dual code does not exist'")
print("=" * 74)
n, k, d = 84, 12, 12
print(f"  stated parameters: [{n}, {k}, {d}] binary, described as self-dual")
print(f"  a binary self-dual code of length n must satisfy k = n/2 = {n // 2}")
print(f"  but the stated k = {k}")
print(f"  -> k != n/2, so the object cannot be self-dual: the description is")
print(f"     internally contradictory and the conjecture is vacuous as written.")
print(f"  (a genuine self-dual code of length 84 would be [{n},{n // 2},{d}])")

# --- D: congruence lattice -----------------------------------------------------
print()
print("=" * 74)
print("D. 00000008540 - 'Con(L) is Boolean exactly when L is subdirectly irreducible'")
print("=" * 74)


def con_lattice_of_boolean_square():
    """Con(2x2) for the 4-element Boolean lattice 2^2 = {0,a,b,1}."""
    elems = [0, 1, 2, 3]          # 0 = bottom, 1 = a, 2 = b, 3 = top
    meet, join = {}, {}
    for x in elems:
        for y in elems:
            if x == 0 or y == 0:
                m = 0
            elif x == 3:
                m = y
            elif y == 3:
                m = x
            elif x == y:
                m = x
            else:
                m = 0              # a and b are incomparable
            if x == 3 or y == 3:
                j = 3
            elif x == 0:
                j = y
            elif y == 0:
                j = x
            elif x == y:
                j = x
            else:
                j = 3              # a join b = top
            meet[(x, y)] = m
            join[(x, y)] = j

    congs = set()
    for mask in range(4 ** 4):
        raw = [(mask >> (2 * i)) & 3 for i in elems]
        # canonicalise the block labelling, otherwise the same partition is
        # counted once per relabelling
        canon, seen = [], {}
        for lab in raw:
            if lab not in seen:
                seen[lab] = len(seen)
            canon.append(seen[lab])
        part = canon
        ok = True
        # a lattice congruence must satisfy: x ~ y  =>  f(x,z) ~ f(y,z) for
        # every z and every basic operation f. Checking only that each block is
        # a sublattice is NOT sufficient.
        for x in elems:
            for y in elems:
                if part[x] != part[y]:
                    continue
                for z in elems:
                    if part[meet[(x, z)]] != part[meet[(y, z)]]:
                        ok = False
                    if part[join[(x, z)]] != part[join[(y, z)]]:
                        ok = False
        if ok:
            congs.add(tuple(part))
    return sorted(congs)


congs = con_lattice_of_boolean_square()
print(f"  2x2 = the 4-element Boolean lattice {{0,a,b,1}}")
print(f"  congruences found: {len(congs)}")
for c in congs:
    blocks = {}
    for e, lab in enumerate(c):
        blocks.setdefault(lab, []).append("0ab1"[e])
    print("    " + " | ".join("{" + ",".join(v) + "}" for v in blocks.values()))
print()
print("  The 4 congruences form a diamond: the two middle congruences are")
print("  incomparable and both sit below the total congruence. A 4-element")
print("  distributive lattice with that shape is 2^2, so Con(2x2) is Boolean.")
print()
print("  But 2x2 = 2 x 2 is a direct product of two nontrivial lattices, so it is")
print("  NOT subdirectly irreducible: its congruence lattice has TWO atoms,")
print("  whereas subdirect irreducibility requires exactly one.")
print()
print("  -> counterexample: Con(2x2) is Boolean while 2x2 is not subdirectly")
print("     irreducible. The 'exactly when' (iff) direction is false.")
print()

# --- D2: the SMALLEST counterexample is the 3-element chain C3 --------------
# NOTE: 2x2 is a counterexample, but it is not the smallest one.  The smallest
# is C3, the 3-element chain.  This was found while writing the submission
# package: C3 has Con(C3) = 2^2 (Boolean) and two atoms, so it is not
# subdirectly irreducible.  No 2-element lattice works (C2 has one atom), so
# C3 is optimal in size.


def con_chain(n):
    """All congruences of the n-element chain: partitions into intervals."""
    elems = list(range(n))
    meet = {(x, y): min(x, y) for x in elems for y in elems}
    join = {(x, y): max(x, y) for x in elems for y in elems}
    congs = set()
    for mask in range(4 ** n):
        raw = [(mask >> (2 * i)) & 3 for i in elems]
        canon, seen = [], {}
        for lab in raw:
            if lab not in seen:
                seen[lab] = len(seen)
            canon.append(seen[lab])
        part = canon
        ok = True
        for x in elems:
            for y in elems:
                if part[x] != part[y]:
                    continue
                for z in elems:
                    if part[meet[(x, z)]] != part[meet[(y, z)]]:
                        ok = False
                    if part[join[(x, z)]] != part[join[(y, z)]]:
                        ok = False
        if ok:
            congs.add(tuple(part))
    return sorted(congs)


def count_atoms(congs):
    """Congruences covering the diagonal."""
    n = len(congs[0])
    diag = tuple(range(n))

    def finer(a, b):
        return all(b[x] == b[y] for x in range(n) for y in range(n)
                   if a[x] == a[y])

    ats = []
    for c in congs:
        if c == diag:
            continue
        if all(d == diag for d in congs if d != c and finer(d, c)):
            ats.append(c)
    return ats


for n in (2, 3, 4):
    cc = con_chain(n)
    ats = count_atoms(cc)
    is_bool = len(cc) == 2 ** len(ats)
    si = len(ats) == 1
    tag = ""
    if is_bool and not si:
        tag = "  <- COUNTEREXAMPLE"
    print(f"  C{n}: |Con| = {len(cc):2d} = 2^{len(ats)}  atoms = {len(ats)}  "
          f"Boolean = {str(is_bool):5s}  SI = {str(si):5s}{tag}")

print()
print("  C3 is the smallest counterexample: Con(C3) is Boolean, but C3 is not")
print("  subdirectly irreducible.  C3 embeds subdirectly into C2 x C2 via")
print("     0 -> (0,0),  1 -> (0,1),  2 -> (1,1)")
print("  with both projections onto C2 surjective and neither an isomorphism.")
print("  Equivalently Con(C3) has two atoms, {0,1}|{2} and {0}|{1,2}.")
print()
print("  C3 is directly indecomposable (a product of two nontrivial lattices")
print("  has >= 4 elements, and C3 is a chain), so it is the classical example")
print("  that subdirect irreducibility is strictly stronger than direct")
print("  indecomposability.")
print()
print("  C2 is the only 2-element lattice and has exactly one atom, so it is")
print("  SI and consistent with the conjecture.  Hence C3 is minimal.")
print()
print("  Generalisation: for every n >= 3 the chain Cn is a counterexample")
print("  (Con(Cn) has 2^(n-1) elements and n-1 >= 2 atoms).")
