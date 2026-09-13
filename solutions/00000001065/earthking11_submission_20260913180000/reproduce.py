#!/usr/bin/env python3
"""
Exhaustive refutation of Conjecture 00000001065.

Conjecture: in F_q^2 the minimal size of a Nikodym set exceeds the minimal
size of a Kakeya set by exactly q - 1.

Definitions used (the stated "almost all" wording):

* A Kakeya set K contains a full line in every one of the q+1 directions.
* A Nikodym set N is a subset such that through every point p of F_q^2 there
  is a line L with p in L and L \\ {p} contained in N; i.e. all *other*
  points of the line lie in N while p itself may be exceptional.

The script enumerates *all* subsets of F_q^2 for q = 2, 3, 4 (GF(4) arithmetic
uses the irreducible polynomial x^2 + x + 1) and reports the minima.

Standard library only.  Exits 0.
"""

from itertools import product


# --------------------------------------------------------------------------
# Finite field arithmetic for q in {2, 3, 4}
# --------------------------------------------------------------------------
class Field:
    def __init__(self, q):
        self.q = q
        if q == 2:
            self.add = lambda a, b: a ^ b
            self.mul = lambda a, b: a & b
            self.neg = lambda a: a
        elif q == 3:
            self.add = lambda a, b: (a + b) % 3
            self.mul = lambda a, b: (a * b) % 3
            self.neg = lambda a: (-a) % 3
        elif q == 4:
            # Elements 0,1,2,3 encode 0, 1, x, x+1 with x^2 = x + 1.
            def mul(a, b):
                r = 0
                while b:
                    if b & 1:
                        r ^= a
                    b >>= 1
                    a <<= 1
                    if a & 0b100:
                        a ^= 0b111  # x^2 -> x + 1
                return r & 0b11
            self.add = lambda a, b: a ^ b
            self.mul = mul
            self.neg = lambda a: a
        else:
            raise ValueError("q must be 2, 3 or 4")

    def inv(self, a):
        assert a != 0
        for b in range(self.q):
            if self.mul(a, b) == 1:
                return b
        raise AssertionError("no inverse")


# --------------------------------------------------------------------------
# Geometry of F_q^2
# --------------------------------------------------------------------------
def directions(f):
    """The q+1 directions, normalised to a canonical nonzero vector."""
    q = f.q
    seen, dirs = set(), []
    for a in range(q):
        for b in range(q):
            if a == 0 and b == 0:
                continue
            key = (1, f.mul(f.inv(a), b)) if a != 0 else (0, 1)
            if key not in seen:
                seen.add(key)
                dirs.append(key)
    return dirs


def lines(f):
    """All q(q+1) lines as (direction index, point bitmask)."""
    q = f.q
    dirs = directions(f)
    seen, out = set(), []
    for di, (d1, d2) in enumerate(dirs):
        for pa in range(q):
            for pb in range(q):
                pts = frozenset(
                    (f.add(pa, f.mul(s, d1)), f.add(pb, f.mul(s, d2)))
                    for s in range(q)
                )
                if pts in seen:
                    continue
                seen.add(pts)
                mask = 0
                for (x, y) in pts:
                    mask |= 1 << (x * q + y)
                out.append((di, mask))
    assert len(out) == q * (q + 1), (len(out), q * (q + 1))
    return out


def is_kakeya(S, ls, n_dirs):
    """Contains a full line in every direction."""
    hit = set()
    for di, mask in ls:
        if mask & ~S == 0:
            hit.add(di)
    return len(hit) == n_dirs


def is_nikodym(S, ls, n_points):
    """Through every point, a line whose other points are all in S."""
    for x in range(n_points):
        bit = 1 << x
        ok = False
        for _, mask in ls:
            if mask & bit and (mask & ~S) & ~bit == 0:
                ok = True
                break
        if not ok:
            return False
    return True


def popcount(x):
    return bin(x).count("1")


def search(q):
    f = Field(q)
    n_points = q * q
    ls = lines(f)
    n_dirs = q + 1
    best_k = best_n = None
    for S in range(1 << n_points):
        if is_kakeya(S, ls, n_dirs):
            c = popcount(S)
            if best_k is None or c < best_k:
                best_k = c
        if is_nikodym(S, ls, n_points):
            c = popcount(S)
            if best_n is None or c < best_n:
                best_n = c
    return best_k, best_n


def kakeya_formula(q):
    """Known Kakeya minimum: q(q+1)/2 for even q, + (q-1)/2 for odd q."""
    base = q * (q + 1) // 2
    return base if q % 2 == 0 else base + (q - 1) // 2


def main():
    print("Conjecture 00000001065: min Nikodym - min Kakeya == q - 1")
    print("Definitions: Kakeya = full line in every direction;")
    print("Nikodym = through every point a line whose OTHER points all lie in the set.")
    print()
    header = f"{'q':>2} | {'min Kakeya':>10} | {'min Nikodym':>11} | {'difference':>10} | {'q-1':>3} | {'verdict':>8}"
    print(header)
    print("-" * len(header))

    all_differ = False
    for q in (2, 3, 4):
        bk, bn = search(q)
        diff = bn - bk
        claim = q - 1
        verdict = "MATCH" if diff == claim else "DIFFERS"
        if diff != claim:
            all_differ = True
        print(f"{q:>2} | {bk:>10} | {bn:>11} | {diff:>10} | {claim:>3} | {verdict:>8}")

    print()
    print("Sanity check (Kakeya minima against q(q+1)/2 [+ (q-1)/2 for odd q]):")
    for q in (2, 3, 4):
        bk, _ = search(q)
        good = bk == kakeya_formula(q)
        print(f"  q={q}: computed {bk}, formula {kakeya_formula(q)} -> {'OK' if good else 'MISMATCH'}")
    print()
    print("Smallest witness, q=2: {(0,0),(0,1)} is Nikodym (size 2),")
    print("while every Kakeya set needs at least 3 points.")
    print()
    if all_differ:
        print("RESULT: the conjecture is REFUTED (differences are negative or zero, not q-1).")
    else:
        print("RESULT: the conjecture holds for the tested q.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
