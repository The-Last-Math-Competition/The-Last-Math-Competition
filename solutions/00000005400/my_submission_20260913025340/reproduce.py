#!/usr/bin/env python3
"""
Reproduce the disproof of TLMC conjecture 00000005400.

Conjecture (abridged): "There exist two maps with identical orbit distribution
limits but different periodic point counts, and the separation is realized by an
explicit conjugate pair with the same measure but different periods."

This script verifies, by exhaustive enumeration on the 4-element set {0,1,2,3}:

  Part A (Identity II)  conjugation preserves pointwise periods:
      for ALL (tau, f, x) in S4 x S4 x {0,1,2,3}   (24*24*4 = 2304 triples)
          period(tau f tau^-1)(tau x) = period(f)(x).
      Hence "an explicit conjugate pair with different periods" cannot exist.

  Part B (Identity I)   orbit distribution determines periodic point count:
      over ALL 4^4 = 256 self-maps f of {0,1,2,3}:
        (a) P(f) = sum over l of l * N_l(f), where N_l(f) = number of periodic
            orbits of length exactly l;
        (b) two maps with the same orbit profile (sorted cycle-length list)
            never have different periodic point counts.
      Hence "identical orbit distribution but different periodic point counts"
      is self-contradictory.

  Part C  prints the S4 cycle-type table and a concrete conjugate pair with a
          pointwise period comparison.

No dependencies, no absolute paths. Run:  python3 reproduce.py
Exit code 0 iff all checks pass.
"""
from itertools import permutations, product
from collections import Counter

N = 4  # size of the ground set


def compose(p, q):
    """(p o q)(x) = p[q[x]] for tuples p, q of length N."""
    return tuple(p[q[x]] for x in range(N))


def inverse(p):
    inv = [None] * N
    for x in range(N):
        inv[p[x]] = x
    return tuple(inv)


def period(f, x):
    """Least k >= 1 with f^k(x) = x (exists for every point of a finite set's
    functional graph once x is on a cycle; caller ensures x is periodic)."""
    y = x
    for k in range(1, N + 1):
        y = f[y]
        if y == x:
            return k
    raise ValueError(f"point {x} of {f} is not periodic")


def cycles(f):
    """All cycles of the functional graph of f, as a list of tuples.
    Cycles are pairwise disjoint; each is discovered exactly once."""
    seen = set()          # points already classified
    found = set()         # frozensets of cycles already recorded
    out = []
    for s in range(N):
        if s in seen:
            continue
        path, pos, y = [], {}, s
        while y not in pos:
            pos[y] = len(path)
            path.append(y)
            y = f[y]
        cyc = tuple(path[pos[y]:])           # the cycle reached from s
        key = frozenset(cyc)
        if key not in found:
            found.add(key)
            out.append(cyc)
        seen.update(path)
    # internal sanity: disjointness
    pts = [p for c in out for p in c]
    assert len(pts) == len(set(pts)), "cycles must be pairwise disjoint"
    return out


def profile(f):
    """Orbit distribution: sorted list of cycle lengths."""
    return tuple(sorted(len(c) for c in cycles(f)))


def n_l(f):
    """N_l(f): number of periodic orbits of length exactly l, as a dict."""
    d = Counter(len(c) for c in cycles(f))
    return dict(d)


def periodic_count(f):
    """P(f): number of periodic points."""
    return sum(len(c) for c in cycles(f))


def main():
    S4 = list(permutations(range(N)))
    assert len(S4) == 24

    # ---------------- Part A: Identity II on all 2304 triples ----------------
    checked = violations = 0
    for tau in S4:
        ti = inverse(tau)
        for f in S4:
            g = compose(compose(tau, f), ti)     # g = tau f tau^-1
            for x in range(N):
                checked += 1
                if period(g, tau[x]) != period(f, x):
                    violations += 1
                    print(f"VIOLATION II: tau={tau} f={f} x={x}")
    print(f"[A] Identity II (conjugation preserves pointwise period): "
          f"{checked} triples checked, {violations} violations")
    assert checked == 2304 and violations == 0

    # ------------- Part B: Identity I on all 256 self-maps -------------------
    profiles = {}
    checked = violations = 0
    for f in product(range(N), repeat=N):
        P = periodic_count(f)
        total = sum(l * m for l, m in n_l(f).items())
        checked += 1
        if P != total:
            violations += 1
            print(f"VIOLATION I(a): f={f} P={P} sum l*N_l={total}")
        profiles.setdefault(profile(f), set()).add(P)
    distinct = {p: sorted(v) for p, v in profiles.items()}
    multi = {p: v for p, v in distinct.items() if len(v) > 1}
    print(f"[B] Identity I(a)  P(f) = sum l*N_l(f): {checked} self-maps checked, "
          f"{violations} violations")
    print(f"[B] Identity I(b)  {len(distinct)} distinct orbit profiles; "
          f"profiles with more than one periodic count: "
          f"{multi if multi else 'none'}")
    assert checked == 256 and violations == 0 and not multi

    # permuted case: on S4 itself every profile gives P = 4
    perm_profiles = {}
    for f in S4:
        perm_profiles.setdefault(profile(f), set()).add(periodic_count(f))
    print(f"[B] on S4: {len(perm_profiles)} cycle types "
          f"(the partitions of 4), periodic count always 4: "
          f"{all(v == {4} for v in perm_profiles.values())}")

    # ---------------- Part C: tables -----------------------------------------
    ct = Counter(profile(f) for f in S4)
    print("\nS4 cycle types (profile -> number of permutations, P):")
    for p in sorted(ct):
        print(f"    {p}: {ct[p]} permutations, P=4")

    f0 = (1, 0, 3, 2)      # (0 1)(2 3)
    tau0 = (0, 2, 3, 1)    # (1 2 3)
    g0 = compose(compose(tau0, f0), inverse(tau0))
    print(f"\nConcrete conjugate pair: f={f0}, tau={tau0}, g=tau f tau^-1={g0}")
    ok = True
    for x in range(N):
        pf, pg = period(f0, x), period(g0, tau0[x])
        ok &= pf == pg
        print(f"    x={x}: period_f(x)={pf}  tau(x)={tau0[x]}  "
              f"period_g(tau x)={pg}")
    assert ok, "pointwise periods of the conjugate pair must agree"
    print("    pointwise periods agree for all x")

    print("\nALL CHECKS PASSED (2304/2304 conjugacy equalities, "
          "256/256 count identities, 11/11 profiles determine P)")


if __name__ == "__main__":
    main()
