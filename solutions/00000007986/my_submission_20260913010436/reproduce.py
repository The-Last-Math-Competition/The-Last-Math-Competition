#!/usr/bin/env python3
"""Reproduction script for the disproof of conjecture 00000007986.

Conjecture (main clause): rho(C) <= n - sqrt(n * d) for codes with nontrivial
2-transitive automorphism group.

Counterexamples: binary repetition codes C4 = {0000, 1111} in F_2^4 and
C2 = {00, 11} in F_2^2. Their automorphism groups (coordinate permutations
S_4 and S_2, which stabilize the code set) are nontrivial and 2-transitive,
yet rho(C4) = 2 > 0 = 4 - sqrt(16) and rho(C2) = 1 > 0 = 2 - sqrt(4).

This script performs exhaustive enumeration independently of any external data.
"""

from itertools import product, permutations


def hamming(x, y):
    """Hamming distance between two binary tuples of equal length."""
    assert len(x) == len(y)
    return sum(1 for a, b in zip(x, y) if a != b)


def covering_radius(code, n):
    """rho(code) = max over all 2^n vectors x of min distance to a codeword."""
    assert len(code) >= 1 and all(len(c) == n for c in code)
    points = list(product((0, 1), repeat=n))
    assert len(points) == 2 ** n
    return max(min(hamming(x, c) for c in code) for x in points)


def min_distance(code):
    """Minimum Hamming distance between distinct codewords."""
    return min(hamming(c1, c2) for c1 in code for c2 in code if c1 != c2)


def is_2transitive_stabilizer(code, n):
    """Check the automorphism claim: every permutation of the n coordinates
    stabilizes the code set (so the group S_n, which is nontrivial and
    2-transitive for n >= 2, is contained in the automorphism group)."""
    count = 0
    for p in permutations(range(n)):
        acted = {tuple(c[p[i]] for i in range(n)) for c in code}
        if acted == set(code):
            count += 1
    return count == len(list(permutations(range(n)))), count


def bound_rhs(n, d):
    """Right-hand side n - sqrt(n*d), computed in exact arithmetic when n*d is
    a perfect square (as in both counterexamples)."""
    k = n * d
    r = int(round(k ** 0.5))
    assert r * r == k, "n*d is not a perfect square"
    return n - r


def main():
    print("=" * 72)
    print("Disproof of conjecture 00000007986: rho(C) <= n - sqrt(n*d)")
    print("=" * 72)

    # ---------------- primary counterexample C4 ----------------
    n4, C4 = 4, [(0, 0, 0, 0), (1, 1, 1, 1)]
    d4 = min_distance(C4)
    rho4 = covering_radius(C4, n4)
    rhs4 = bound_rhs(n4, d4)
    stab4, cnt4 = is_2transitive_stabilizer(C4, n4)

    print("\n[Primary counterexample] C4 = {0000, 1111} in F_2^4")
    print(f"  exhaustive enumeration of all {2**n4} vectors of F_2^4:")
    for x in product((0, 1), repeat=n4):
        print(f"    d({ ''.join(map(str, x)) }, 0000)="
              f"{hamming(x, C4[0])}, d(x, 1111)={hamming(x, C4[1])}, "
              f"min={min(hamming(x, c) for c in C4)}")
    print(f"  n = {n4}, d = {d4}")
    print(f"  covering radius rho(C4) = max min(...) = {rho4}")
    print(f"  automorphism group: all {cnt4} coordinate permutations of S_4 "
          f"stabilize the code: {stab4} (S_4 is nontrivial and 2-transitive)")
    print(f"  conjecture RHS = n - sqrt(n*d) = {n4} - sqrt({n4 * d4}) = {rhs4}")
    print(f"  claimed inequality: {rho4} <= {rhs4}  ->  {rho4 <= rhs4}")
    assert d4 == 4, "d(C4) must be 4"
    assert rho4 == 2, "rho(C4) must be 2"
    assert rhs4 == 0, "4 - sqrt(16) must be 0"
    assert stab4, "S4 must stabilize C4 setwise"
    assert rho4 > rhs4, "counterexample must violate the bound"

    # ---------------- secondary counterexample C2 ----------------
    n2, C2 = 2, [(0, 0), (1, 1)]
    d2 = min_distance(C2)
    rho2 = covering_radius(C2, n2)
    rhs2 = bound_rhs(n2, d2)
    stab2, cnt2 = is_2transitive_stabilizer(C2, n2)

    print("\n[Secondary counterexample] C2 = {00, 11} in F_2^2")
    for x in product((0, 1), repeat=n2):
        print(f"    d({ ''.join(map(str, x)) }, 00)={hamming(x, C2[0])}, "
              f"d(x, 11)={hamming(x, C2[1])}, "
              f"min={min(hamming(x, c) for c in C2)}")
    print(f"  n = {n2}, d = {d2}")
    print(f"  covering radius rho(C2) = max min(...) = {rho2}")
    print(f"  automorphism group: all {cnt2} coordinate permutations of S_2 "
          f"stabilize the code: {stab2} (S_2 is nontrivial and 2-transitive)")
    print(f"  conjecture RHS = n - sqrt(n*d) = {n2} - sqrt({n2 * d2}) = {rhs2}")
    print(f"  claimed inequality: {rho2} <= {rhs2}  ->  {rho2 <= rhs2}")
    assert d2 == 2, "d(C2) must be 2"
    assert rho2 == 1, "rho(C2) must be 1"
    assert rhs2 == 0, "2 - sqrt(4) must be 0"
    assert stab2, "S2 must stabilize C2 setwise"
    assert rho2 > rhs2, "counterexample must violate the bound"

    # ---------------- verdict ----------------
    print("\n" + "=" * 72)
    print("VERDICT: conjecture 00000007986 (main clause "
          "rho(C) <= n - sqrt(n*d)) is FALSE.")
    print("  rho(C4) = 2 > 0 = 4 - sqrt(16)")
    print("  rho(C2) = 1 > 0 = 2 - sqrt(4)")
    print("Both codes have nontrivial 2-transitive automorphism groups, so the")
    print("hypothesis of the conjecture is satisfied in both cases.")
    print("(Scope: only the main inequality is refuted; the orbit-rank and")
    print(" design-strength clauses are not targeted by this disproof.)")
    print("=" * 72)


if __name__ == "__main__":
    main()
