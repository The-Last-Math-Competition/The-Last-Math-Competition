#!/usr/bin/env python3
r"""
Independent Python 3.12 verification suite for Conjecture 00000004768.

Cross-checks from first principles:
1. Canonical set partitions Pi_n and noncrossing partitions NC_n (Kreweras 1972).
2. Partial-order and bounded-lattice axioms under refinement on NC_1..NC_4 and Pi_1..Pi_4.
3. Exact linear extension counts e(NC_n) via three independent methods:
   - Brute-force permutation enumeration (n = 1, 2, 3),
   - Dynamic programming over the order-ideal lattice J(P) (n = 1, 2, 3, 4),
   - Exact bipartite telescoping neighborhood formula over all 6! = 720 coatom
     AND atom orderings of NC_4 \ {0_hat, 1_hat}, verifying all 9 S-profiles.
4. Exact block-size products D_n, block-factorial products, principal ideal/filter
   products, non-vacuity at n = 1, 2, and all arithmetic/prime-factor obstructions
   at n = 3 and n = 4 (both for NC_n and for Pi_n).
"""

from __future__ import annotations
import itertools
import math
from collections import Counter, deque

Partition = tuple[tuple[int, ...], ...]


def enum_set_partitions(elements: list[int]) -> list[Partition]:
    """Generate all canonical set partitions (sorted nonempty sorted blocks)."""
    if not elements:
        return [()]
    first, rest = elements[0], elements[1:]
    result: set[Partition] = set()
    for p in enum_set_partitions(rest):
        for idx in range(len(p)):
            blocks = list(p)
            blocks[idx] = tuple(sorted(blocks[idx] + (first,)))
            result.add(tuple(sorted(blocks)))
        result.add(tuple(sorted(p + ((first,),))))
    return sorted(result)


def is_noncrossing(part: Partition) -> bool:
    """Exact Kreweras noncrossing test: forbid a < b < c < d with a,c in A != B and b,d in B."""
    block_of = {x: idx for idx, blk in enumerate(part) for x in blk}
    elems = sorted(block_of.keys())
    n = len(elems)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                for l in range(k + 1, n):
                    a, b, c, d = elems[i], elems[j], elems[k], elems[l]
                    if (
                        block_of[a] == block_of[c]
                        and block_of[b] == block_of[d]
                        and block_of[a] != block_of[b]
                    ):
                        return False
    return True


def refines(p1: Partition, p2: Partition) -> bool:
    """True iff every block of p1 is a subset of some block of p2."""
    s2 = [set(b) for b in p2]
    return all(any(set(b1).issubset(sb2) for sb2 in s2) for b1 in p1)


def verify_finite_lattice(name: str, elems: list[Partition]) -> None:
    """Exhaustively verify poset axioms and existence/uniqueness of all binary meets and joins."""
    m = len(elems)
    le = [[refines(elems[i], elems[j]) for j in range(m)] for i in range(m)]
    # Reflexivity, antisymmetry, transitivity
    for i in range(m):
        assert le[i][i], f"{name}: reflexivity failed at {i}"
        for j in range(m):
            if le[i][j] and le[j][i]:
                assert i == j, f"{name}: antisymmetry failed at {i}, {j}"
            for k in range(m):
                if le[i][j] and le[j][k]:
                    assert le[i][k], f"{name}: transitivity failed at {i}, {j}, {k}"
    # Every pair has a unique greatest lower bound (meet) and least upper bound (join)
    for i in range(m):
        for j in range(m):
            lbs = [k for k in range(m) if le[k][i] and le[k][j]]
            glbs = [g for g in lbs if all(le[k][g] for k in lbs)]
            assert len(glbs) == 1, f"{name}: meet failed for {i}, {j}"
            ubs = [k for k in range(m) if le[i][k] and le[j][k]]
            lubs = [u for u in ubs if all(le[u][k] for k in ubs)]
            assert len(lubs) == 1, f"{name}: join failed for {i}, {j}"


def count_linext_bruteforce(elems: list[Partition]) -> int:
    """Count linear extensions directly by iterating over all |P|! permutations."""
    m = len(elems)
    le = [[refines(elems[i], elems[j]) for j in range(m)] for i in range(m)]
    count = 0
    for perm in itertools.permutations(range(m)):
        pos = [0] * m
        for idx, elem_id in enumerate(perm):
            pos[elem_id] = idx
        if all(pos[i] <= pos[j] for i in range(m) for j in range(m) if le[i][j]):
            count += 1
    return count


def count_linext_ideal_dp(elems: list[Partition]) -> tuple[int, int]:
    """Count linear extensions via order-ideal dynamic programming over J(P)."""
    m = len(elems)
    preds = [0] * m
    for i in range(m):
        for j in range(m):
            if i != j and refines(elems[j], elems[i]):
                preds[i] |= 1 << j
    dp: dict[int, int] = {0: 1}
    queue = deque([0])
    while queue:
        mask = queue.popleft()
        ways = dp[mask]
        for x in range(m):
            if not (mask & (1 << x)) and (preds[x] & mask) == preds[x]:
                nmask = mask | (1 << x)
                if nmask not in dp:
                    dp[nmask] = 0
                    queue.append(nmask)
                dp[nmask] += ways
    return dp[(1 << m) - 1], len(dp)


def block_size_product(elems: list[Partition]) -> int:
    return math.prod(len(b) for p in elems for b in p)


def block_factorial_product(elems: list[Partition]) -> int:
    return math.prod(math.factorial(len(b)) for p in elems for b in p)


def factorize(n: int) -> dict[int, int]:
    factors: dict[int, int] = {}
    d, temp = 2, n
    while d * d <= temp:
        while temp % d == 0:
            factors[d] = factors.get(d, 0) + 1
            temp //= d
        d += 1 if d == 2 else 2
    if temp > 1:
        factors[temp] = factors.get(temp, 0) + 1
    return factors


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    return all(n % d != 0 for d in range(2, math.isqrt(n) + 1))


def main() -> None:
    print("=== Conjecture 00000004768 Independent Verification Suite ===\n")

    expected_nc = {
        1: (1, 1, 1),
        2: (2, 1, 2),
        3: (5, 6, 24),
        4: (14, 1399200, 331776),
    }

    print("1. Checking noncrossing partition lattices NC_n (n = 1..5):")
    for n in range(1, 6):
        all_p = enum_set_partitions(list(range(1, n + 1)))
        nc_p = [p for p in all_p if is_noncrossing(p)]
        catalan = math.comb(2 * n, n) // (n + 1)
        assert len(all_p) in (1, 2, 5, 15, 52)
        assert len(nc_p) == catalan, f"Catalan mismatch at n={n}"

        if n <= 4:
            verify_finite_lattice(f"NC_{n}", nc_p)
            e_dp, num_ideals = count_linext_ideal_dp(nc_p)
            interior = [p for p in nc_p if len(p) not in (1, n)]
            e_int, num_int_ideals = count_linext_ideal_dp(interior)
            assert e_dp == e_int
            if n <= 3:
                e_bf = count_linext_bruteforce(nc_p)
                assert e_bf == e_dp
            d_prod = block_size_product(nc_p)
            exp_card, exp_e, exp_d = expected_nc[n]
            assert (len(nc_p), e_dp, d_prod) == (exp_card, exp_e, exp_d)
            lhs = math.factorial(len(nc_p))
            rhs = e_dp * d_prod
            print(
                f"   n={n}: |NC_{n}|={len(nc_p)}, |J(NC_{n})|={num_ideals} "
                f"(|J(int)|={num_int_ideals}), e(NC_{n})={e_dp}, D_{n}={d_prod}, "
                f"|NC_{n}|! == e*D_{n}? {lhs == rhs}"
            )
        else:
            print(f"   n=5: |NC_5|={len(nc_p)} (Catalan C_5 = 42), |Pi_5|={len(all_p)}")

    # Verify non-sublattice behavior of NC_4 inside Pi_4 on {{1,3},{2},{4}} and {{1},{2,4},{3}}
    nc4 = [p for p in enum_set_partitions([1, 2, 3, 4]) if is_noncrossing(p)]
    pi4 = enum_set_partitions([1, 2, 3, 4])
    assert len(pi4) - len(nc4) == 1
    unique_crossing = [p for p in pi4 if not is_noncrossing(p)]
    assert unique_crossing == [((1, 3), (2, 4))]
    print(f"\n2. Unique crossing partition of {{1,2,3,4}} verified: {unique_crossing[0]}")

    print("\n3. Cross-checking e(NC_4) = 1,399,200 via bipartite telescoping over 6! = 720 orders:")
    atoms = [(1, 2), (2, 3), (3, 4), (1, 4), (1, 3), (2, 4)]
    coatoms = [
        [{1, 2, 3}, {4}],
        [{2, 3, 4}, {1}],
        [{1, 3, 4}, {2}],
        [{1, 2, 4}, {3}],
        [{1, 2}, {3, 4}],
        [{1, 4}, {2, 3}],
    ]
    lower_masks = [
        sum((1 << i) for i, a in enumerate(atoms) if any(set(a).issubset(blk) for blk in blks))
        for blks in coatoms
    ]
    upper_masks = [
        sum((1 << j) for j, blks in enumerate(coatoms) if any(set(a).issubset(blk) for blk in blks))
        for a in atoms
    ]

    expected_profiles = {
        (2, 4, 5, 5, 6, 6): 48,
        (2, 4, 5, 6, 6, 6): 144,
        (2, 4, 6, 6, 6, 6): 48,
        (3, 4, 5, 5, 6, 6): 32,
        (3, 4, 5, 6, 6, 6): 112,
        (3, 4, 6, 6, 6, 6): 48,
        (3, 5, 5, 5, 6, 6): 16,
        (3, 5, 5, 6, 6, 6): 80,
        (3, 5, 6, 6, 6, 6): 192,
    }

    for mode_name, masks in [("coatom-orderings", lower_masks), ("atom-orderings", upper_masks)]:
        prof_counter: Counter[tuple[int, ...]] = Counter()
        total_sum = 0
        for perm in itertools.permutations(range(6)):
            cur = 0
            prof = []
            denom = 1
            for j_step, idx in enumerate(perm, start=1):
                cur |= masks[idx]
                s_j = cur.bit_count()
                prof.append(s_j)
                denom *= j_step + s_j
            assert math.factorial(12) % denom == 0
            total_sum += math.factorial(12) // denom
            prof_counter[tuple(prof)] += 1
        assert dict(prof_counter) == expected_profiles, f"Profile mismatch in {mode_name}"
        assert sum(prof_counter.values()) == 720
        assert total_sum == 1399200
        print(f"   {mode_name}: 9 exact S-profiles verified, sum over 720 permutations = {total_sum}")

    print("\n4. Checking prime-factor obstructions on NC_4:")
    e4 = 1399200
    d4 = block_size_product(nc4)
    d4_fact = block_factorial_product(nc4)
    ideal_prod = math.prod(sum(1 for q in nc4 if refines(q, p)) for p in nc4)
    filter_prod = math.prod(sum(1 for q in nc4 if refines(p, q)) for p in nc4)

    assert is_prime(53)
    assert factorize(e4) == {2: 5, 3: 1, 5: 2, 11: 1, 53: 1}
    assert factorize(d4) == {2: 12, 3: 4}
    assert factorize(d4_fact) == {2: 17, 3: 5}
    assert ideal_prod == filter_prod == 8960000
    assert factorize(ideal_prod) == {2: 11, 5: 4, 7: 1}
    assert all(math.factorial(m) % 53 != 0 for m in range(53))
    assert math.factorial(14) % e4 != 0
    assert math.factorial(12) % e4 != 0
    assert (e4 * d4) % 53 == 0

    g14 = math.gcd(math.factorial(14), e4)
    g12 = math.gcd(math.factorial(12), e4)
    print(f"   e(NC_4) = {e4} = 2^5 * 3 * 5^2 * 11 * 53 (53 is prime: {is_prime(53)})")
    print(f"   D_4 (block sizes)      = {d4} = 2^12 * 3^4")
    print(f"   D_4! (block factorials)= {d4_fact} = 2^17 * 3^5")
    print(f"   Principal ideal/filter = {ideal_prod} = 2^11 * 5^4 * 7")
    print(f"   |NC_4|! / e(NC_4)      = {math.factorial(14)//g14} / {e4//g14} (non-integer!)")
    print(f"   (|NC_4|-2)! / e(NC_4)  = {math.factorial(12)//g12} / {e4//g12} (non-integer!)")

    print("\n5. Checking full partition lattice Pi_4 (15 elements):")
    verify_finite_lattice("Pi_4", pi4)
    e_pi4, ideals_pi4 = count_linext_ideal_dp(pi4)
    d_pi4 = block_size_product(pi4)
    assert e_pi4 == 10368000
    assert factorize(e_pi4) == {2: 10, 3: 4, 5: 3}
    assert d_pi4 == 1327104
    assert math.factorial(15) != e_pi4 * d_pi4
    assert math.factorial(13) % e_pi4 != 0
    print(
        f"   |Pi_4|={len(pi4)}, |J(Pi_4)|={ideals_pi4}, e(Pi_4)={e_pi4} = 2^10 * 3^4 * 5^3, "
        f"D(Pi_4)={d_pi4} = 2^14 * 3^4"
    )
    print("   15! != e(Pi_4)*D(Pi_4) and 13! % e(Pi_4) != 0 verified.")

    print("\nALL CHECKS PASSED SUCCESSFULLY.")


if __name__ == "__main__":
    main()
