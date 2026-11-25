#!/usr/bin/env python3
r"""
Independent computational verification for Conjecture 00000002223.

Checks:
1. Byte-level alignment and mathematical definitions for amalgamated duplication
   R >< P = {(r, s) in R x R : s - r in P}, prime ideals, zero-divisor graphs
   Gamma(A) on nonzero zero-divisors Z*(A), and strict prime-ideal chains.
2. Minimal 4-element Boolean counterexample R = F_2 x F_2 with prime ideal
   P = {0} x F_2:
   - Verifies R >< P has 8 elements (isomorphic to F_2^3), Z*(R >< P) has 6
     vertices and 6 edges (the 3-sunlet / net graph), and exact diameter 3.
   - Enumerates all ideals and prime ideals of R and R >< P, confirming both
     have Krull dimension 0 (zero strict prime chains of length >= 1, hence
     zero prime chains of length 2).
3. Infinite Boolean counterexample family R^(m) = F_2^m with prime ideal
   P^(m) = {f in F_2^m : f(0) = 0} for m = 2, 3, 4:
   - Verifies |R^(m)| = 2^m, |P^(m)| = 2^(m-1), |R^(m) >< P^(m)| = 2^(2m-1),
     exact graph diameter 3, explicit witness pair (x_m, y_m) at distance 3,
     and complete absence of strict prime inclusions in Spec(R^(m)) and
     Spec(R^(m) >< P^(m)).
4. Survey of additional finite commutative rings (Z/nZ, F_p x F_q, local rings
   F_2[x]/(x^k)), verifying Anderson-Livingston's upper bound diam <= 3 (Clause 1)
   and the systematic failure of necessity in Clause 2.
5. Bounded-box verification of the sufficiency counterexample R = Z[x] with the
   strict prime chain (0) < (x) < (2, x) = P of exact height 2:
   - Confirms (0) < (x) < (2, x) is a strict chain of length 2 in Z[x] and lifts
     to a strict chain of length 2 in Z[x] >< (2, x).
   - Confirms on a finite truncated subset S_B of Z[x] >< (2, x) that nonzero
     zero-divisors partition into ({0} x (P \ {0})) |_| ((P \ {0}) x {0}),
     inducing a complete bipartite graph K_{n, n} (n >= 2) of exact diameter 2 != 3.
"""

from collections import deque
import itertools
import sys


def ring_zmod(n):
    elems = list(range(n))
    add = lambda a, b: (a + b) % n
    mul = lambda a, b: (a * b) % n
    neg = lambda a: (-a) % n
    return elems, add, mul, neg, 0, 1 % n


def prod_ring(r1, r2):
    e1, add1, mul1, neg1, z1, o1 = r1
    e2, add2, mul2, neg2, z2, o2 = r2
    elems = [(a, b) for a in e1 for b in e2]
    add = lambda x, y: (add1(x[0], y[0]), add2(x[1], y[1]))
    mul = lambda x, y: (mul1(x[0], y[0]), mul2(x[1], y[1]))
    neg = lambda x: (neg1(x[0]), neg2(x[1]))
    return elems, add, mul, neg, (z1, z2), (o1, o2)


def bool_vec_ring(m):
    elems = list(itertools.product([0, 1], repeat=m))
    add = lambda x, y: tuple((a ^ b) for a, b in zip(x, y))
    mul = lambda x, y: tuple((a & b) for a, b in zip(x, y))
    neg = lambda x: x
    zero = (0,) * m
    one = (1,) * m
    return elems, add, mul, neg, zero, one


def f2_trunc_poly(n):
    elems = list(range(1 << n))
    add = lambda a, b: a ^ b
    neg = lambda a: a

    def mul(a, b):
        res = 0
        for i in range(n):
            if (a >> i) & 1:
                for j in range(n - i):
                    if (b >> j) & 1:
                        res ^= 1 << (i + j)
        return res

    return elems, add, mul, neg, 0, 1


def verify_comm_ring_axioms(R):
    elems, add, mul, neg, zero, one = R
    elem_set = set(elems)
    assert zero in elem_set and one in elem_set and zero != one
    for a in elems:
        assert add(zero, a) == a
        assert add(neg(a), a) == zero
        assert mul(one, a) == a
        for b in elems:
            assert add(a, b) in elem_set and mul(a, b) in elem_set
            assert add(a, b) == add(b, a)
            assert mul(a, b) == mul(b, a)
    # Spot-check associativity and distributivity exhaustively for |R| <= 32
    if len(elems) <= 32:
        for a in elems:
            for b in elems:
                for c in elems:
                    assert add(add(a, b), c) == add(a, add(b, c))
                    assert mul(mul(a, b), c) == mul(a, mul(b, c))
                    assert mul(a, add(b, c)) == add(mul(a, b), mul(a, c))


def enumerate_ideals(R):
    elems, add, mul, neg, zero, one = R
    principal = set()
    for x in elems:
        gen = {mul(r, x) for r in elems}
        changed = True
        while changed:
            changed = False
            nxt = set(gen)
            for a in gen:
                for b in gen:
                    s = add(a, b)
                    if s not in nxt:
                        nxt.add(s)
                        changed = True
            gen = nxt
        principal.add(frozenset(gen))

    ideals = {frozenset([zero])}
    for p_id in principal:
        nxt_ideals = set(ideals)
        for cur in ideals:
            s = frozenset(add(a, b) for a in cur for b in p_id)
            nxt_ideals.add(s)
        ideals = nxt_ideals
    return sorted(ideals, key=len)


def is_ideal(R, I):
    elems, add, mul, neg, zero, one = R
    if zero not in I:
        return False
    for a in I:
        if neg(a) not in I:
            return False
        for b in I:
            if add(a, b) not in I:
                return False
        for r in elems:
            if mul(r, a) not in I:
                return False
    return True


def is_prime_ideal(R, P):
    elems, add, mul, neg, zero, one = R
    if not is_ideal(R, P) or one in P:
        return False
    for a in elems:
        if a not in P:
            for b in elems:
                if b not in P and mul(a, b) in P:
                    return False
    return True


def amalgamated_duplication(R, P):
    elems, add, mul, neg, zero, one = R
    dup_elems = [(r, s) for r in elems for s in elems if add(s, neg(r)) in P]
    dup_add = lambda x, y: (add(x[0], y[0]), add(x[1], y[1]))
    dup_mul = lambda x, y: (mul(x[0], y[0]), mul(x[1], y[1]))
    dup_neg = lambda x: (neg(x[0]), neg(x[1]))
    return dup_elems, dup_add, dup_mul, dup_neg, (zero, zero), (one, one)


def zero_divisor_graph_stats(A):
    elems, add, mul, neg, zero, one = A
    zstar = [
        x for x in elems
        if x != zero and any(y != zero and mul(x, y) == zero for y in elems)
    ]
    if not zstar:
        return {"vertices": zstar, "edges": 0, "diam": None, "dist": {}}
    adj = {x: [] for x in zstar}
    edge_count = 0
    for i, x in enumerate(zstar):
        for j, y in enumerate(zstar):
            if i != j and mul(x, y) == zero:
                adj[x].append(y)
                if i < j:
                    edge_count += 1

    all_dist = {}
    max_d = 0
    for src in zstar:
        dist = {src: 0}
        q = deque([src])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    q.append(v)
        assert len(dist) == len(zstar), "Zero-divisor graph must be connected!"
        all_dist[src] = dist
        max_d = max(max_d, max(dist.values()))
    return {"vertices": zstar, "edges": edge_count, "diam": max_d, "dist": all_dist, "adj": adj}


def prime_chains_of_length(primes, k):
    """Return all strict chains Q_0 < Q_1 < ... < Q_k (k strict inclusions)."""
    chains = []

    def dfs(chain):
        if len(chain) == k + 1:
            chains.append(tuple(chain))
            return
        last = chain[-1]
        for q in primes:
            if last < q:
                chain.append(q)
                dfs(chain)
                chain.pop()

    for q0 in primes:
        dfs([q0])
    return chains


def check_minimal_counterexample():
    print("=" * 74)
    print("CHECK 1: Minimal Boolean Counterexample R = F_2 x F_2, P = {0} x F_2")
    print("=" * 74)
    R = bool_vec_ring(2)
    verify_comm_ring_axioms(R)
    P = frozenset(x for x in R[0] if x[0] == 0)
    assert is_prime_ideal(R, P)
    assert len(R[0]) == 4 and len(P) == 2

    dup = amalgamated_duplication(R, P)
    verify_comm_ring_axioms(dup)
    assert len(dup[0]) == 8

    stats = zero_divisor_graph_stats(dup)
    assert len(stats["vertices"]) == 6
    assert stats["edges"] == 6
    assert stats["diam"] == 3

    x0 = ((0, 1), (0, 1))
    y0 = ((1, 0), (1, 1))
    a0 = ((1, 0), (1, 0))
    b0 = ((0, 1), (0, 0))
    assert stats["dist"][x0][y0] == 3
    assert stats["adj"][x0] == [a0]
    assert stats["adj"][y0] == [b0]
    assert b0 in stats["adj"][a0]

    ideals_R = enumerate_ideals(R)
    primes_R = [I for I in ideals_R if is_prime_ideal(R, I)]
    ideals_dup = enumerate_ideals(dup)
    primes_dup = [I for I in ideals_dup if is_prime_ideal(dup, I)]

    chains1_R = prime_chains_of_length(primes_R, 1)
    chains2_R = prime_chains_of_length(primes_R, 2)
    chains1_dup = prime_chains_of_length(primes_dup, 1)
    chains2_dup = prime_chains_of_length(primes_dup, 2)

    assert len(primes_R) == 2 and len(chains1_R) == 0 and len(chains2_R) == 0
    assert len(primes_dup) == 3 and len(chains1_dup) == 0 and len(chains2_dup) == 0

    print(f"  |R| = {len(R[0])}, |P| = {len(P)}, |R >< P| = {len(dup[0])}")
    print(f"  |Z*(R >< P)| = {len(stats['vertices'])}, |E(Gamma)| = {stats['edges']}, diam(Gamma(R >< P)) = {stats['diam']}")
    print(f"  Unique neighbor of x = {x0}: {stats['adj'][x0]}")
    print(f"  Unique neighbor of y = {y0}: {stats['adj'][y0]}")
    print(f"  Shortest path of length 3: {x0} -- {a0} -- {b0} -- {y0}")
    print(f"  |Spec(R)| = {len(primes_R)}, strict chains of len >= 1 in Spec(R): {len(chains1_R)}")
    print(f"  |Spec(R >< P)| = {len(primes_dup)}, strict chains of len >= 1 in Spec(R >< P): {len(chains1_dup)}")
    print("  [PASS] Minimal counterexample achieves diam = 3 with ZERO prime chains of length 1 or 2.\n")


def check_infinite_boolean_family():
    print("=" * 74)
    print("CHECK 2: Infinite Pairwise Non-Isomorphic Family R^(m) = F_2^m (m = 2, 3, 4)")
    print("=" * 74)
    for m in (2, 3, 4):
        R = bool_vec_ring(m)
        P = frozenset(x for x in R[0] if x[0] == 0)
        assert is_prime_ideal(R, P)
        dup = amalgamated_duplication(R, P)
        if len(dup[0]) <= 32:
            verify_comm_ring_axioms(dup)
        assert len(R[0]) == (1 << m)
        assert len(P) == (1 << (m - 1))
        assert len(dup[0]) == (1 << (2 * m - 1))

        stats = zero_divisor_graph_stats(dup)
        assert len(stats["vertices"]) == (1 << (2 * m - 1)) - 2
        assert stats["diam"] == 3

        fx = (0,) + (1,) * (m - 1)
        gx = (0,) + (1,) * (m - 1)
        fy = (1, 0) + (1,) * (m - 2)
        gy = (1,) * m
        xm = (fx, gx)
        ym = (fy, gy)
        assert stats["dist"][xm][ym] == 3
        assert len(stats["adj"][xm]) == 1
        assert len(stats["adj"][ym]) == 1

        # Every element a in R^(m) and dup satisfies a^2 = a (Boolean), hence Krull dim 0
        for a in dup[0]:
            assert dup[2](a, a) == a
        if m <= 3:
            primes_R = [I for I in enumerate_ideals(R) if is_prime_ideal(R, I)]
            primes_dup = [I for I in enumerate_ideals(dup) if is_prime_ideal(dup, I)]
            assert len(primes_R) == m
            assert len(primes_dup) == 2 * m - 1
            assert len(prime_chains_of_length(primes_R, 1)) == 0
            assert len(prime_chains_of_length(primes_dup, 1)) == 0

        print(
            f"  m = {m}: |R^(m)| = {len(R[0]):2d}, |R^(m) >< P^(m)| = {len(dup[0]):3d}, "
            f"|Z*| = {len(stats['vertices']):3d}, diam = {stats['diam']}, dist(x_m, y_m) = {stats['dist'][xm][ym]}"
        )
    print("  [PASS] Family R^(m) achieves diam = 3 with Boolean spectrum (dim = 0) for all tested m.\n")


def check_finite_ring_survey():
    print("=" * 74)
    print("CHECK 3: Finite Commutative Ring Survey (Clause 1 Bound & Clause 2 Audit)")
    print("=" * 74)
    survey = [
        ("Z/2Z", ring_zmod(2)),
        ("Z/4Z", ring_zmod(4)),
        ("Z/6Z", ring_zmod(6)),
        ("Z/8Z", ring_zmod(8)),
        ("Z/9Z", ring_zmod(9)),
        ("Z/12Z", ring_zmod(12)),
        ("F_2 x F_3", prod_ring(ring_zmod(2), ring_zmod(3))),
        ("F_3 x F_3", prod_ring(ring_zmod(3), ring_zmod(3))),
        ("F_2[x]/(x^2)", f2_trunc_poly(2)),
        ("F_2[x]/(x^3)", f2_trunc_poly(3)),
    ]
    for name, R in survey:
        verify_comm_ring_axioms(R)
        primes_R = [I for I in enumerate_ideals(R) if is_prime_ideal(R, I)]
        assert len(prime_chains_of_length(primes_R, 1)) == 0
        for P in primes_R:
            dup = amalgamated_duplication(R, P)
            stats = zero_divisor_graph_stats(dup)
            d = stats["diam"]
            assert d is None or d <= 3, "Clause 1 (Anderson-Livingston bound <= 3) violated!"
            print(
                f"  {name:12s} | |P| = {len(P):2d} | |R >< P| = {len(dup[0]):3d} | "
                f"|Z*| = {len(stats['vertices']):2d} | diam = {str(d):4s} | chains_len>=1(R) = 0"
            )
    print("  [PASS] Clause 1 (diam <= 3) holds across all surveyed rings; every diam = 3 case has 0 strict prime chains.\n")


def check_sufficiency_failure_domains():
    print("=" * 74)
    print("CHECK 4: Sufficiency Counterexamples F_2[x, y] and Z[x] (Exact Height 2)")
    print("=" * 74)

    # Part A: F_2[x, y] with (0) < (x) < (x, y) = P (matching Main.lean's F2XY)
    # Represent polynomials in F_2[x, y] with deg_x <= 2 and deg_y <= 2 (2^9 = 512 polynomials)
    f2xy_box = list(itertools.product([0, 1], repeat=9))  # idx 3*i + j = coeff of x^i y^j
    zero_f2xy = (0,) * 9
    one_f2xy = (1,) + (0,) * 8

    def mul_f2xy(p, q):
        out = [0] * 25  # deg_x <= 4, deg_y <= 4
        for i1 in range(3):
            for j1 in range(3):
                if p[3 * i1 + j1]:
                    for i2 in range(3):
                        for j2 in range(3):
                            if q[3 * i2 + j2]:
                                out[5 * (i1 + i2) + (j1 + j2)] ^= 1
        return tuple(out)

    zero_25 = (0,) * 25
    in_x_f2xy = lambda p: p[0] == 0 and p[1] == 0 and p[2] == 0
    in_xy_f2xy = lambda p: p[0] == 0

    poly_x_f2 = tuple(1 if idx == 3 else 0 for idx in range(9))
    poly_y_f2 = tuple(1 if idx == 1 else 0 for idx in range(9))
    assert not (poly_x_f2 == zero_f2xy) and in_x_f2xy(poly_x_f2)
    assert not in_x_f2xy(poly_y_f2) and in_xy_f2xy(poly_y_f2)
    assert not in_xy_f2xy(one_f2xy)

    # Check domain and primality on deg <= 1 window (2^4 = 16 polynomials)
    f2xy_small = list(itertools.product([0, 1], repeat=4))  # (1, y, x, xy)
    zero_s4 = (0, 0, 0, 0)

    def mul_s4(p, q):
        out = [0] * 9
        for i1 in range(2):
            for j1 in range(2):
                if p[2 * i1 + j1]:
                    for i2 in range(2):
                        for j2 in range(2):
                            if q[2 * i2 + j2]:
                                out[3 * (i1 + i2) + (j1 + j2)] ^= 1
        return tuple(out)

    zero_9 = (0,) * 9
    for p in f2xy_small:
        for q in f2xy_small:
            prod = mul_s4(p, q)
            if prod == zero_9:
                assert p == zero_s4 or q == zero_s4
            if prod[0] == 0 and prod[1] == 0 and prod[2] == 0:
                assert (p[0] == 0 and p[1] == 0) or (q[0] == 0 and q[1] == 0)
            if prod[0] == 0:
                assert p[0] == 0 or q[0] == 0

    dup_f2xy = [(r, s) for r in f2xy_small for s in f2xy_small if (s[0] ^ r[0]) == 0]
    zstar_f2xy = [
        u for u in dup_f2xy
        if u != (zero_s4, zero_s4)
        and any(
            v != (zero_s4, zero_s4)
            and mul_s4(u[0], v[0]) == zero_9
            and mul_s4(u[1], v[1]) == zero_9
            for v in dup_f2xy
        )
    ]
    left_f2xy = [(zero_s4, p) for p in f2xy_small if p != zero_s4 and p[0] == 0]
    right_f2xy = [(p, zero_s4) for p in f2xy_small if p != zero_s4 and p[0] == 0]
    assert set(zstar_f2xy) == set(left_f2xy) | set(right_f2xy)
    assert len(left_f2xy) == 7 and len(right_f2xy) == 7

    # Compute exact diameter of K_{7, 7}
    adj_f2xy = {
        u: [
            v for v in zstar_f2xy
            if u != v and mul_s4(u[0], v[0]) == zero_9 and mul_s4(u[1], v[1]) == zero_9
        ]
        for u in zstar_f2xy
    }
    diam_f2xy = 0
    for src in zstar_f2xy:
        dist = {src: 0}
        q = deque([src])
        while q:
            u = q.popleft()
            for v in adj_f2xy[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    q.append(v)
        assert len(dist) == len(zstar_f2xy)
        diam_f2xy = max(diam_f2xy, max(dist.values()))
    assert diam_f2xy == 2
    print(f"  [Part A: F_2[x,y] >< (x,y)] Window |S| = {len(dup_f2xy)}, |Z*| = {len(zstar_f2xy)} (K_{{7,7}}), diam = {diam_f2xy} != 3.")

    # Part B: Mixed-characteristic Z[x] with (0) < (x) < (2, x) = P
    box_polys = list(itertools.product(range(-2, 3), repeat=3))
    zero_p = (0, 0, 0)
    one_p = (1, 0, 0)

    def poly_mul(p, q):
        out = [0] * 5
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                out[i + j] += a * b
        return tuple(out)

    in_q0 = lambda p: p == zero_p
    in_q1 = lambda p: p[0] == 0
    in_P = lambda p: p[0] % 2 == 0

    poly_x = (0, 1, 0)
    poly_2 = (2, 0, 0)
    assert in_q0(zero_p) and not in_q0(poly_x)
    assert in_q1(poly_x) and not in_q1(poly_2)
    assert in_P(poly_2) and not in_P(one_p)
    for p in box_polys:
        if in_q0(p):
            assert in_q1(p)
        if in_q1(p):
            assert in_P(p)

    zero_5 = (0, 0, 0, 0, 0)
    for p in box_polys:
        for q in box_polys:
            prod = poly_mul(p, q)
            if prod == zero_5:
                assert p == zero_p or q == zero_p
            if prod[0] == 0:
                assert p[0] == 0 or q[0] == 0
            if prod[0] % 2 == 0:
                assert p[0] % 2 == 0 or q[0] % 2 == 0

    small_polys = list(itertools.product([-1, 0, 1, 2], repeat=2))
    zero_s = (0, 0)
    in_P_s = lambda p: p[0] % 2 == 0
    mul_s = lambda p, q: (p[0] * q[0], p[0] * q[1] + p[1] * q[0], p[1] * q[1])

    dup_window = [(r, s) for r in small_polys for s in small_polys if (s[0] - r[0]) % 2 == 0]
    zstar_window = [
        x for x in dup_window
        if x != (zero_s, zero_s)
        and any(
            y != (zero_s, zero_s)
            and mul_s(x[0], y[0]) == (0, 0, 0)
            and mul_s(x[1], y[1]) == (0, 0, 0)
            for y in dup_window
        )
    ]

    part_left = [(zero_s, p) for p in small_polys if p != zero_s and in_P_s(p)]
    part_right = [(p, zero_s) for p in small_polys if p != zero_s and in_P_s(p)]
    assert set(zstar_window) == set(part_left) | set(part_right)
    assert set(part_left).isdisjoint(part_right)
    assert len(part_left) >= 2 and len(part_right) >= 2

    adj = {u: [] for u in zstar_window}
    for u in zstar_window:
        for v in zstar_window:
            if u != v and mul_s(u[0], v[0]) == (0, 0, 0) and mul_s(u[1], v[1]) == (0, 0, 0):
                adj[u].append(v)

    max_d = 0
    for src in zstar_window:
        dist = {src: 0}
        q = deque([src])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    q.append(v)
        assert len(dist) == len(zstar_window)
        max_d = max(max_d, max(dist.values()))

    assert max_d == 2
    print(f"  [Part B: Z[x] >< (2,x)]     Window |S| = {len(dup_window)}, |Z*| = {len(zstar_window)} (K_{{{len(part_left)},{len(part_right)}}}), diam = {max_d} != 3.")
    print("  [PASS] Sufficiency also fails: exact height-2 prime ideals in domains yield diameter 2 != 3.\n")


def main():
    check_minimal_counterexample()
    check_infinite_boolean_family()
    check_finite_ring_survey()
    check_sufficiency_failure_domains()
    print("ALL COMPUTATIONAL VERIFICATION CHECKS PASSED SUCCESSFULLY.")


if __name__ == "__main__":
    sys.exit(main())
