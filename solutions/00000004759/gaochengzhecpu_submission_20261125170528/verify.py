"""
Standalone Exact Verification Suite for Conjecture 00000004759
(Nested Recursion of Operator-Valued Free Convolution).

Uses only the Python 3.12 standard library (`fractions`, `itertools`).
Exits with code 0 iff all checks pass.
"""

from fractions import Fraction
from itertools import permutations, product
import sys


# ============================================================================
# 1. Exact 2x2 Matrix Arithmetic over Q
# ============================================================================

Z2 = ((Fraction(0), Fraction(0)), (Fraction(0), Fraction(0)))
I2 = ((Fraction(1), Fraction(0)), (Fraction(0), Fraction(1)))
E11 = ((Fraction(1), Fraction(0)), (Fraction(0), Fraction(0)))
E12 = ((Fraction(0), Fraction(1)), (Fraction(0), Fraction(0)))
E21 = ((Fraction(0), Fraction(0)), (Fraction(1), Fraction(0)))
E22 = ((Fraction(0), Fraction(0)), (Fraction(0), Fraction(1)))
SIGMA_X = ((Fraction(0), Fraction(1)), (Fraction(1), Fraction(0)))
BASIS_MATS = [E11, E12, E21, E22]


def mat_add(A, B):
    return tuple(tuple(A[r][c] + B[r][c] for c in range(2)) for r in range(2))


def mat_sub(A, B):
    return tuple(tuple(A[r][c] - B[r][c] for c in range(2)) for r in range(2))


def mat_scale(s, A):
    s = Fraction(s)
    return tuple(tuple(s * A[r][c] for c in range(2)) for r in range(2))


def mat_mul(A, B):
    return tuple(
        tuple(sum(A[r][k] * B[k][c] for k in range(2)) for c in range(2))
        for r in range(2)
    )


def mat_list_prod(ms):
    acc = I2
    for m in ms:
        acc = mat_mul(acc, m)
    return acc


def diag_mat(d1, d2):
    return ((Fraction(d1), Fraction(0)), (Fraction(0), Fraction(d2)))


# ============================================================================
# 2. Noncrossing Partitions NC(n), First-Block Bijection, and Nesting Depth
# ============================================================================

def generate_set_partitions(elements):
    if not elements:
        yield []
        return
    first = elements[0]
    for rest in generate_set_partitions(elements[1:]):
        for idx in range(len(rest)):
            yield rest[:idx] + [[first] + rest[idx]] + rest[idx + 1:]
        yield [[first]] + rest


def is_noncrossing(part):
    m = len(part)
    for i in range(m):
        for j in range(i + 1, m):
            V, W = part[i], part[j]
            for a in V:
                for c in V:
                    if a < c:
                        for b in W:
                            for d in W:
                                if b < d and ((a < b < c < d) or (b < a < d < c)):
                                    return False
    return True


def nc_partitions(n):
    out = []
    for p in generate_set_partitions(list(range(1, n + 1))):
        ps = tuple(sorted(tuple(sorted(b)) for b in p))
        if is_noncrossing(ps):
            out.append(ps)
    return sorted(out)


def nesting_depth(part):
    if not part:
        return 0
    best = 1
    for V in part:
        enc = sum(1 for W in part if W != V and W[0] < V[0] and V[-1] < W[-1])
        best = max(best, 1 + enc)
    return best


def enum_nc_decomp(n):
    """Recursive first-block decomposition matching Lean `NCDecomp.enumNC`."""
    if n == 0:
        return [None]
    out = []
    for inners, tail in _enum_splits(n - 1):
        out.append(("block", inners, tail))
    return out


def _enum_splits(budget):
    if budget == 0:
        return [((), None)]
    res = [((), t) for t in enum_nc_decomp(budget)]
    for k in range(budget):
        ps = enum_nc_decomp(k)
        rests = _enum_splits(budget - 1 - k)
        for p in ps:
            for rs, t in rests:
                res.append(((p,) + rs, t))
    return res


def decomp_to_partition(node, offset=1):
    if node is None:
        return (), offset
    _, inners, tail = node
    first_blk = [offset]
    cur = offset + 1
    sub_blks = []
    for child in inners:
        c_blks, cur = decomp_to_partition(child, cur)
        sub_blks.extend(c_blks)
        first_blk.append(cur)
        cur += 1
    t_blks, cur = decomp_to_partition(tail, cur)
    sub_blks.extend(t_blks)
    all_blks = tuple(sorted([tuple(first_blk)] + list(sub_blks)))
    return all_blks, cur


def verify_nc_combinatorics():
    expected_catalan = {1: 1, 2: 2, 3: 5, 4: 14, 5: 42, 6: 132, 7: 429}
    expected_depths = {
        1: [(1, 1)],
        2: [(1, 2)],
        3: [(1, 4), (2, 1)],
        4: [(1, 8), (2, 6)],
        5: [(1, 16), (2, 25), (3, 1)],
        6: [(1, 32), (2, 90), (3, 10)],
    }
    for n in range(1, 8):
        ncs = nc_partitions(n)
        decomps = enum_nc_decomp(n)
        mapped = sorted(decomp_to_partition(d, 1)[0] for d in decomps)
        assert len(ncs) == expected_catalan[n], f"Catalan count failed at n={n}"
        assert mapped == ncs, f"NCDecomp bijection failed at n={n}"
        if n <= 6:
            hist = {}
            for p in ncs:
                d = nesting_depth(p)
                hist[d] = hist.get(d, 0) + 1
            assert sorted(hist.items()) == expected_depths[n], f"Depth histogram failed at n={n}"
            # Verify depth-1 interval partition count is 2^(n-1)
            assert hist[1] == 2 ** (n - 1)
    print("[PASS] Check 1: NC(n) Catalan counts, NCDecomp bijection, and nesting-depth histograms (n=1..7).")


# ============================================================================
# 3. Exact Fock Space & Finite-Dimensional Rademacher Realizations over M_2(Q)
# ============================================================================

def state_add(s1, s2):
    out = dict(s1)
    for w, v in s2.items():
        nv = (
            out.get(w, (Fraction(0), Fraction(0)))[0] + v[0],
            out.get(w, (Fraction(0), Fraction(0)))[1] + v[1],
        )
        if nv == (Fraction(0), Fraction(0)):
            out.pop(w, None)
        else:
            out[w] = nv
    return out


def apply_create(i, state):
    return {(i,) + w: vec for w, vec in state.items()}


def apply_annihilate(i, state):
    out = {}
    for w, vec in state.items():
        if w and w[0] == i:
            nw = w[1:]
            prev = out.get(nw, (Fraction(0), Fraction(0)))
            out[nw] = (prev[0] + vec[0], prev[1] + vec[1])
    return {w: v for w, v in out.items() if v != (Fraction(0), Fraction(0))}


def apply_mat(B, state):
    out = {}
    for w, vec in state.items():
        nv = (
            B[0][0] * vec[0] + B[0][1] * vec[1],
            B[1][0] * vec[0] + B[1][1] * vec[1],
        )
        if nv != (Fraction(0), Fraction(0)):
            out[w] = nv
    return out


def op_expectation(op_fn):
    s0 = op_fn({(): (Fraction(1), Fraction(0))})
    s1 = op_fn({(): (Fraction(0), Fraction(1))})
    c0 = s0.get((), (Fraction(0), Fraction(0)))
    c1 = s1.get((), (Fraction(0), Fraction(0)))
    return ((c0[0], c1[0]), (c0[1], c1[1]))


def op_s(i):
    return lambda st: state_add(apply_annihilate(i, st), apply_create(i, st))


def op_b(B):
    return lambda st: apply_mat(B, st)


def op_tensor(M, scalar_op):
    return lambda st: apply_mat(M, scalar_op(st))


def op_sum(*ops):
    def fn(st):
        acc = {}
        for op in ops:
            acc = state_add(acc, op(st))
        return acc
    return fn


def op_diff(op1, op2):
    return lambda st: state_add(op1(st), apply_mat(diag_mat(-1, -1), op2(st)))


def op_comp(*ops):
    def fn(st):
        cur = st
        for op in reversed(ops):
            cur = op(cur)
        return cur
    return fn


def op_pow(op, k):
    if k == 0:
        return lambda st: st
    return op_comp(*([op] * k))


def verify_moment_counterexamples():
    X = op_tensor(I2, op_s(0))
    X_tilde = op_tensor(SIGMA_X, op_s(0))
    Y_det = op_b(E11)
    Y_semi = op_tensor(E11, op_s(1))

    # 1. Verify B-freeness directly on centered alternating words up to length 5
    a0_list = [X, X_tilde, op_diff(op_pow(X, 2), op_b(I2)), op_comp(op_b(E12), X_tilde)]
    a1_list = [Y_semi, op_diff(op_pow(Y_semi, 2), op_b(E11)), op_comp(Y_semi, op_b(E12))]
    for a0 in a0_list:
        assert op_expectation(a0) == Z2
    for a1 in a1_list:
        assert op_expectation(a1) == Z2
    for length in range(1, 6):
        for start in (0, 1):
            pools = [(a0_list if (start + idx) % 2 == 0 else a1_list) for idx in range(length)]
            for seq in product(*pools):
                assert op_expectation(op_comp(*seq)) == Z2

    # 2. Identical single-variable power moments for k = 0..8
    catalans = {0: 1, 2: 1, 4: 2, 6: 5, 8: 14}
    for k in range(9):
        mx = op_expectation(op_pow(X, k))
        mxt = op_expectation(op_pow(X_tilde, k))
        expected = diag_mat(catalans[k], catalans[k]) if k % 2 == 0 else Z2
        assert mx == expected and mxt == expected

    # 3. Order n=3 discrepancy with Y_det = E11 (and 8D Rademacher cross-check)
    assert op_expectation(op_pow(op_sum(X, Y_det), 1)) == diag_mat(1, 0)
    assert op_expectation(op_pow(op_sum(X_tilde, Y_det), 1)) == diag_mat(1, 0)
    assert op_expectation(op_pow(op_sum(X, Y_det), 2)) == diag_mat(2, 1)
    assert op_expectation(op_pow(op_sum(X_tilde, Y_det), 2)) == diag_mat(2, 1)
    assert op_expectation(op_pow(op_sum(X, Y_det), 3)) == diag_mat(4, 0)
    assert op_expectation(op_pow(op_sum(X_tilde, Y_det), 3)) == diag_mat(3, 1)

    # 8-dimensional finite-dimensional algebra M_2(Q) (+) M_2(Q) cross-check for n=3:
    rad_X = (I2, diag_mat(-1, -1))
    rad_Xt = (SIGMA_X, mat_scale(-1, SIGMA_X))
    rad_Y = (E11, E11)
    rad_exp = lambda pair: mat_scale(Fraction(1, 2), mat_add(pair[0], pair[1]))
    rad_sum1 = (mat_add(rad_X[0], rad_Y[0]), mat_add(rad_X[1], rad_Y[1]))
    rad_sum2 = (mat_add(rad_Xt[0], rad_Y[0]), mat_add(rad_Xt[1], rad_Y[1]))
    assert rad_exp((mat_list_prod([rad_sum1[0]] * 3), mat_list_prod([rad_sum1[1]] * 3))) == diag_mat(4, 0)
    assert rad_exp((mat_list_prod([rad_sum2[0]] * 3), mat_list_prod([rad_sum2[1]] * 3))) == diag_mat(3, 1)

    # Multiplicative convolution discrepancy at n=2:
    assert op_expectation(op_pow(op_comp(X, Y_det), 2)) == E11
    assert op_expectation(op_pow(op_comp(X_tilde, Y_det), 2)) == Z2

    # 4. Centered semicircular discrepancy at n=4 (depth 2) and n=6 (depth 3)
    for k in (1, 2, 3, 5):
        assert op_expectation(op_pow(op_sum(X, Y_semi), k)) == op_expectation(op_pow(op_sum(X_tilde, Y_semi), k))
    assert op_expectation(op_pow(op_sum(X, Y_semi), 4)) == diag_mat(8, 2)
    assert op_expectation(op_pow(op_sum(X_tilde, Y_semi), 4)) == diag_mat(7, 3)
    assert op_expectation(op_pow(op_sum(X, Y_semi), 6)) == diag_mat(40, 5)
    assert op_expectation(op_pow(op_sum(X_tilde, Y_semi), 6)) == diag_mat(30, 12)

    print("[PASS] Check 2: B-freeness and moment-indistinguishable convolution counterexamples (n=2, 3, 4, 6).")


# ============================================================================
# 4. Exact Verification of the 78-Operator Un-Nested Block-Weighting No-Go Theorem
# ============================================================================

def eta_swap(B):
    return ((B[1][1], Fraction(0)), (Fraction(0), B[0][0]))


def eval_unnested(perm, pat_id, eta, bs):
    x, y, z = bs[perm[0]], bs[perm[1]], bs[perm[2]]
    if pat_id == 0: return mat_mul(mat_mul(x, y), z)
    if pat_id == 1: return mat_mul(mat_mul(eta(x), y), z)
    if pat_id == 2: return mat_mul(mat_mul(x, eta(y)), z)
    if pat_id == 3: return mat_mul(mat_mul(x, y), eta(z))
    if pat_id == 4: return mat_mul(mat_mul(eta(x), eta(y)), z)
    if pat_id == 5: return mat_mul(mat_mul(eta(x), y), eta(z))
    if pat_id == 6: return mat_mul(mat_mul(x, eta(y)), eta(z))
    if pat_id == 7: return mat_mul(mat_mul(eta(x), eta(y)), eta(z))
    if pat_id == 8: return mat_mul(eta(mat_mul(x, y)), z)
    if pat_id == 9: return mat_mul(eta(mat_mul(x, y)), eta(z))
    if pat_id == 10: return mat_mul(x, eta(mat_mul(y, z)))
    if pat_id == 11: return mat_mul(eta(x), eta(mat_mul(y, z)))
    if pat_id == 12: return eta(mat_mul(mat_mul(x, y), z))
    raise ValueError(pat_id)


def phi_all(fn):
    return (
        fn(E11, E11, E12)[0][1]
        + fn(E11, E11, E21)[1][0]
        + fn(E11, E11, E22)[0][0]
        - fn(E11, E11, E22)[1][1]
        - fn(E11, E12, E11)[0][1]
        - fn(E11, E12, E22)[0][1]
        - fn(E11, E21, E11)[1][0]
        - fn(E11, E21, E22)[1][0]
        - fn(E11, E22, E11)[0][0]
        + fn(E11, E22, E11)[1][1]
        + fn(E11, E22, E12)[0][1]
        + fn(E11, E22, E21)[1][0]
    )


def verify_unnested_no_go():
    X_swap = op_sum(
        lambda st: apply_mat(E12, apply_annihilate(0, st)),
        lambda st: apply_mat(E21, apply_create(0, st)),
        lambda st: apply_mat(E21, apply_annihilate(1, st)),
        lambda st: apply_mat(E12, apply_create(1, st)),
    )
    for B in BASIS_MATS:
        assert op_expectation(op_comp(X_swap, op_b(B), X_swap)) == eta_swap(B)

    def mu4_xswap(b1, b2, b3):
        return op_expectation(op_comp(X_swap, op_b(b1), X_swap, op_b(b2), X_swap, op_b(b3), X_swap))

    def nested_rainbow(b1, b2, b3):
        return eta_swap(mat_mul(mat_mul(b1, eta_swap(b2)), b3))

    # 1-point separation for all 13 order-preserving un-nested operators at (E12, E11, E21)
    assert mu4_xswap(E12, E11, E21) == E22
    for pid in range(13):
        assert eval_unnested((0, 1, 2), pid, eta_swap, (E12, E11, E21))[1][1] == 0

    # 12-term +/-1 functional separation across all 78 permuted un-nested operators
    for perm in permutations(range(3)):
        for pid in range(13):
            val = phi_all(lambda b1, b2, b3, p=perm, pid=pid: eval_unnested(p, pid, eta_swap, (b1, b2, b3)))
            assert val == 0, f"phi_all non-zero at {perm}, {pid}: {val}"
    assert phi_all(nested_rainbow) == 1
    assert phi_all(mu4_xswap) == 1

    # Pure-component vanishing witness for B-free X1 = E11 \otimes s0, Y1 = E22 \otimes s1 at (E21, E11, E12)
    X1 = op_tensor(E11, op_s(0))
    Y1 = op_tensor(E22, op_s(1))
    Z1 = op_sum(X1, Y1)
    assert op_expectation(op_comp(X1, op_b(E21), X1, op_b(E11), X1, op_b(E12), X1)) == Z2
    assert op_expectation(op_comp(Y1, op_b(E21), Y1, op_b(E11), Y1, op_b(E12), Y1)) == Z2
    assert op_expectation(op_comp(Z1, op_b(E21), Z1)) == Z2
    assert op_expectation(op_comp(Z1, op_b(E12), Z1)) == Z2
    assert op_expectation(op_comp(Z1, op_b(E21), Z1, op_b(E11), Z1, op_b(E12), Z1)) == E22

    print("[PASS] Check 3: Un-nested block-weighting no-go theorem (all 78 operators) & pure-vanishing witness.")


# ============================================================================
# 5. Speicher's Nested Recursion, Central Factorization, and Depth <= 3 Polynomials
# ============================================================================

def eval_nc_stream(kappa, node, bs):
    if node is None:
        return I2, bs
    _, inners, tail = node
    args, bs1 = eval_gaps_stream(kappa, inners, bs)
    v_val = kappa(len(inners) + 1, tuple(args))
    if tail is None:
        return v_val, bs1
    b_sep, bs2 = bs1[0], bs1[1:]
    t_val, bs3 = eval_nc_stream(kappa, tail, bs2)
    return mat_mul(mat_mul(v_val, b_sep), t_val), bs3


def eval_gaps_stream(kappa, inners, bs):
    if not inners:
        return [], bs
    head, rest = inners[0], inners[1:]
    if head is None:
        b, bs1 = bs[0], bs[1:]
        r_args, bs2 = eval_gaps_stream(kappa, rest, bs1)
        return [b] + r_args, bs2
    b_open, bs1 = bs[0], bs[1:]
    mid_val, bs2 = eval_nc_stream(kappa, head, bs1)
    b_close, bs3 = bs2[0], bs2[1:]
    r_args, bs4 = eval_gaps_stream(kappa, rest, bs3)
    return [mat_mul(mat_mul(b_open, mid_val), b_close)] + r_args, bs4


def make_moment_oracle(op):
    memo = {}
    def mu(n, inner_bs):
        key = (n, inner_bs)
        if key in memo:
            return memo[key]
        seq = [op]
        for B in inner_bs:
            seq.append(op_b(B))
            seq.append(op)
        memo[key] = op_expectation(op_comp(*seq))
        return memo[key]
    return mu


def make_cumulant_oracle(mu):
    memo = {}
    def kappa(n, inner_bs):
        key = (n, inner_bs)
        if key in memo:
            return memo[key]
        decomps = enum_nc_decomp(n)
        full_blk = ("block", (None,) * (n - 1), None)
        rest = Z2
        for d in decomps:
            if d == full_blk:
                continue
            val, rem = eval_nc_stream(kappa, d, list(inner_bs))
            assert rem == []
            rest = mat_add(rest, val)
        memo[key] = mat_sub(mu(n, inner_bs), rest)
        return memo[key]
    return kappa


def verify_speicher_and_depth3():
    s0, s1 = op_s(0), op_s(1)
    X_ns = op_sum(op_b(E12), op_tensor(SIGMA_X, s0), op_tensor(E11, op_comp(s0, s0)))
    Y_ns = op_sum(op_b(E21), op_tensor(E11, s1), op_tensor(E22, op_comp(s1, s1)))
    Z_ns = op_sum(X_ns, Y_ns)

    mu_X = make_moment_oracle(X_ns)
    mu_Y = make_moment_oracle(Y_ns)
    mu_Z = make_moment_oracle(Z_ns)
    kap_X = make_cumulant_oracle(mu_X)
    kap_Y = make_cumulant_oracle(mu_Y)
    kap_Z_sum = lambda n, bs: mat_add(kap_X(n, bs), kap_Y(n, bs))

    def speicher_conv(n, bs):
        acc = Z2
        for d in enum_nc_decomp(n):
            val, rem = eval_nc_stream(kap_Z_sum, d, list(bs))
            assert rem == []
            acc = mat_add(acc, val)
        return acc

    # Exhaustive check for n = 1..4 (85 basis tuples) + structured checks for n = 5, 6 (depth 3)
    for n in range(1, 5):
        for bs in product(BASIS_MATS, repeat=n - 1):
            assert mu_Z(n, bs) == speicher_conv(n, bs)
    for bs5 in [(E12, E11, E22, E21), (SIGMA_X, E11, E12, I2), (I2, E21, E12, E22)]:
        assert mu_Z(5, bs5) == speicher_conv(5, bs5)
    for bs6 in [(E12, E11, E22, E21, I2), (SIGMA_X, E11, E12, E21, E22), (I2, I2, I2, I2, I2)]:
        assert mu_Z(6, bs6) == speicher_conv(6, bs6)

    # Verify all degree <= 3 monomial patterns via closed-form nested formulas
    for deg in range(4):
        for pat in product((0, 1), repeat=deg):
            for bs in product([E11, E12, E21, SIGMA_X], repeat=deg + 1):
                # Exact Fock evaluation
                seq = [op_b(bs[0])]
                for idx, v in enumerate(pat):
                    seq.append(X_ns if v == 0 else Y_ns)
                    seq.append(op_b(bs[idx + 1]))
                exact_val = op_expectation(op_comp(*seq))
                # Closed-form nested formula matching Lean `computeMonomDeg3`
                if deg == 0:
                    pred = bs[0]
                elif deg == 1:
                    m1 = mu_X(1, ()) if pat[0] == 0 else mu_Y(1, ())
                    pred = mat_list_prod([bs[0], m1, bs[1]])
                elif deg == 2:
                    if pat == (0, 0): core = mu_X(2, (bs[1],))
                    elif pat == (1, 1): core = mu_Y(2, (bs[1],))
                    elif pat == (0, 1): core = mat_list_prod([mu_X(1, ()), bs[1], mu_Y(1, ())])
                    else: core = mat_list_prod([mu_Y(1, ()), bs[1], mu_X(1, ())])
                    pred = mat_list_prod([bs[0], core, bs[2]])
                else:
                    if pat == (0, 0, 0): core = mu_X(3, (bs[1], bs[2]))
                    elif pat == (1, 1, 1): core = mu_Y(3, (bs[1], bs[2]))
                    elif pat == (0, 0, 1): core = mat_list_prod([mu_X(2, (bs[1],)), bs[2], mu_Y(1, ())])
                    elif pat == (1, 1, 0): core = mat_list_prod([mu_Y(2, (bs[1],)), bs[2], mu_X(1, ())])
                    elif pat == (0, 1, 1): core = mat_list_prod([mu_X(1, ()), bs[1], mu_Y(2, (bs[2],))])
                    elif pat == (1, 0, 0): core = mat_list_prod([mu_Y(1, ()), bs[1], mu_X(2, (bs[2],))])
                    elif pat == (0, 1, 0): core = mu_X(2, (mat_list_prod([bs[1], mu_Y(1, ()), bs[2]]),))
                    else: core = mu_Y(2, (mat_list_prod([bs[1], mu_X(1, ()), bs[2]]),))
                    pred = mat_list_prod([bs[0], core, bs[3]])
                assert exact_val == pred

    # Verify Central-Commutative Factorization over commutative diagonal subalgebra D_2(Q)
    X_cen = op_sum(op_b(diag_mat(1, 2)), op_tensor(diag_mat(2, -1), s0), op_tensor(diag_mat(1, 3), op_comp(s0, s0)))
    Y_cen = op_sum(op_b(diag_mat(-1, 1)), op_tensor(diag_mat(3, 2), s1))
    Z_cen = op_sum(X_cen, Y_cen)
    kap_Xc = make_cumulant_oracle(make_moment_oracle(X_cen))
    kap_Yc = make_cumulant_oracle(make_moment_oracle(Y_cen))
    mu_Zc = make_moment_oracle(Z_cen)

    def block_weight_prod(node, c_map):
        if node is None:
            return I2
        _, inners, tail = node
        acc = c_map(len(inners) + 1)
        for ch in inners:
            acc = mat_mul(acc, block_weight_prod(ch, c_map))
        return mat_mul(acc, block_weight_prod(tail, c_map))

    c_sum = lambda k: mat_add(kap_Xc(k, (I2,) * (k - 1)), kap_Yc(k, (I2,) * (k - 1)))
    diag_pool = [diag_mat(2, 3), diag_mat(-1, 4), diag_mat(5, -2)]
    for n in range(1, 7):
        bs = [diag_pool[i % 3] for i in range(n - 1)]
        weighted_sum = Z2
        for d in enum_nc_decomp(n):
            weighted_sum = mat_add(weighted_sum, block_weight_prod(d, c_sum))
        pred = mat_mul(mat_list_prod(bs), weighted_sum)
        assert mu_Zc(n, tuple(bs)) == pred

    print("[PASS] Check 4: Speicher nested recursion (n=1..6), degree<=3 universal evaluator, and central factorization.")


def main():
    print("=== Conjecture 00000004759 Exact Verification Suite ===")
    verify_nc_combinatorics()
    verify_moment_counterexamples()
    verify_unnested_no_go()
    verify_speicher_and_depth3()
    print("=== ALL VERIFICATION CHECKS PASSED (EXIT 0) ===")


if __name__ == "__main__":
    sys.exit(main() or 0)
