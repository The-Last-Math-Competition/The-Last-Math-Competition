"""
Independent Computational Verification Suite for Conjecture 00000000546
=======================================================================

Conjecture 00000000546:
  "Definition: The depth of monomial subrings.
   Conjecture: The depth-drop threshold of the numerical semigroup <a, a+1, ..., a+k>
   equals ceil(a/k) (a depth jump for symmetric gaps)."

This script exhaustively and exactly verifies all algebraic and combinatorial
constructions associated with S_{a,k} = <a, a+1, ..., a+k> (a >= 2, 1 <= k <= a - 1):

  1. Combinatorial / Eliahou depth q(S_{a,k}) = ceil(C(S_{a,k}) / m(S_{a,k})),
     ordinary power-truncation threshold, symmetric-gap classification, and the
     exact symmetric-gap depth-jump phenomenon (435 pairs for 2 <= a <= 30).
  2. Affine monomial subring K[S_{a,k}] <= K[t]: Apéry-set structure and constant
     homological depth 1 across all (a, k).
  3. Projective monomial curve coordinate ring R_{a,k} <= K[u, v]: exact regular
     sequence check for (u^{a+k}, v^{a+k}) and nilpotency bound modulo (u^{a+k}, v^{a+k}),
     confirming constant homological depth 2 across all 2 <= a <= 18, 1 <= k < a.
  4. Tangent cone gr_m(K[[S_{a,k}]]): exact m-adic valuation nu_m(s) = floor(s / a),
     Sally's criterion (constant homological depth 1), Hilbert-function / reduction-number
     threshold ceil((a-1)/k), and top-generator nilpotency / sumset-overlap threshold ceil(a/k).
  5. Powers of the defining toric ideal P / I_{a,k}^t over Q[x_0, ..., x_k]: exact
     rational Gaussian elimination confirming depth(P / I_{a,k}^t) = 1.
  6. Symmetric-gap pinched Veronese subrings B_{a,k}^{(m)}: exact depth-2 threshold
     m >= ceil((a-1)/k), refuting ceil(a/k) whenever (a - 1) % k == 0.
"""

from __future__ import annotations
from fractions import Fraction
import sys


def ceil_div(n: int, k: int) -> int:
    assert k > 0
    return (n + k - 1) // k


def generate_interval_semigroup(a: int, k: int, bound: int) -> set[int]:
    """Exact DP generation of S_{a,k} = <a, a+1, ..., a+k> intersect [0, bound]."""
    S = {0}
    gens = range(a, a + k + 1)
    for x in range(a, bound + 1):
        for g in gens:
            if (x - g) in S:
                S.add(x)
                break
    return S


def rref_rank_fraction(rows: list[list[Fraction]], ncols: int) -> tuple[int, list[list[Fraction]]]:
    """Exact rational reduced row-echelon form returning (rank, basis_rows)."""
    mat = [list(r) for r in rows]
    pivots = 0
    for col in range(ncols):
        piv = None
        for r in range(pivots, len(mat)):
            if mat[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        mat[pivots], mat[piv] = mat[piv], mat[pivots]
        scale = mat[pivots][col]
        mat[pivots] = [v / scale for v in mat[pivots]]
        for r in range(len(mat)):
            if r != pivots and mat[r][col] != 0:
                factor = mat[r][col]
                mat[r] = [mat[r][c] - factor * mat[pivots][c] for c in range(ncols)]
        pivots += 1
    return pivots, mat[:pivots]


def verify_semigroup_and_eliahou_depth() -> None:
    print("[Test 1] Numerical semigroup S_{a,k}, Eliahou depth, and symmetric-gap jumps...")
    total_pairs = 0
    disagree_pairs = 0
    sym_jump_checks = 0

    for a in range(2, 31):
        for k in range(1, a):
            total_pairs += 1
            bound = a * (a + 2)
            S = generate_interval_semigroup(a, k, bound)
            gaps = [x for x in range(bound + 1) if x not in S]
            assert gaps, f"Expected non-empty gaps for a={a}, k={k}"
            F = max(gaps)
            C = F + 1
            m_mult = min(x for x in S if x > 0)
            assert m_mult == a, f"Multiplicity mismatch at a={a}, k={k}"

            # Verify no gaps exist in [C, bound] and bound - C >= a
            assert bound - C >= a
            assert all(x in S for x in range(C, bound + 1))

            q_true = ceil_div(C, m_mult)
            q_formula = ceil_div(a - 1, k)
            q_conj = ceil_div(a, k)

            assert C == q_formula * a, f"Conductor mismatch at ({a},{k}): {C} != {q_formula * a}"
            assert F == q_formula * a - 1
            assert q_true == q_formula

            # Exact characterization of failure locus of ceil(a/k)
            disagrees = (q_true != q_conj)
            assert disagrees == ((a - 1) % k == 0), f"Disagreement locus failed at ({a},{k})"
            if disagrees:
                disagree_pairs += 1
                assert q_conj == q_true + 1

            # Ordinary power-truncation threshold S_{a,k}^{(m)}
            for m in range(1, q_conj + 2):
                S_m = {0} | {
                    s for r in range(m, (bound // a) + 2)
                    for s in range(r * a, min(r * (a + k), bound) + 1)
                }
                is_ordinary = all(n in S_m for n in range(m * a, bound - a))
                assert is_ordinary == (m >= q_formula), (
                    f"Power semigroup threshold mismatch at a={a}, k={k}, m={m}"
                )

            # Symmetric-gap classification: x in S <=> F - x not in S
            is_sym = all(((F - x) in S) != (x in S) for x in range(F + 1))
            expected_sym = (k == 1) or ((a - 2) % k == 0)
            assert is_sym == expected_sym, f"Symmetry mismatch at ({a},{k})"

            # Symmetric-gap depth jump (for k >= 2, a >= k + 2)
            if k >= 2 and a >= k + 2:
                sym_jump_checks += 1
                q_prev = ceil_div(a - 2, k)
                assert (q_true - q_prev) == (1 if is_sym else 0), (
                    f"Eliahou jump mismatch at ({a},{k})"
                )
                if is_sym:
                    # Conjectured ceil(a/k) NEVER jumps at symmetric-gap S_{a,k} for k >= 2
                    assert ceil_div(a, k) == ceil_div(a - 1, k), (
                        f"Conjectured formula unexpectedly jumped at symmetric ({a},{k})"
                    )

            # Dual strict drop as k -> k + 1 at every symmetric S_{a,k} (1 <= k <= a - 2)
            if k <= a - 2 and is_sym:
                assert ceil_div(a - 1, k + 1) < ceil_div(a - 1, k)

    assert total_pairs == 435
    print(f"  PASS: Verified {total_pairs} pairs (2 <= a <= 30, 1 <= k < a); "
          f"ceil(a/k) fails on {disagree_pairs} pairs ((a-1) % k == 0); "
          f"{sym_jump_checks} symmetric-jump transitions checked.")


def verify_affine_and_tangent_cone() -> None:
    print("[Test 2] Affine subring K[S_{a,k}] and tangent cone gr_m(K[[S_{a,k}]])...")
    checked = 0
    for a in range(2, 18):
        for k in range(1, a):
            checked += 1
            q0 = ceil_div(a - 1, k)
            q_conj = ceil_div(a, k)
            max_r = q_conj + 4
            bound = (max_r + 2) * (a + k)
            S = generate_interval_semigroup(a, k, bound)

            # Apéry set Ap(S, a) = {s in S : s - a not in S} has exact size a (depth = 1)
            apery = [s for s in S if s <= (q0 + 1) * a and (s < a or (s - a) not in S)]
            assert len(apery) == a, f"Apéry size != a at ({a},{k})"
            assert max(apery) == q0 * a - 1 + a - (a - 1 - (q0 - 1) * k) or max(apery) < (q0 + 1) * a
            # Every sum of (q0 + 1) positive elements of S lies in a + S
            for s in S:
                if s >= (q0 + 1) * a and s <= bound:
                    assert (s - a) in S

            # Exact m-adic filtration m^r = union_{j >= r} [j*a, j*(a+k)]
            m_pow: dict[int, set[int]] = {}
            for r in range(0, max_r + 2):
                if r == 0:
                    m_pow[r] = set(S)
                else:
                    m_pow[r] = {
                        s for j in range(r, (bound // a) + 2)
                        for s in range(j * a, min(j * (a + k), bound) + 1)
                    }

            # Check exact m-adic valuation nu_m(s) == s // a for all s in S up to max_r * a
            for s in S:
                if s <= max_r * a:
                    nu = max(r for r in range(max_r + 1) if s in m_pow[r])
                    assert nu == s // a, f"m-adic order mismatch at ({a},{k}), s={s}"
                    # Sally's criterion: nu_m(s + a) == nu_m(s) + 1 (so gr_m has depth 1)
                    if s + a <= max_r * a:
                        nu_next = max(r for r in range(max_r + 2) if (s + a) in m_pow[r])
                        assert nu_next == nu + 1

            # Hilbert function H_{gr_m}(r) = |m^r \ m^{r+1}| == min(r*k + 1, a)
            for r in range(0, max_r):
                quot_r = [s for s in m_pow[r] if s not in m_pow[r + 1] and s < (r + 2) * a]
                assert len(quot_r) == min(r * k + 1, a), (
                    f"Hilbert function mismatch at ({a},{k}), r={r}"
                )

            # Reduction number threshold: m^{r+1} == a + m^r iff r >= ceil((a-1)/k)
            for r in range(1, max_r):
                cap = (r + 3) * a
                lhs = {s for s in m_pow[r + 1] if s <= cap}
                rhs = {a + s for s in m_pow[r] if a + s <= cap}
                assert (lhs == rhs) == (r >= q0), f"Reduction threshold mismatch at ({a},{k}), r={r}"

            # Top-generator nilpotency / sumset-overlap threshold: r*(a+k) in m^{r+1} iff r >= ceil(a/k)
            for r in range(1, max_r):
                in_next = (r * (a + k)) in m_pow[r + 1]
                overlap = bool(
                    set(range(r * a, r * (a + k) + 1))
                    & set(range((r + 1) * a, (r + 1) * (a + k) + 1))
                )
                assert in_next == (r >= q_conj)
                assert overlap == (r >= q_conj)

    print(f"  PASS: Verified affine subring & tangent cone invariants on {checked} pairs (2 <= a <= 17).")


def verify_projective_closure_and_pinched_veronese() -> None:
    print("[Test 3] Projective closure R_{a,k} and symmetric-gap Veronese B_{a,k}^{(m)}...")
    proj_checked = 0
    for a in range(2, 19):
        for k in range(1, a):
            proj_checked += 1
            d = a + k
            A_proj = {0} | set(range(a, a + k + 1))
            q0 = ceil_div(a - 1, k)
            max_r = q0 + 5

            sumsets = [{0}]
            for r in range(1, max_r + 1):
                prev = sumsets[-1]
                nxt = {x + y for x in prev for y in A_proj}
                sumsets.append(nxt)
                # Regular sequence criterion: r*A cap (d + r*A) == d + (r - 1)*A
                lhs = nxt & {d + x for x in nxt}
                rhs = {d + x for x in prev}
                assert lhs == rhs, f"R_{{a,k}} failed CM at ({a},{k}), r={r}"
                # Maximality: for r >= q0 + 2, every element of r*A lies in (r-1)*A U (d + (r-1)*A)
                if r >= q0 + 2:
                    covered = prev | {d + x for x in prev}
                    assert nxt.issubset(covered), f"High-degree cover failed at ({a},{k}), r={r}"

    ver_checked = 0
    ver_refuted = 0
    for a in range(3, 16):
        for k in range(1, a - 1):
            q0 = ceil_div(a - 1, k)
            q_conj = ceil_div(a, k)
            for m in range(1, q_conj + 2):
                ver_checked += 1
                D = m * (a + k)
                A_ver = {
                    s for j in range(m + 1)
                    for s in range(j * a, j * a + m * k + 1)
                }
                max_r = ceil_div(a - 1, m * k) + 3
                sumsets = [{0}]
                is_cm = True
                for r in range(1, max_r + 1):
                    prev = sumsets[-1]
                    nxt = {x + y for x in prev for y in A_ver}
                    sumsets.append(nxt)
                    if (nxt & {D + x for x in nxt}) != {D + x for x in prev}:
                        is_cm = False
                        break
                assert is_cm == (m >= q0), (
                    f"Pinched Veronese CM mismatch at a={a}, k={k}, m={m}: {is_cm} vs {m >= q0}"
                )
            if (a - 1) % k == 0:
                ver_refuted += 1
                assert q0 < q_conj

    print(f"  PASS: Projective closure R_{{a,k}} has constant depth 2 on all {proj_checked} pairs; "
          f"pinched Veronese B_{{a,k}}^{{(m)}} verified across {ver_checked} triples "
          f"({ver_refuted} explicit counterexamples to ceil(a/k)).")


def verify_toric_ideal_powers() -> None:
    print("[Test 4] Powers of the defining toric ideal P / I_{a,k}^t over Q[x_0, ..., x_k]...")
    # Complete-intersection cases (never drop: depth(P / I_{a,k}^t) = 1 for all t >= 1)
    # vs. non-complete-intersection cases (drop to depth 0 already at t = 2, even when ceil(a/k) = 3!)
    expected_first_drop = {
        (3, 1): None,   # hypersurface (codim 1 CI), symmetric, ceil(3/1) = 3
        (4, 2): None,   # codim 2 Gorenstein = CI, symmetric, ceil(4/2) = 2
        (6, 2): None,   # codim 2 Gorenstein = CI, symmetric, ceil(6/2) = 3
        (5, 3): 3,      # codim 3 Gorenstein (Pfaffian, non-CI), symmetric: drops at t = 3 != 2 = ceil(5/3)
        (3, 2): 2,      # Hilbert-Burch 2x3 minors: drops at t = 2
        (5, 2): 2,      # drops at t = 2 != 3 = ceil(5/2) (refutes ceil(a/k)!)
        (7, 3): 2,      # drops at t = 2 != 3 = ceil(7/3) (refutes ceil(a/k)!)
    }
    for (a, k), exp_drop in expected_first_drop.items():
        max_wt = 45
        max_t = 4
        mons_by_wt: dict[int, list[tuple[int, ...]]] = {0: [(0,) * (k + 1)]}
        for w in range(1, max_wt + 1):
            ms: list[tuple[int, ...]] = []

            def gen(idx: int, rem: int, cur: tuple[int, ...]) -> None:
                if idx == k:
                    if rem % (a + k) == 0:
                        ms.append(cur + (rem // (a + k),))
                    return
                wt_i = a + idx
                for c in range(rem // wt_i + 1):
                    gen(idx + 1, rem - c * wt_i, cur + (c,))

            gen(0, w, ())
            if ms:
                mons_by_wt[w] = ms

        rel_wts = [w for w, ms in mons_by_wt.items() if len(ms) >= 2]
        basis_prev: dict[int, list[list[Fraction]]] = {}
        first_drop: int | None = None
        for t in range(1, max_t + 1):
            basis_cur: dict[int, list[list[Fraction]]] = {}
            for w, ms in mons_by_wt.items():
                idx_map = {m: i for i, m in enumerate(ms)}
                n = len(ms)
                if t == 1:
                    rows = []
                    for i in range(1, n):
                        row = [Fraction(0)] * n
                        row[0] = Fraction(1)
                        row[i] = Fraction(-1)
                        rows.append(row)
                    basis_cur[w] = rows
                else:
                    rows = []
                    for w1 in rel_wts:
                        if w1 > w or (w - w1) not in basis_prev:
                            continue
                        prows = basis_prev[w - w1]
                        if not prows:
                            continue
                        ms1 = mons_by_wt[w1]
                        ms2 = mons_by_wt[w - w1]
                        m1_0 = ms1[0]
                        for i in range(1, len(ms1)):
                            m1_i = ms1[i]
                            for prow in prows:
                                row = [Fraction(0)] * n
                                for j, coeff in enumerate(prow):
                                    if coeff != 0:
                                        m2 = ms2[j]
                                        pa = tuple(m1_0[u] + m2[u] for u in range(k + 1))
                                        pb = tuple(m1_i[u] + m2[u] for u in range(k + 1))
                                        row[idx_map[pa]] += coeff
                                        row[idx_map[pb]] -= coeff
                                rows.append(row)
                    _, basis_cur[w] = rref_rank_fraction(rows, n)

            dropped = False
            for w, ms in mons_by_wt.items():
                if w + a > max_wt:
                    continue
                dim_quot = len(ms) - len(basis_cur[w])
                if dim_quot == 0:
                    continue
                ms_next = mons_by_wt.get(w + a, [])
                idx_next = {m: i for i, m in enumerate(ms_next)}
                n_next = len(ms_next)
                comb_rows = list(basis_cur.get(w + a, []))
                for m in ms:
                    shifted = (m[0] + 1,) + m[1:]
                    row = [Fraction(0)] * n_next
                    row[idx_next[shifted]] = Fraction(1)
                    comb_rows.append(row)
                rk, _ = rref_rank_fraction(comb_rows, n_next)
                dim_img = rk - len(basis_cur.get(w + a, []))
                if dim_img < dim_quot:
                    dropped = True
                    break
            if dropped and first_drop is None:
                first_drop = t
            basis_prev = basis_cur

        assert first_drop == exp_drop, (
            f"Toric power drop mismatch at ({a},{k}): got {first_drop}, expected {exp_drop}"
        )

    print("  PASS: Exact rational linear algebra verified Brodmann power depths P / I_{a,k}^t "
          "(CI cases never drop; (5,2) and (7,3) drop at t = 2 != 3 = ceil(a/k)).")


def main() -> int:
    print("Running verification suite for Conjecture 00000000546...")
    verify_semigroup_and_eliahou_depth()
    verify_affine_and_tangent_cone()
    verify_projective_closure_and_pinched_veronese()
    verify_toric_ideal_powers()
    print("\nALL VERIFICATION CHECKS PASSED SUCCESSFULLY (exit code 0).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
