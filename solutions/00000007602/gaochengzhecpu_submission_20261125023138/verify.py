#!/usr/bin/env python3
"""
Exact computational verification for Conjecture 00000007602:
"Definition: The outer product as the fully antisymmetric part structure.
 Conjecture: The dimension-vanishing threshold of the outer product is exact and
 given by binomial zeros; and the realization of the threshold is full
 antisymmetrization."

Uses only Python 3.12 standard library exact arithmetic (fractions.Fraction,
modular integers mod p, and exact combinatorics) with zero floating-point
approximations.
"""

from __future__ import annotations

from fractions import Fraction
import itertools
import math
import sys
from typing import Dict, List, Sequence, Tuple


MultiIndex = Tuple[int, ...]
Perm = Tuple[int, ...]


def all_perms_with_sign(k: int) -> List[Tuple[Perm, int]]:
    """Return all permutations of {0, ..., k-1} paired with their sign in {+1, -1}."""
    result: List[Tuple[Perm, int]] = []
    for p in itertools.permutations(range(k)):
        inv = 0
        for i in range(k):
            for j in range(i + 1, k):
                if p[i] > p[j]:
                    inv += 1
        sgn = -1 if (inv % 2 == 1) else 1
        result.append((p, sgn))
    return result


def falling_factorial(x: Fraction, k: int) -> Fraction:
    """Evaluate x * (x - 1) * ... * (x - k + 1)."""
    prod = Fraction(1, 1)
    for j in range(k):
        prod *= (x - j)
    return prod


def binomial_poly(x: Fraction, k: int) -> Fraction:
    """Evaluate the rational binomial polynomial choose(x, k)."""
    return falling_factorial(x, k) / Fraction(math.factorial(k), 1)


def rref_rank_fraction(rows: List[List[Fraction]], ncols: int) -> int:
    """Compute exact rank of a matrix over Q using Gaussian elimination."""
    mat = [row[:] for row in rows]
    nrows = len(mat)
    r = 0
    for c in range(ncols):
        pivot = None
        for i in range(r, nrows):
            if mat[i][c] != 0:
                pivot = i
                break
        if pivot is None:
            continue
        mat[r], mat[pivot] = mat[pivot], mat[r]
        pv = mat[r][c]
        mat[r] = [val / pv for val in mat[r]]
        for i in range(nrows):
            if i != r and mat[i][c] != 0:
                factor = mat[i][c]
                mat[i] = [mat[i][j] - factor * mat[r][j] for j in range(ncols)]
        r += 1
    return r


def rref_rank_mod_p(rows: List[List[int]], ncols: int, p: int) -> int:
    """Compute exact rank of a matrix over F_p using Gaussian elimination."""
    mat = [[x % p for x in row] for row in rows]
    nrows = len(mat)
    r = 0
    for c in range(ncols):
        pivot = None
        for i in range(r, nrows):
            if mat[i][c] != 0:
                pivot = i
                break
        if pivot is None:
            continue
        mat[r], mat[pivot] = mat[pivot], mat[r]
        inv_pv = pow(mat[r][c], -1, p)
        mat[r] = [(val * inv_pv) % p for val in mat[r]]
        for i in range(nrows):
            if i != r and mat[i][c] != 0:
                factor = mat[i][c]
                mat[i] = [(mat[i][j] - factor * mat[r][j]) % p for j in range(ncols)]
        r += 1
    return r


def mat_mul_fraction(a: List[List[Fraction]], b: List[List[Fraction]]) -> List[List[Fraction]]:
    """Exact matrix multiplication over Q."""
    m = len(a)
    n = len(b)
    p = len(b[0]) if n > 0 else 0
    out = [[Fraction(0, 1) for _ in range(p)] for _ in range(m)]
    for i in range(m):
        for k_idx in range(n):
            aik = a[i][k_idx]
            if aik != 0:
                for j in range(p):
                    if b[k_idx][j] != 0:
                        out[i][j] += aik * b[k_idx][j]
    return out


def mat_mul_mod_p(a: List[List[int]], b: List[List[int]], p_mod: int) -> List[List[int]]:
    """Exact matrix multiplication over F_p."""
    m = len(a)
    n = len(b)
    p = len(b[0]) if n > 0 else 0
    out = [[0 for _ in range(p)] for _ in range(m)]
    for i in range(m):
        for k_idx in range(n):
            aik = a[i][k_idx]
            if aik != 0:
                for j in range(p):
                    if b[k_idx][j] != 0:
                        out[i][j] = (out[i][j] + aik * b[k_idx][j]) % p_mod
    return out


def build_alt_matrix_indices(n: int, k: int) -> Tuple[List[MultiIndex], List[List[int]]]:
    """
    Build the integer matrix of the unnormalized antisymmetrizer
    Alt_k : T^k(Z^n) -> T^k(Z^n) in the standard multi-index basis.
    Here (sigma . T)(I) = T(I o sigma), so on basis tensors E_J:
    Alt_k(E_J)(I) = sum_{sigma : I o sigma = J} sgn(sigma).
    """
    basis = list(itertools.product(range(n), repeat=k))
    idx_of = {mi: pos for pos, mi in enumerate(basis)}
    dim = len(basis)
    mat = [[0 for _ in range(dim)] for _ in range(dim)]
    perms = all_perms_with_sign(k)
    for col, j_mi in enumerate(basis):
        # (sigma . E_J)(I) = E_J(I o sigma) = 1 iff I = J o sigma^{-1}
        for sigma, sgn in perms:
            # Compute target I such that I[sigma[r]] = J[r]
            target = [0] * k
            for r in range(k):
                target[sigma[r]] = j_mi[r]
            row = idx_of[tuple(target)]
            mat[row][col] += sgn
    return basis, mat


def antisym_subspace_dim_q(n: int, k: int) -> int:
    """Exact dimension of A^k_sgn(Q^n) = {T : sigma . T = sgn(sigma) T for all sigma in S_k}."""
    basis = list(itertools.product(range(n), repeat=k))
    idx_of = {mi: pos for pos, mi in enumerate(basis)}
    dim = len(basis)
    if dim == 0:
        return 0
    equations: List[List[Fraction]] = []
    for sigma, sgn in all_perms_with_sign(k):
        for i_mi in basis:
            i_pos = idx_of[i_mi]
            permuted = tuple(i_mi[sigma[r]] for r in range(k))
            p_pos = idx_of[permuted]
            row = [Fraction(0, 1)] * dim
            row[p_pos] += Fraction(1, 1)
            row[i_pos] -= Fraction(sgn, 1)
            if any(x != 0 for x in row):
                equations.append(row)
    rank = rref_rank_fraction(equations, dim)
    return dim - rank


def antisym_subspace_dim_mod_p(n: int, k: int, p: int) -> int:
    """Exact dimension of A^k_sgn(F_p^n) = {T : sigma . T = sgn(sigma) T for all sigma in S_k}."""
    basis = list(itertools.product(range(n), repeat=k))
    idx_of = {mi: pos for pos, mi in enumerate(basis)}
    dim = len(basis)
    if dim == 0:
        return 0
    equations: List[List[int]] = []
    for sigma, sgn in all_perms_with_sign(k):
        for i_mi in basis:
            i_pos = idx_of[i_mi]
            permuted = tuple(i_mi[sigma[r]] for r in range(k))
            p_pos = idx_of[permuted]
            row = [0] * dim
            row[p_pos] = (row[p_pos] + 1) % p
            row[i_pos] = (row[i_pos] - sgn) % p
            if any(x != 0 for x in row):
                equations.append(row)
    rank = rref_rank_mod_p(equations, dim, p)
    return dim - rank


def check_1_binomial_zeros_and_strict_tuples() -> None:
    print("[Check 1] Binomial polynomial zeros and strictly increasing k-tuple basis...")
    for n in range(0, 8):
        for k in range(0, 9):
            c_nk = math.comb(n, k)
            poly_val = binomial_poly(Fraction(n, 1), k)
            assert poly_val == Fraction(c_nk, 1), f"Mismatch at n={n}, k={k}"
            strict_tuples = list(itertools.combinations(range(n), k))
            assert len(strict_tuples) == c_nk
            assert (c_nk == 0) == (k > n)
    for k in range(1, 8):
        roots = [m for m in range(-3, k + 5) if binomial_poly(Fraction(m, 1), k) == 0]
        assert roots == list(range(0, k)), f"Unexpected integer roots for k={k}: {roots}"
    print("  PASS: choose(n, k) == 0 <=> k > n, matching exact roots {0, ..., k-1} of choose(x, k).")


def check_2_char0_positive_theorem() -> None:
    print("[Check 2] Characteristic-0 positive theorem (exact Q linear algebra)...")
    test_pairs = [
        (1, 0), (1, 1), (1, 2), (1, 3),
        (2, 0), (2, 1), (2, 2), (2, 3), (2, 4),
        (3, 0), (3, 1), (3, 2), (3, 3), (3, 4),
        (4, 1), (4, 2), (4, 3),
    ]
    for n, k in test_pairs:
        _, int_mat = build_alt_matrix_indices(n, k)
        dim = len(int_mat)
        k_fact = Fraction(math.factorial(k), 1)
        alt_q = [[Fraction(val, 1) for val in row] for row in int_mat]
        pi_q = [[val / k_fact for val in row] for row in alt_q]

        # Verify Alt_k^2 = k! Alt_k and Pi_k^2 = Pi_k
        pi_sq = mat_mul_fraction(pi_q, pi_q)
        assert pi_sq == pi_q, f"Pi_k not idempotent at (n={n}, k={k})"

        rank_pi = rref_rank_fraction(pi_q, dim)
        dim_antisym = antisym_subspace_dim_q(n, k)
        expected = math.comb(n, k)
        assert rank_pi == expected, f"rank(Pi_{k})={rank_pi} != {expected} at n={n}"
        assert dim_antisym == expected, f"dim A^{k}_sgn={dim_antisym} != {expected} at n={n}"

        is_zero_op = all(val == 0 for row in pi_q for val in row)
        assert is_zero_op == (k > n), f"Threshold mismatch at (n={n}, k={k})"

    # Also verify top degree n=4, k=4 directly via coordinate projection on strictly mono tuple
    _, int_mat_44 = build_alt_matrix_indices(4, 4)
    assert any(val != 0 for row in int_mat_44 for val in row)
    # And n=4, k=5 pigeonhole vanishing on arbitrary basis checks
    for i_mi in itertools.product(range(4), repeat=5):
        assert len(set(i_mi)) < 5
    print("  PASS: Over Q, Pi_k = (1/k!) Alt_k is idempotent, rank(Pi_k) = dim A^k_sgn(Q^n) = choose(n, k),")
    print("        and Pi_k == 0 <=> k > n <=> choose(n, k) == 0.")


def check_3_char_p_refutations() -> None:
    print("[Check 3] Positive-characteristic refutations (F_2 and F_3 exact linear algebra)...")
    # 3a. Over F_2, A^k_sgn(F_2^n) = ((F_2^n)^{tensor k})^{S_k} has dim choose(n + k - 1, k) >= 1 for ALL k > n >= 1
    print("  [3a] Dimension of A^k_sgn(F_2^n) vs choose(n, k):")
    for n in (1, 2, 3):
        dims_str = []
        for k in (1, 2, 3, 4):
            dim_f2 = antisym_subspace_dim_mod_p(n, k, 2)
            expected_sym = math.comb(n + k - 1, k)
            assert dim_f2 == expected_sym, (
                f"F_2 antisym dim mismatch at (n={n}, k={k}): got {dim_f2}, expected {expected_sym}"
            )
            dims_str.append(f"k={k}: dim A^k_sgn={dim_f2} (choose({n},{k})={math.comb(n,k)})")
            if k > n:
                assert math.comb(n, k) == 0 and dim_f2 >= 1
        print(f"       n={n}: " + "; ".join(dims_str))

    # Concrete witness checks at n=2, k=2 and n=2, k=3
    assert antisym_subspace_dim_mod_p(2, 2, 2) == 3 and math.comb(2, 2) == 1
    assert antisym_subspace_dim_mod_p(2, 3, 2) == 4 and math.comb(2, 3) == 0

    # 3b. Nilpotence Alt_k^2 == 0 and non-existence of (1/k!) Alt_k when p <= k <= n
    for p, n, k in [(2, 2, 2), (2, 3, 2), (2, 3, 3), (3, 3, 3)]:
        assert math.factorial(k) % p == 0
        _, int_mat = build_alt_matrix_indices(n, k)
        dim = len(int_mat)
        alt_p = [[val % p for val in row] for row in int_mat]
        alt_p_sq = mat_mul_mod_p(alt_p, alt_p, p)
        rank_alt_p = rref_rank_mod_p(alt_p, dim, p)
        assert rank_alt_p == math.comb(n, k) >= 1
        assert all(val == 0 for row in alt_p_sq for val in row), (
            f"Expected Alt_{k}^2 == 0 mod {p} at n={n}"
        )
    print("  [3b] PASS: For p <= k <= n (e.g. p=2,n=2,k=2 and p=3,n=3,k=3), k! == 0 mod p,")
    print("       rank(Alt_k) = choose(n,k) >= 1, yet Alt_k o Alt_k == 0 (nilpotent, not a projection).")

    # 3c. Iterated outer product failure via Alt_{r+s} on alternating tensors below/at threshold
    # p=2, n=3, r=2, s=1 => r+s = 3 = n, choose(3,3) = 1 != 0
    basis_33, int_mat_33 = build_alt_matrix_indices(3, 3)
    idx_33 = {mi: pos for pos, mi in enumerate(basis_33)}
    alt_33_f2 = [[val % 2 for val in row] for row in int_mat_33]
    # omega_01 = e_0 tensor e_1 + e_1 tensor e_0, tensored with e_2 gives E_(0,1,2) + E_(1,0,2)
    vec = [0] * len(basis_33)
    vec[idx_33[(0, 1, 2)]] = 1
    vec[idx_33[(1, 0, 2)]] = 1
    out_vec = [
        sum(alt_33_f2[row][col] * vec[col] for col in range(len(basis_33))) % 2
        for row in range(len(basis_33))
    ]
    assert all(x == 0 for x in out_vec), "Expected Alt_3((e0^e1) tensor e2) == 0 over F_2"
    # Whereas Alt_3(e0 tensor e1 tensor e2) is the non-zero volume alternating tensor!
    vol_col = [alt_33_f2[row][idx_33[(0, 1, 2)]] for row in range(len(basis_33))]
    assert any(x != 0 for x in vol_col)
    print("  [3c] PASS: Over F_2^3 (n=3, choose(3,3)=1), omega_01 = Alt_2(e_0 tensor e_1) != 0,")
    print("       yet full antisymmetrization Alt_3(omega_01 tensor e_2) == 0 prematurely at k=3=n.")

    # 3d. Modular Lucas binomial zeros in F_p vs actual exterior dimension choose(n, k)
    lucas_mismatches = []
    for p in (2, 3, 5):
        for n in range(1, 7):
            for k in range(1, n):
                c = math.comb(n, k)
                if c % p == 0 and c > 0:
                    lucas_mismatches.append((p, n, k, c))
    assert (2, 2, 1, 2) in lucas_mismatches and (2, 4, 2, 6) in lucas_mismatches
    print(f"  [3d] PASS: Found {len(lucas_mismatches)} modular Lucas zeros (choose(n,k) == 0 mod p while dim Lambda^k = choose(n,k) > 0),")
    print("       minimal example: p=2, n=2, k=1 has choose(2,1) = 2 == 0 in F_2 while dim Lambda^1(F_2^2) = 2.")


class CliffordElement:
    """Exact element of Euclidean Clifford / exterior algebra over Q in dimension n."""

    def __init__(self, n: int, coeffs: Dict[ int, Fraction ] | None = None) -> None:
        self.n = n
        self.coeffs: Dict[int, Fraction] = {}
        if coeffs:
            for mask, val in coeffs.items():
                if val != 0:
                    self.coeffs[mask] = val

    @staticmethod
    def blade(n: int, indices: Sequence[int], coeff: Fraction = Fraction(1, 1)) -> "CliffordElement":
        mask = 0
        sign = 1
        for idx in indices:
            assert 0 <= idx < n
            # Count bits > idx already set
            higher = mask >> (idx + 1)
            if bin(higher).count("1") % 2 == 1:
                sign = -sign
            if (mask >> idx) & 1:
                # Repeated index in Euclidean Clifford e_i^2 = +1
                mask ^= (1 << idx)
            else:
                mask |= (1 << idx)
        return CliffordElement(n, {mask: coeff * sign})

    def __add__(self, other: "CliffordElement") -> "CliffordElement":
        assert self.n == other.n
        out = dict(self.coeffs)
        for m, v in other.coeffs.items():
            out[m] = out.get(m, Fraction(0, 1)) + v
        return CliffordElement(self.n, out)

    def __sub__(self, other: "CliffordElement") -> "CliffordElement":
        assert self.n == other.n
        out = dict(self.coeffs)
        for m, v in other.coeffs.items():
            out[m] = out.get(m, Fraction(0, 1)) - v
        return CliffordElement(self.n, out)

    def scale(self, c: Fraction) -> "CliffordElement":
        return CliffordElement(self.n, {m: v * c for m, v in self.coeffs.items()})

    def is_zero(self) -> bool:
        return len(self.coeffs) == 0

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CliffordElement):
            return False
        return self.n == other.n and self.coeffs == other.coeffs

    @staticmethod
    def _koszul_sign(a_mask: int, b_mask: int, n: int) -> int:
        swaps = 0
        for i in range(n):
            if (a_mask >> i) & 1:
                # Count j < i in b_mask
                lower_b = b_mask & ((1 << i) - 1)
                swaps += bin(lower_b).count("1")
        return -1 if (swaps % 2 == 1) else 1

    def cliff_mul(self, other: "CliffordElement") -> "CliffordElement":
        """Geometric product in Cl_{n,0}(Q) with e_i^2 = +1."""
        assert self.n == other.n
        out: Dict[int, Fraction] = {}
        for am, av in self.coeffs.items():
            for bm, bv in other.coeffs.items():
                sgn = self._koszul_sign(am, bm, self.n)
                target = am ^ bm
                out[target] = out.get(target, Fraction(0, 1)) + av * bv * sgn
        return CliffordElement(self.n, out)

    def wedge(self, other: "CliffordElement") -> "CliffordElement":
        """Exterior (Grassmann) product in Lambda(Q^n)."""
        assert self.n == other.n
        out: Dict[int, Fraction] = {}
        for am, av in self.coeffs.items():
            for bm, bv in other.coeffs.items():
                if (am & bm) == 0:
                    sgn = self._koszul_sign(am, bm, self.n)
                    target = am | bm
                    out[target] = out.get(target, Fraction(0, 1)) + av * bv * sgn
        return CliffordElement(self.n, out)

    def grade_proj(self, g: int) -> "CliffordElement":
        return CliffordElement(
            self.n,
            {m: v for m, v in self.coeffs.items() if bin(m).count("1") == g},
        )


def check_4_char0_multivector_refutations() -> None:
    print("[Check 4] Characteristic-0 higher-grade multivector checks in Lambda(Q^n) and Cl_{n,0}(Q)...")
    half = Fraction(1, 2)

    # 4a. Confirm grade-1 vectors DO satisfy (1/k!) sum sgn(sigma) u_{sigma(1)}...u_{sigma(k)} == u_1 ^ ... ^ u_k
    for n in (3, 4):
        basis_vecs = [CliffordElement.blade(n, [i]) for i in range(n)]
        for k in range(1, n + 2):
            sample = [basis_vecs[i % n] for i in range(k)]
            wedge_prod = CliffordElement(n, {0: Fraction(1, 1)})
            for u in sample:
                wedge_prod = wedge_prod.wedge(u)
            antisym_prod = CliffordElement(n, {})
            for sigma, sgn in all_perms_with_sign(k):
                term = CliffordElement(n, {0: Fraction(sgn, 1)})
                for r in range(k):
                    term = term.cliff_mul(sample[sigma[r]])
                antisym_prod = antisym_prod + term
            antisym_prod = antisym_prod.scale(Fraction(1, math.factorial(k)))
            assert antisym_prod == wedge_prod

    # 4b. Verify <A B>_{r+s} == A ^ B for all homogeneous basis blades in n=4
    for am in range(16):
        ga = bin(am).count("1")
        a_el = CliffordElement(4, {am: Fraction(1, 1)})
        for bm in range(16):
            gb = bin(bm).count("1")
            b_el = CliffordElement(4, {bm: Fraction(1, 1)})
            assert a_el.cliff_mul(b_el).grade_proj(ga + gb) == a_el.wedge(b_el)

    # 4c. Premature vanishing at n=4, r=s=2, r+s=4=n (choose(4,4) = 1 != 0)
    a4 = CliffordElement.blade(4, [0, 1])  # e_0 ^ e_1
    b4 = CliffordElement.blade(4, [2, 3])  # e_2 ^ e_3
    vol4 = CliffordElement.blade(4, [0, 1, 2, 3])
    assert a4.wedge(b4) == vol4 and not vol4.is_zero()
    assert a4.cliff_mul(b4).grade_proj(4) == vol4
    wedge_comm_4 = (a4.wedge(b4) - b4.wedge(a4)).scale(half)
    cliff_comm_4 = (a4.cliff_mul(b4) - b4.cliff_mul(a4)).scale(half)
    assert wedge_comm_4.is_zero() and cliff_comm_4.is_zero()
    print("  [4a] PASS: In Cl_{4,0}(Q) / Lambda(Q^4) at r+s = 4 = n (choose(4,4)=1),")
    print("       A = e_0^e_1, B = e_2^e_3 satisfy A ^ B = e_0123 != 0, yet (1/2)(AB - BA) = (1/2)(A^B - B^A) = 0.")

    # 4d. Non-vanishing above the threshold at n=3, r=s=2, r+s=4 > 3 (choose(3,4) = 0)
    a3 = CliffordElement.blade(3, [0, 1])  # e_0 e_1
    b3 = CliffordElement.blade(3, [1, 2])  # e_1 e_2
    e02 = CliffordElement.blade(3, [0, 2])
    assert math.comb(3, 4) == 0
    assert a3.wedge(b3).is_zero() and a3.cliff_mul(b3).grade_proj(4).is_zero()
    cliff_comm_3 = (a3.cliff_mul(b3) - b3.cliff_mul(a3)).scale(half)
    assert cliff_comm_3 == e02 and not cliff_comm_3.is_zero()

    # Also 3-fold bivector antisymmetrization at total grade 6 > 3 (choose(3,6) = 0)
    c3 = CliffordElement.blade(3, [2, 0])  # e_2 e_0
    tri_alt = CliffordElement(3, {})
    tri = [a3, b3, c3]
    for sigma, sgn in all_perms_with_sign(3):
        term = tri[sigma[0]].cliff_mul(tri[sigma[1]]).cliff_mul(tri[sigma[2]]).scale(Fraction(sgn, 6))
        tri_alt = tri_alt + term
    scalar_one = CliffordElement(3, {0: Fraction(1, 1)})
    assert tri_alt == scalar_one and not tri_alt.is_zero()
    print("  [4b] PASS: In Cl_{3,0}(Q) at total grade 4 > 3 (choose(3,4)=0), A = e_0 e_1, B = e_1 e_2")
    print("       satisfy A ^ B = <AB>_4 = 0, yet (1/2)(AB - BA) = e_0 e_2 != 0 (and 3-fold Alt_3/6 = 1 != 0 at grade 6 > 3).")


def main() -> int:
    print("=" * 78)
    print("Verification Suite for Conjecture 00000007602")
    print("=" * 78)
    check_1_binomial_zeros_and_strict_tuples()
    check_2_char0_positive_theorem()
    check_3_char_p_refutations()
    check_4_char0_multivector_refutations()
    print("=" * 78)
    print("ALL VERIFICATION CHECKS PASSED (EXIT 0).")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
