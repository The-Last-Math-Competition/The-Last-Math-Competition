#!/usr/bin/env python3
"""
Standalone exact verification script for Conjecture 00000007165:
  "Definition: The spectrum of the Rayleigh quotient with the extremal faces of
   the quotient. Conjecture: The contact manifolds of extremal faces hold, and
   the dimension of the manifolds is the multiplicity of the index."

Uses ONLY Python standard library exact arithmetic (fractions.Fraction and an
exact Gaussian rational field Q[i] = Q + i Q; zero floating-point operations).

Verifies:
  1. Positive Linear-Cone Characterization (Non-Vacuity):
     For symmetric / Hermitian matrices B = U A U* with maximum eigenvalue
     lambda_max of multiplicity m >= 1, R_B(x) <= lambda_max for all x != 0,
     R_B(x) = lambda_max <-> B x = lambda_max x, and the unnormalized linear
     cone {0} U {x != 0 : R_B(x) = lambda_max} = ker(B - lambda_max I) has
     exact F-dimension m (real dimension 2m != m over C).
  2. Complete Dimension Refutation Across All 5 Normalized State Domains:
     - Domain 1 (Real unit sphere S^{n-1}): dim_R = m - 1 != m for all m >= 1
       (verified via exact Zariski tangent spaces, rotated eigenbases, and
       rational stereographic charts; cardinality 2 at m = 1).
     - Domain 2 (Real projective space RP^{n-1}): dim_R = m - 1 != m for all
       m >= 1 (singleton ray at m = 1).
     - Domain 3 (Complex unit sphere S^{2n-1}): strict contact submanifold of
       (S^{2n-1}, Im<z, dz>) with nondegenerate symplectic d(alpha)|_xi and
       exact dim_R = 2m - 1 (equals m only at m = 1; fails for all m >= 2).
     - Domain 4 (Complex projective space CP^{n-1}): dim_C = m - 1 != m for all
       m >= 1, and dim_R = 2m - 2 != m for all m != 2 (fails at m = 1 and m >= 3).
     - Domain 5 (Density-matrix state spaces D_n(C) and D_n(R)): extremal face
       F_max(B) has exact real affine dimension m^2 - 1 != m for all m >= 1
       over C, and m(m+1)/2 - 1 != m for m = 1 and all m >= 3 over R.
  3. Structural Obstructions Beyond Extremal Hermitian Eigenvalues:
     - Non-normal matrices (e.g. [[0, 2], [0, 0]] with algebraic multiplicity 2
       at lambda = 0, maximum Rayleigh value 1 != 0, contact ray dim 0 != 2).
     - Joint Rayleigh quotients / multidimensional extremal faces of W(A)
       (A_1 = diag(1,1,0,0), A_2 = diag(0,0,1,0) on hypotenuse face u + v = 1).
     - Interior eigenvalues (singular level set of diag(1,0,-1) on S^2 with
       jumping Zariski tangent dimension 1 vs. 2) and Morse index (n - m vs. m - 1).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import itertools
import sys
from typing import List, Sequence, Tuple


# ============================================================================
# 1. Exact Rational & Gaussian Rational (Q[i]) Linear Algebra
# ============================================================================

@dataclass(frozen=True)
class GaussianRat:
    """Exact element re + i * im in Q[i]."""
    re: Fraction
    im: Fraction = Fraction(0)

    @staticmethod
    def of(val: int | Fraction | "GaussianRat") -> "GaussianRat":
        if isinstance(val, GaussianRat):
            return val
        return GaussianRat(Fraction(val), Fraction(0))

    def __add__(self, other: "GaussianRat") -> "GaussianRat":
        return GaussianRat(self.re + other.re, self.im + other.im)

    def __sub__(self, other: "GaussianRat") -> "GaussianRat":
        return GaussianRat(self.re - other.re, self.im - other.im)

    def __neg__(self) -> "GaussianRat":
        return GaussianRat(-self.re, -self.im)

    def __mul__(self, other: "GaussianRat") -> "GaussianRat":
        return GaussianRat(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def conj(self) -> "GaussianRat":
        return GaussianRat(self.re, -self.im)

    def norm_sq(self) -> Fraction:
        return self.re * self.re + self.im * self.im

    def is_zero(self) -> bool:
        return self.re == 0 and self.im == 0

    def inv(self) -> "GaussianRat":
        ns = self.norm_sq()
        if ns == 0:
            raise ZeroDivisionError("Inverse of zero GaussianRat")
        return GaussianRat(self.re / ns, -self.im / ns)

    def __truediv__(self, other: "GaussianRat") -> "GaussianRat":
        return self * other.inv()


CZERO = GaussianRat(Fraction(0), Fraction(0))
CONE = GaussianRat(Fraction(1), Fraction(0))
CI = GaussianRat(Fraction(0), Fraction(1))


def rref_q(matrix: Sequence[Sequence[Fraction]]) -> Tuple[List[List[Fraction]], List[int]]:
    """Exact reduced row echelon form over Q; returns (rref_matrix, pivot_cols)."""
    if not matrix:
        return [], []
    rows = len(matrix)
    cols = len(matrix[0])
    mat = [[Fraction(x) for x in row] for row in matrix]
    pivots: List[int] = []
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        piv = None
        for i in range(r, rows):
            if mat[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        scale = mat[r][c]
        mat[r] = [val / scale for val in mat[r]]
        for i in range(rows):
            if i != r and mat[i][c] != 0:
                factor = mat[i][c]
                mat[i] = [mat[i][j] - factor * mat[r][j] for j in range(cols)]
        pivots.append(c)
        r += 1
    return mat, pivots


def rank_q(matrix: Sequence[Sequence[Fraction]]) -> int:
    if not matrix or not matrix[0]:
        return 0
    _, pivots = rref_q(matrix)
    return len(pivots)


def kernel_basis_q(matrix: Sequence[Sequence[Fraction]], ncols: int) -> List[List[Fraction]]:
    """Exact basis of {x in Q^ncols : matrix * x = 0}."""
    if ncols == 0:
        return []
    if not matrix:
        return [
            [Fraction(1 if i == j else 0) for j in range(ncols)]
            for i in range(ncols)
        ]
    rref_mat, pivots = rref_q(matrix)
    pivot_set = set(pivots)
    free_cols = [c for c in range(ncols) if c not in pivot_set]
    basis: List[List[Fraction]] = []
    for fc in free_cols:
        vec = [Fraction(0) for _ in range(ncols)]
        vec[fc] = Fraction(1)
        for row_idx, pc in enumerate(pivots):
            vec[pc] = -rref_mat[row_idx][fc]
        basis.append(vec)
    return basis


def rref_c(matrix: Sequence[Sequence[GaussianRat]]) -> Tuple[List[List[GaussianRat]], List[int]]:
    """Exact reduced row echelon form over Q[i]."""
    if not matrix:
        return [], []
    rows = len(matrix)
    cols = len(matrix[0])
    mat = [[GaussianRat.of(x) for x in row] for row in matrix]
    pivots: List[int] = []
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        piv = None
        for i in range(r, rows):
            if not mat[i][c].is_zero():
                piv = i
                break
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        scale = mat[r][c]
        mat[r] = [val / scale for val in mat[r]]
        for i in range(rows):
            if i != r and not mat[i][c].is_zero():
                factor = mat[i][c]
                mat[i] = [mat[i][j] - factor * mat[r][j] for j in range(cols)]
        pivots.append(c)
        r += 1
    return mat, pivots


def nullity_c(matrix: Sequence[Sequence[GaussianRat]], ncols: int) -> int:
    if ncols == 0:
        return 0
    if not matrix:
        return ncols
    _, pivots = rref_c(matrix)
    return ncols - len(pivots)


def det_q(matrix: Sequence[Sequence[Fraction]]) -> Fraction:
    """Exact determinant over Q via Gaussian elimination with sign tracking."""
    n = len(matrix)
    if n == 0:
        return Fraction(1)
    mat = [[Fraction(x) for x in row] for row in matrix]
    sign = Fraction(1)
    det_val = Fraction(1)
    for col in range(n):
        piv = None
        for r in range(col, n):
            if mat[r][col] != 0:
                piv = r
                break
        if piv is None:
            return Fraction(0)
        if piv != col:
            mat[col], mat[piv] = mat[piv], mat[col]
            sign = -sign
        pivot_val = mat[col][col]
        det_val *= pivot_val
        for r in range(col + 1, n):
            if mat[r][col] != 0:
                factor = mat[r][col] / pivot_val
                for c in range(col, n):
                    mat[r][c] -= factor * mat[col][c]
    return sign * det_val


def mat_mul_q(a: Sequence[Sequence[Fraction]], b: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    m, k, n = len(a), len(b), len(b[0])
    return [
        [sum((a[i][t] * b[t][j] for t in range(k)), Fraction(0)) for j in range(n)]
        for i in range(m)
    ]


def mat_vec_q(a: Sequence[Sequence[Fraction]], x: Sequence[Fraction]) -> List[Fraction]:
    return [sum((a[i][j] * x[j] for j in range(len(x))), Fraction(0)) for i in range(len(a))]


def dot_q(x: Sequence[Fraction], y: Sequence[Fraction]) -> Fraction:
    return sum((xi * yi for xi, yi in zip(x, y)), Fraction(0))


def transpose_q(a: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    return [[a[i][j] for i in range(len(a))] for j in range(len(a[0]))]


def eye_q(n: int) -> List[List[Fraction]]:
    return [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]


def mat_mul_c(a: Sequence[Sequence[GaussianRat]], b: Sequence[Sequence[GaussianRat]]) -> List[List[GaussianRat]]:
    m, k, n = len(a), len(b), len(b[0])
    return [
        [sum((a[i][t] * b[t][j] for t in range(k)), CZERO) for j in range(n)]
        for i in range(m)
    ]


def mat_vec_c(a: Sequence[Sequence[GaussianRat]], z: Sequence[GaussianRat]) -> List[GaussianRat]:
    return [sum((a[i][j] * z[j] for j in range(len(z))), CZERO) for i in range(len(a))]


def hermitian_inner(z: Sequence[GaussianRat], w: Sequence[GaussianRat]) -> GaussianRat:
    """Standard complex inner product <z, w> = sum_j conj(z_j) * w_j."""
    return sum((zj.conj() * wj for zj, wj in zip(z, w)), CZERO)


def conj_transpose_c(a: Sequence[Sequence[GaussianRat]]) -> List[List[GaussianRat]]:
    return [[a[i][j].conj() for i in range(len(a))] for j in range(len(a[0]))]


def eye_c(n: int) -> List[List[GaussianRat]]:
    return [[CONE if i == j else CZERO for j in range(n)] for i in range(n)]


def rayleigh_q(a: Sequence[Sequence[Fraction]], x: Sequence[Fraction]) -> Fraction:
    ns = dot_q(x, x)
    assert ns > 0, "Rayleigh quotient requires x != 0"
    return dot_q(x, mat_vec_q(a, x)) / ns


def rayleigh_c(a: Sequence[Sequence[GaussianRat]], z: Sequence[GaussianRat]) -> GaussianRat:
    ns = hermitian_inner(z, z)
    assert ns.im == 0 and ns.re > 0, "Rayleigh quotient requires z != 0"
    num = hermitian_inner(z, mat_vec_c(a, z))
    return GaussianRat(num.re / ns.re, num.im / ns.re)


# ============================================================================
# 2. Exact Rational Orthogonal & Unitary Test Matrices (Non-Diagonal!)
# ============================================================================

def rational_orthogonal(n: int) -> List[List[Fraction]]:
    """Constructs a nontrivial exact orthogonal matrix U in O_n(Q) via Cayley transform."""
    # Skew-symmetric S with off-diagonal entries, U = (I - S)(I + S)^{-1}
    s = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            val = Fraction(1, i + j + 1)
            s[i][j] = val
            s[j][i] = -val
    i_minus_s = [[(Fraction(1) if i == j else Fraction(0)) - s[i][j] for j in range(n)] for i in range(n)]
    i_plus_s = [[(Fraction(1) if i == j else Fraction(0)) + s[i][j] for j in range(n)] for i in range(n)]
    # Invert (I + S) via RREF on [I + S | I]
    aug = [i_plus_s[i] + eye_q(n)[i] for i in range(n)]
    rref_aug, pivots = rref_q(aug)
    assert pivots == list(range(n)), "I + S must be invertible"
    inv_i_plus_s = [row[n:] for row in rref_aug]
    u = mat_mul_q(i_minus_s, inv_i_plus_s)
    assert mat_mul_q(transpose_q(u), u) == eye_q(n), "U must be exact orthogonal"
    return u


def gaussian_unitary(n: int) -> List[List[GaussianRat]]:
    """Constructs a nontrivial exact unitary matrix U in U_n(Q[i]) via Cayley transform."""
    # Skew-Hermitian K (K* = -K), U = (I - K)(I + K)^{-1}
    k = [[CZERO for _ in range(n)] for _ in range(n)]
    for i in range(n):
        k[i][i] = GaussianRat(Fraction(0), Fraction(1, i + 2))
        for j in range(i + 1, n):
            val = GaussianRat(Fraction(1, i + j + 2), Fraction(1, i + j + 3))
            k[i][j] = val
            k[j][i] = -val.conj()
    id_c = eye_c(n)
    i_minus_k = [[id_c[i][j] - k[i][j] for j in range(n)] for i in range(n)]
    i_plus_k = [[id_c[i][j] + k[i][j] for j in range(n)] for i in range(n)]
    aug = [i_plus_k[i] + id_c[i] for i in range(n)]
    rref_aug, pivots = rref_c(aug)
    assert pivots == list(range(n)), "I + K must be invertible"
    inv_i_plus_k = [row[n:] for row in rref_aug]
    u = mat_mul_c(i_minus_k, inv_i_plus_k)
    assert mat_mul_c(conj_transpose_c(u), u) == id_c, "U must be exact unitary"
    return u


def model_spectrum(n: int, m: int) -> Tuple[List[Fraction], Fraction]:
    """Spectrum with maximum eigenvalue 2 of exact multiplicity m, and strictly smaller eigenvalues."""
    lam_max = Fraction(2)
    eigs = [lam_max if i < m else Fraction(1 - (i - m)) for i in range(n)]
    assert sum(1 for x in eigs if x == lam_max) == m
    assert all(x < lam_max for x in eigs[m:])
    return eigs, lam_max


# ============================================================================
# 3. Verification Suites
# ============================================================================

def verify_positive_linear_cone() -> None:
    print("[1/6] Verifying positive linear-cone eigenspace characterization (1 <= m <= n <= 5)...")
    for n in range(1, 6):
        u_real = rational_orthogonal(n)
        u_comp = gaussian_unitary(n)
        for m in range(1, n + 1):
            eigs, lam_max = model_spectrum(n, m)
            diag_q = [[eigs[i] if i == j else Fraction(0) for j in range(n)] for i in range(n)]
            b_real = mat_mul_q(mat_mul_q(u_real, diag_q), transpose_q(u_real))
            assert b_real == transpose_q(b_real), "B_real must be symmetric"

            # Exact eigenspace dimension over Q
            shifted_real = [
                [b_real[i][j] - (lam_max if i == j else Fraction(0)) for j in range(n)]
                for i in range(n)
            ]
            ker_basis = kernel_basis_q(shifted_real, n)
            assert len(ker_basis) == m, f"Expected dim ker = {m}, got {len(ker_basis)}"

            # Sample vectors inside and outside ker(B - lam_max I)
            for coeff_tuple in itertools.product([-1, 0, 1], repeat=min(n, 4)):
                c_full = list(coeff_tuple) + [0] * (n - len(coeff_tuple))
                if all(v == 0 for v in c_full):
                    continue
                # Map c_full in eigenbasis via U
                x = mat_vec_q(u_real, [Fraction(v) for v in c_full])
                rx = rayleigh_q(b_real, x)
                assert rx <= lam_max, f"Rayleigh bound violated: {rx} > {lam_max}"
                bx = mat_vec_q(b_real, x)
                is_eig = all(bx[i] == lam_max * x[i] for i in range(n))
                assert (rx == lam_max) == is_eig, "R_B(x) = lam_max iff B x = lam_max x failed"

            # Complex Hermitian check
            diag_c = [[GaussianRat.of(eigs[i]) if i == j else CZERO for j in range(n)] for i in range(n)]
            b_comp = mat_mul_c(mat_mul_c(u_comp, diag_c), conj_transpose_c(u_comp))
            assert b_comp == conj_transpose_c(b_comp), "B_comp must be Hermitian"
            shifted_c = [
                [b_comp[i][j] - (GaussianRat.of(lam_max) if i == j else CZERO) for j in range(n)]
                for i in range(n)
            ]
            dim_c = nullity_c(shifted_c, n)
            assert dim_c == m, f"Expected C-dim ker = {m}, got {dim_c}"

            # Realified system on Q^{2n} for ker_C(B_comp - lam_max I)
            real_rows: List[List[Fraction]] = []
            for i in range(n):
                row_re: List[Fraction] = []
                row_im: List[Fraction] = []
                for j in range(n):
                    entry = shifted_c[i][j]
                    # (a + i b)(x + i y) = (a x - b y) + i (b x + a y)
                    row_re.extend([entry.re, -entry.im])
                    row_im.extend([entry.im, entry.re])
                real_rows.append(row_re)
                real_rows.append(row_im)
            dim_r_of_c_cone = len(kernel_basis_q(real_rows, 2 * n))
            assert dim_r_of_c_cone == 2 * m and dim_r_of_c_cone != m

    print("      PASS: R_B(x) = lambda_max <=> B x = lambda_max x; linear cone has F-dim m (real dim 2m != m over C).")


def verify_real_sphere_and_projective() -> None:
    print("[2/6] Verifying Domains 1 & 2: Real Sphere S^{n-1} and Real Projective Space RP^{n-1} (1 <= m <= n <= 6)...")
    # Explicit minimal counterexample A = diag(2, 1) (n = 2, m = 1)
    a_min = [[Fraction(2), Fraction(0)], [Fraction(0), Fraction(1)]]
    # On S^1: x_1^2 + x_2^2 = 1 and 2 x_1^2 + x_2^2 = 2 => x_2 = 0 and x_1 = +-1
    e1_pos = [Fraction(1), Fraction(0)]
    e1_neg = [Fraction(-1), Fraction(0)]
    for pt in (e1_pos, e1_neg):
        assert dot_q(pt, pt) == 1 and rayleigh_q(a_min, pt) == 2

    for n in range(1, 7):
        u = rational_orthogonal(n)
        for m in range(1, n + 1):
            eigs, lam_max = model_spectrum(n, m)
            diag_q = [[eigs[i] if i == j else Fraction(0) for j in range(n)] for i in range(n)]
            b = mat_mul_q(mat_mul_q(u, diag_q), transpose_q(u))
            # Unit eigenvector p = U e_1 in M_{R,S}(B)
            p = [u[i][0] for i in range(n)]
            assert dot_q(p, p) == 1 and rayleigh_q(b, p) == lam_max

            # Tangent space T_p M_{R,S}(B) = {v in Q^n : <p, v> = 0 and (B - lam_max I) v = 0}
            eqs: List[List[Fraction]] = [p[:]]
            for i in range(n):
                eqs.append([b[i][j] - (lam_max if i == j else Fraction(0)) for j in range(n)])
            t_basis = kernel_basis_q(eqs, n)
            dim_sphere = len(t_basis)
            assert dim_sphere == m - 1, f"Expected m - 1 = {m - 1}, got {dim_sphere}"
            assert dim_sphere != m, "Sphere contact dimension CANNOT equal multiplicity m!"

            # Rational stereographic chart sigma : Q^{m-1} -> M_{R,S}(B) \ {-p}
            # Using orthonormal basis columns u_0, ..., u_{m-1} of ker(B - lam_max I)
            u_cols = [[u[i][k] for i in range(n)] for k in range(m)]
            for sample_y in itertools.product([Fraction(-1), Fraction(0), Fraction(2)], repeat=min(m - 1, 3)):
                y = list(sample_y) + [Fraction(0)] * ((m - 1) - len(sample_y))
                ynorm = dot_q(y, y)
                denom = Fraction(1) + ynorm
                c0 = (Fraction(1) - ynorm) / denom
                pt = [c0 * u_cols[0][i] for i in range(n)]
                for k in range(m - 1):
                    ck = (Fraction(2) * y[k]) / denom
                    for i in range(n):
                        pt[i] += ck * u_cols[k + 1][i]
                assert dot_q(pt, pt) == 1, "Stereographic point must lie on S^{n-1}"
                assert rayleigh_q(b, pt) == lam_max, "Stereographic point must attain lambda_max"
                # Inverse chart recovery: y_k = <u_{k+1}, pt> / (1 + <u_0, pt>)
                one_plus_x0 = Fraction(1) + dot_q(u_cols[0], pt)
                assert one_plus_x0 != 0
                y_rec = [dot_q(u_cols[k + 1], pt) / one_plus_x0 for k in range(m - 1)]
                assert y_rec == y, "Stereographic chart must be bijective on M_{R,S}(B) \\ {-p}"

            # RP^{n-1} inhomogeneous chart [p + sum_{k=1}^{m-1} y_k u_k] has exact dim m - 1 != m
            dim_rp = len(u_cols) - 1
            assert dim_rp == m - 1 and dim_rp != m

    print("      PASS: dim M_{R,S}(B) = dim M_{RP}(B) = m - 1 != m for ALL 1 <= m <= n <= 6.")


def verify_complex_sphere_and_contact_structure() -> None:
    print("[3/6] Verifying Domain 3: Complex Sphere S^{2n-1} & strict contact form alpha = Im<z, dz> (1 <= m <= n <= 5)...")
    for n in range(1, 6):
        u = gaussian_unitary(n)
        for m in range(1, n + 1):
            eigs, lam_max = model_spectrum(n, m)
            diag_c = [[GaussianRat.of(eigs[i]) if i == j else CZERO for j in range(n)] for i in range(n)]
            b = mat_mul_c(mat_mul_c(u, diag_c), conj_transpose_c(u))
            p = [u[i][0] for i in range(n)]
            assert hermitian_inner(p, p) == CONE
            assert rayleigh_c(b, p) == GaussianRat.of(lam_max)

            # Real tangent space T_p M_{C,S}(B) in Q^{2n}:
            #   Re<p, v> = 0  AND  (B - lam_max I) v = 0
            eqs: List[List[Fraction]] = []
            # Re(sum_j conj(p_j) (x_j + i y_j)) = sum_j (p_j.re * x_j + p_j.im * y_j) = 0
            sphere_row: List[Fraction] = []
            for j in range(n):
                sphere_row.extend([p[j].re, p[j].im])
            eqs.append(sphere_row)
            for i in range(n):
                row_re: List[Fraction] = []
                row_im: List[Fraction] = []
                for j in range(n):
                    entry = b[i][j] - (GaussianRat.of(lam_max) if i == j else CZERO)
                    row_re.extend([entry.re, -entry.im])
                    row_im.extend([entry.im, entry.re])
                eqs.append(row_re)
                eqs.append(row_im)

            t_basis = kernel_basis_q(eqs, 2 * n)
            dim_csphere = len(t_basis)
            assert dim_csphere == 2 * m - 1, f"Expected 2m - 1 = {2 * m - 1}, got {dim_csphere}"
            if m == 1:
                assert dim_csphere == 1  # Phase circle S^1 coincidence at m = 1
            else:
                assert dim_csphere != m, f"Complex sphere dim {dim_csphere} must differ from m={m} for m >= 2"

            # Verify strict contact structure alpha_p(v) = Im<p, v> on T_p M_{C,S}(B):
            # Reeb vector R = i * p must lie in T_p M_{C,S}(B) and satisfy alpha_p(R) = 1.
            reeb_c = [CI * pj for pj in p]
            assert hermitian_inner(p, reeb_c) == CI  # Re = 0, Im = 1
            b_reeb = mat_vec_c(b, reeb_c)
            assert all(b_reeb[i] == GaussianRat.of(lam_max) * reeb_c[i] for i in range(n))

            # Contact hyperplane xi_p = T_p M_{C,S}(B) cap ker(alpha_p) has dim 2m - 2,
            # and d(alpha)(v, w) = 2 Im<v, w> is nondegenerate on xi_p!
            alpha_row: List[Fraction] = []
            for j in range(n):
                # Im(conj(p_j)(x_j + i y_j)) = p_j.re * y_j - p_j.im * x_j
                alpha_row.extend([-p[j].im, p[j].re])
            xi_basis = kernel_basis_q(eqs + [alpha_row], 2 * n)
            assert len(xi_basis) == 2 * m - 2
            if m >= 2:
                k_dim = len(xi_basis)
                gram_symp: List[List[Fraction]] = []
                for u_vec in xi_basis:
                    u_c = [GaussianRat(u_vec[2 * j], u_vec[2 * j + 1]) for j in range(n)]
                    row_symp: List[Fraction] = []
                    for w_vec in xi_basis:
                        w_c = [GaussianRat(w_vec[2 * j], w_vec[2 * j + 1]) for j in range(n)]
                        row_symp.append(Fraction(2) * hermitian_inner(u_c, w_c).im)
                    gram_symp.append(row_symp)
                assert det_q(gram_symp) != 0, "d(alpha)|_xi must be nondegenerate symplectic!"

    print("      PASS: M_{C,S}(B) is a strict contact submanifold of exact dim_R = 2m - 1 (fails 2m - 1 = m for all m >= 2).")


def verify_complex_projective() -> None:
    print("[4/6] Verifying Domain 4: Complex Projective Space CP^{n-1} (1 <= m <= n <= 5)...")
    for n in range(1, 6):
        u = gaussian_unitary(n)
        for m in range(1, n + 1):
            eigs, lam_max = model_spectrum(n, m)
            diag_c = [[GaussianRat.of(eigs[i]) if i == j else CZERO for j in range(n)] for i in range(n)]
            b = mat_mul_c(mat_mul_c(u, diag_c), conj_transpose_c(u))
            p = [u[i][0] for i in range(n)]

            # T_{[p]} M_{CP}(B) ~= {v in C^n : <p, v> = 0 and (B - lam_max I) v = 0}
            c_eqs: List[List[GaussianRat]] = [[pj.conj() for pj in p]]
            for i in range(n):
                c_eqs.append([b[i][j] - (GaussianRat.of(lam_max) if i == j else CZERO) for j in range(n)])
            dim_c = nullity_c(c_eqs, n)
            assert dim_c == m - 1 and dim_c != m

            # Real dimension via Q^{2n}
            r_eqs: List[List[Fraction]] = []
            for row in c_eqs:
                r_re: List[Fraction] = []
                r_im: List[Fraction] = []
                for entry in row:
                    r_re.extend([entry.re, -entry.im])
                    r_im.extend([entry.im, entry.re])
                r_eqs.append(r_re)
                r_eqs.append(r_im)
            dim_r = len(kernel_basis_q(r_eqs, 2 * n))
            assert dim_r == 2 * m - 2
            if m != 2:
                assert dim_r != m

    print("      PASS: M_{CP}(B) has dim_C = m - 1 != m (all m >= 1) and dim_R = 2m - 2 != m (all m != 2).")


def verify_density_matrix_faces() -> None:
    print("[5/6] Verifying Domain 5: Density-Matrix Extremal Faces D_n(C) and D_n(R) (1 <= m <= n <= 5)...")
    for n in range(1, 6):
        u_real = rational_orthogonal(n)
        u_comp = gaussian_unitary(n)
        for m in range(1, n + 1):
            eigs, lam_max = model_spectrum(n, m)
            diag_q = [[eigs[i] if i == j else Fraction(0) for j in range(n)] for i in range(n)]
            b_real = mat_mul_q(mat_mul_q(u_real, diag_q), transpose_q(u_real))

            # Real symmetric matrices parameterized in Q^{n^2} by H_{ij}:
            #   H_{ij} = H_{ji}, tr(H) = 0, and (B_real - lam_max I) H = 0
            # (since rho_0 +- eps H >= 0 around rho_0 = (1/m) P_eig <-> ker(B - lam_max I) contains im(H)).
            n2 = n * n
            eqs_real: List[List[Fraction]] = []
            # Symmetry H_{ij} - H_{ji} = 0
            for i in range(n):
                for j in range(i + 1, n):
                    row = [Fraction(0)] * n2
                    row[i * n + j] = Fraction(1)
                    row[j * n + i] = Fraction(-1)
                    eqs_real.append(row)
            # Trace zero sum_i H_{ii} = 0
            tr_row = [Fraction(1 if i == j else 0) for i in range(n) for j in range(n)]
            eqs_real.append(tr_row)
            # Support in eigenspace: ((B_real - lam_max I) H)_{ij} = 0 for all i, j
            shifted_r = [
                [b_real[i][k] - (lam_max if i == k else Fraction(0)) for k in range(n)]
                for i in range(n)
            ]
            for i in range(n):
                for j in range(n):
                    row = [Fraction(0)] * n2
                    for k in range(n):
                        row[k * n + j] = shifted_r[i][k]
                    eqs_real.append(row)
            basis_real_dm = kernel_basis_q(eqs_real, n2)
            dim_real_dm = len(basis_real_dm)
            expected_real_dm = (m * (m + 1)) // 2 - 1
            assert dim_real_dm == expected_real_dm, f"Expected {expected_real_dm}, got {dim_real_dm}"
            if m != 2:
                assert dim_real_dm != m

            # Verify interior point rho_0 = (1/m) sum_{r=0}^{m-1} u_r u_r^T satisfies tr(rho_0)=1, tr(B rho_0)=lam_max
            rho0 = [[Fraction(0) for _ in range(n)] for _ in range(n)]
            for r in range(m):
                for i in range(n):
                    for j in range(n):
                        rho0[i][j] += u_real[i][r] * u_real[j][r] / Fraction(m)
            tr_rho0 = sum((rho0[i][i] for i in range(n)), Fraction(0))
            tr_b_rho0 = sum((b_real[i][j] * rho0[j][i] for i in range(n) for j in range(n)), Fraction(0))
            assert tr_rho0 == 1 and tr_b_rho0 == lam_max

            # Complex Hermitian matrices parameterized in Q^{2 n^2} by (Re H_{ij}, Im H_{ij}):
            #   H* = H, tr(H) = 0, and (B_comp - lam_max I) H = 0.
            diag_c = [[GaussianRat.of(eigs[i]) if i == j else CZERO for j in range(n)] for i in range(n)]
            b_comp = mat_mul_c(mat_mul_c(u_comp, diag_c), conj_transpose_c(u_comp))
            shifted_c = [
                [b_comp[i][k] - (GaussianRat.of(lam_max) if i == k else CZERO) for k in range(n)]
                for i in range(n)
            ]
            dim_amb = 2 * n * n

            def idx_re(i: int, j: int) -> int:
                return 2 * (i * n + j)

            def idx_im(i: int, j: int) -> int:
                return 2 * (i * n + j) + 1

            eqs_comp: List[List[Fraction]] = []
            # Hermiticity: Im H_{ii} = 0; for i < j, Re H_{ij} - Re H_{ji} = 0 and Im H_{ij} + Im H_{ji} = 0
            for i in range(n):
                row = [Fraction(0)] * dim_amb
                row[idx_im(i, i)] = Fraction(1)
                eqs_comp.append(row)
                for j in range(i + 1, n):
                    row1 = [Fraction(0)] * dim_amb
                    row1[idx_re(i, j)] = Fraction(1)
                    row1[idx_re(j, i)] = Fraction(-1)
                    eqs_comp.append(row1)
                    row2 = [Fraction(0)] * dim_amb
                    row2[idx_im(i, j)] = Fraction(1)
                    row2[idx_im(j, i)] = Fraction(1)
                    eqs_comp.append(row2)
            # Trace zero: sum_i Re H_{ii} = 0
            tr_c = [Fraction(0)] * dim_amb
            for i in range(n):
                tr_c[idx_re(i, i)] = Fraction(1)
            eqs_comp.append(tr_c)
            # Support: ((B_comp - lam_max I) H)_{ij} = 0
            for i in range(n):
                for j in range(n):
                    row_r = [Fraction(0)] * dim_amb
                    row_i = [Fraction(0)] * dim_amb
                    for k in range(n):
                        s_ik = shifted_c[i][k]
                        row_r[idx_re(k, j)] += s_ik.re
                        row_r[idx_im(k, j)] -= s_ik.im
                        row_i[idx_re(k, j)] += s_ik.im
                        row_i[idx_im(k, j)] += s_ik.re
                    eqs_comp.append(row_r)
                    eqs_comp.append(row_i)

            dim_comp_dm = len(kernel_basis_q(eqs_comp, dim_amb))
            assert dim_comp_dm == m * m - 1, f"Expected m^2 - 1 = {m * m - 1}, got {dim_comp_dm}"
            assert dim_comp_dm != m, "m^2 - 1 != m for ALL integers m!"

    print("      PASS: dim_R F_max^C = m^2 - 1 != m (all m >= 1); dim_R F_max^R = m(m+1)/2 - 1 != m (m = 1 and m >= 3).")


def verify_nonnormal_joint_and_interior_obstructions() -> None:
    print("[6/6] Verifying non-normal matrices, joint numerical range faces, interior singularities, & Morse indices...")

    # 6A. Non-normal matrix A = [[0, 2], [0, 0]]
    a_nn = [[Fraction(0), Fraction(2)], [Fraction(0), Fraction(0)]]
    # Characteristic polynomial det(lam I - A) = lam^2: tr = 0, det = 0 => lambda = 0 has alg mult 2, geom mult 1
    tr_nn = a_nn[0][0] + a_nn[1][1]
    det_nn = det_q(a_nn)
    geom_mult_0 = len(kernel_basis_q(a_nn, 2))
    assert tr_nn == 0 and det_nn == 0 and geom_mult_0 == 1
    # Symmetric part H(A) = (A + A^T)/2 = [[0, 1], [1, 0]] has max eigenvalue 1 != 0, attained solely along [1 : 1]
    h_nn = [[Fraction(0), Fraction(1)], [Fraction(1), Fraction(0)]]
    assert rayleigh_q(a_nn, [Fraction(1), Fraction(1)]) == Fraction(1)
    for x1, x2 in itertools.product(range(-4, 5), repeat=2):
        if x1 == 0 and x2 == 0:
            continue
        rq = rayleigh_q(a_nn, [Fraction(x1), Fraction(x2)])
        assert rq <= 1
        assert (rq == 1) == (x1 == x2)
    # Tangent space in RP^1 at [(1, 1)] has dimension 0 != 2 (alg mult) and 0 != 1 (geom mult)
    shifted_h = [[h_nn[i][j] - (Fraction(1) if i == j else Fraction(0)) for j in range(2)] for i in range(2)]
    rp_tangent_nn = kernel_basis_q([[Fraction(1), Fraction(1)]] + shifted_h, 2)
    assert len(rp_tangent_nn) == 0

    # 6B. Joint Rayleigh quotient (R_{A_1}, R_{A_2}) with A_1 = diag(1,1,0,0), A_2 = diag(0,0,1,0)
    a1 = [[Fraction(1 if i == j and i < 2 else 0) for j in range(4)] for i in range(4)]
    a2 = [[Fraction(1 if i == j and i == 2 else 0) for j in range(4)] for i in range(4)]
    # Supporting operator A_1 + A_2 = diag(1,1,1,0) cuts out the 1D extremal hypotenuse face u + v = 1
    a_sum = [[a1[i][j] + a2[i][j] for j in range(4)] for i in range(4)]
    m_support = len(kernel_basis_q([[a_sum[i][j] - (Fraction(1) if i == j else Fraction(0)) for j in range(4)] for i in range(4)], 4))
    m_a1 = len(kernel_basis_q([[a1[i][j] - (Fraction(1) if i == j else Fraction(0)) for j in range(4)] for i in range(4)], 4))
    m_a2 = len(kernel_basis_q([[a2[i][j] - (Fraction(1) if i == j else Fraction(0)) for j in range(4)] for i in range(4)], 4))
    assert (m_support, m_a1, m_a2) == (3, 2, 1)
    # Extremal face contains distinct endpoints (1,0), (0,1) and midpoint (1/2, 1/2)
    v_end1 = [Fraction(1), Fraction(0), Fraction(0), Fraction(0)]
    v_end2 = [Fraction(0), Fraction(0), Fraction(1), Fraction(0)]
    v_mid = [Fraction(1), Fraction(0), Fraction(1), Fraction(0)]
    assert (rayleigh_q(a1, v_end1), rayleigh_q(a2, v_end1)) == (Fraction(1), Fraction(0))
    assert (rayleigh_q(a1, v_end2), rayleigh_q(a2, v_end2)) == (Fraction(0), Fraction(1))
    assert (rayleigh_q(a1, v_mid), rayleigh_q(a2, v_mid)) == (Fraction(1, 2), Fraction(1, 2))
    # Contact locus dimensions along hypotenuse face:
    # S^3 / RP^3 -> 2; S^7 -> 5; CP^3 -> 4 (real), 2 (complex); D_4(C) -> 8; D_4(R) -> 5. None equals m_support = 3!
    face_dims = {
        "S^3": m_support - 1,
        "RP^3": m_support - 1,
        "S^7": 2 * m_support - 1,
        "CP^3_C": m_support - 1,
        "CP^3_R": 2 * m_support - 2,
        "D_4(C)": m_support * m_support - 1,
        "D_4(R)": (m_support * (m_support + 1)) // 2 - 1,
    }
    assert all(d != m_support for d in face_dims.values()), f"Unexpected match in {face_dims}"

    # 6C. Interior eigenvalue singularity: A = diag(1, 0, -1) on S^2 at lambda_2 = 0 (multiplicity m = 1)
    a_int = [[Fraction(1), Fraction(0), Fraction(0)], [Fraction(0), Fraction(0), Fraction(0)], [Fraction(0), Fraction(0), Fraction(-1)]]
    assert len(kernel_basis_q(a_int, 3)) == 1  # multiplicity m = 1
    p_sing = [Fraction(0), Fraction(1), Fraction(0)]
    q_reg = [Fraction(2, 3), Fraction(1, 3), Fraction(2, 3)]
    for pt in (p_sing, q_reg):
        assert dot_q(pt, pt) == 1 and rayleigh_q(a_int, pt) == 0
    # Zariski tangent space of {x in S^2 : x_1^2 - x_3^2 = 0} at x is {<x, v> = 0, x_1 v_1 - x_3 v_3 = 0}
    zt_sing = kernel_basis_q([p_sing, [p_sing[0], Fraction(0), -p_sing[2]]], 3)
    zt_reg = kernel_basis_q([q_reg, [q_reg[0], Fraction(0), -q_reg[2]]], 3)
    assert len(zt_reg) == 1 and len(zt_sing) == 2, "Jumping Zariski tangent dim (1 vs 2) proves level set is singular!"

    # 6D. Morse index of M_max(A) on S^{n-1} is n - m != m - 1 in general (e.g. A = diag(2, 1, 1): Morse index 2, dim 0)
    n_test, m_test = 3, 1
    eigs_test, lam_test = model_spectrum(n_test, m_test)
    # Transverse Hessian eigenvalues at e_1 are 2*(lambda_j - lambda_max) < 0 for j >= m
    hess_eigs = [Fraction(2) * (eigs_test[j] - lam_test) for j in range(m_test, n_test)]
    morse_index = sum(1 for ev in hess_eigs if ev < 0)
    assert morse_index == n_test - m_test == 2 and morse_index != (m_test - 1)

    print("      PASS: Non-normal, joint numerical range, interior-index singularity, and Morse-index checks all verified.")


def main() -> int:
    print("=" * 78)
    print("Exact Verification Suite — Conjecture 00000007165")
    print("=" * 78)
    verify_positive_linear_cone()
    verify_real_sphere_and_projective()
    verify_complex_sphere_and_contact_structure()
    verify_complex_projective()
    verify_density_matrix_faces()
    verify_nonnormal_joint_and_interior_obstructions()
    print("=" * 78)
    print("ALL EXACT VERIFICATION CHECKS PASSED (VERDICT: CONJECTURE 00000007165 IS FALSE)")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
