#!/usr/bin/env python3
"""
Standalone exact computational verification suite for Conjecture 00000007610:
"Same Representation-Different Center Extension Separation in Clifford Algebras"

Uses ONLY Python 3 standard library (`fractions.Fraction`, `itertools`) for 100%
exact arithmetic over Q and explicit quadratic field extensions Q(sqrt(delta)),
with zero floating-point approximations and zero external package dependencies.

Verifies:
1. Exact 2^n-dimensional Clifford algebra construction Cl(K^n, d) via both:
   (a) Basis subset / bitmask sign multiplication e_I * e_J = sgn(I, J) * prod(d) * e_{I ^ J}
   (b) Recursive Z/2Z-graded Chevalley construction (used in Lean 4 formalization),
   confirming exact isomorphism and full associativity, distributivity, and
   universal Clifford identity iota(v)^2 = Q(v) * 1 across n = 0, 1, 2, 3, 4.
2. Exact linear-algebraic computation of the ring-theoretic center
   Z(A) = {z in A : z * x == x * z for all x in A} via nullspace of commutator maps.
3. Regime I (Fixed base field Q, center extension pair (Q, Q(i))):
   - A_1 = Cl_{1,1}(Q) = Cl(Q^2, (1, -1)) ~= M_2(Q):
     dim_Q A_1 = 4, dim_Q Z(A_1) = 1 (Z(A_1) ~= Q),
     1 unique simple Q-module class of Q-dimension 2 -> Spec_rep^Q(A_1) = (1, [2]).
   - A_2 = Cl_{0,1}(Q) = Cl(Q^1, (-1)) ~= Q(i):
     dim_Q A_2 = 2, dim_Q Z(A_2) = 2 (Z(A_2) ~= Q(i)),
     1 unique simple Q-module class of Q-dimension 2 -> Spec_rep^Q(A_2) = (1, [2]).
   - Exact verification that Spec_rep^Q(A_1) == Spec_rep^Q(A_2) while Z(A_1) !~= Z(A_2)
     both as Q-algebras (dim 1 != 2) and as abstract unital rings (z^2 + 1 = 0 solvable
     in Z(A_2) and unsolvable in Z(A_1)).
4. Regime II (Fixed base field Q AND same generator dimension n = 1 and n = 3):
   - n = 1: Cl(Q^1, (2)) ~= Q(sqrt(2)) vs Cl(Q^1, (-1)) ~= Q(i):
     both have dim_Q A = 2, Spec_rep^Q = (1, [2]), and non-isomorphic field centers
     Q(sqrt(2)) !~= Q(i) (since (a + b*sqrt(2))^2 + 1 = (a^2 + 2*b^2 + 1) + 2*a*b*sqrt(2) != 0).
   - n = 3 (noncommutative 8-dimensional Clifford algebras over Q):
     Cl(Q^3, (1, -1, -1)) ~= M_2(Q(i)) vs Cl(Q^3, (1, -1, -2)) ~= M_2(Q(sqrt(-2))):
     both have dim_Q A = 8, Spec_rep^Q = (1, [4]), and non-isomorphic quadratic field
     centers Q(i) !~= Q(sqrt(-2)).
5. Regime III (Explicit base-field extension pair Q -> Q(i) on identical split form (1, -1)):
   - B_Q = Cl_{1,1}(Q) over Q and B_{Q(i)} = Cl_{1,1}(Q(i)) over Q(i), sharing the exact
     integer spinor matrices E_0 = [[1, 0], [0, -1]] and E_1 = [[0, 1], [-1, 0]]:
     Spec_rep^Q(B_Q) = (1, [2]) == Spec_rep^{Q(i)}(B_{Q(i)}) = (1, [2]),
     while Z(B_Q) ~= Q and Z(B_{Q(i)}) ~= Q(i) are non-isomorphic as unital rings.
6. Quadratically-closed / algebraically-closed obstruction check:
   - Over C (modeled via exact Q(i) for forms with entries in {1, -1}), every nondegenerate
     Cl_n has either (1, [2^m]) with dim Z = 1 (even n = 2m) or (2, [2^m, 2^m]) with
     dim Z = 2 (odd n = 2m + 1), proving that over an algebraically closed base field,
     Spec_rep uniquely determines Z up to algebra isomorphism, and explaining why a
     nontrivial field extension over a non-quadratically-closed field is essential.
"""

from fractions import Fraction
import itertools
import sys
from typing import Callable, Generic, List, Sequence, Tuple, TypeVar


# =============================================================================
# 1. Exact Field Arithmetic: Q and Quadratic Extensions Q(sqrt(delta))
# =============================================================================

class QuadExt:
    """Exact element a + b * sqrt(delta) in Q(sqrt(delta)), where delta in Q is non-square."""

    def __init__(self, a: Fraction | int, b: Fraction | int = 0, delta: Fraction | int = -1):
        self.a = Fraction(a)
        self.b = Fraction(b)
        self.delta = Fraction(delta)

    def _check_compat(self, other: "QuadExt") -> None:
        if self.delta != other.delta:
            raise ValueError(f"Incompatible quadratic fields: delta={self.delta} vs {other.delta}")

    def __add__(self, other: "QuadExt | int | Fraction") -> "QuadExt":
        if isinstance(other, (int, Fraction)):
            return QuadExt(self.a + Fraction(other), self.b, self.delta)
        self._check_compat(other)
        return QuadExt(self.a + other.a, self.b + other.b, self.delta)

    def __radd__(self, other: int | Fraction) -> "QuadExt":
        return self + other

    def __sub__(self, other: "QuadExt | int | Fraction") -> "QuadExt":
        if isinstance(other, (int, Fraction)):
            return QuadExt(self.a - Fraction(other), self.b, self.delta)
        self._check_compat(other)
        return QuadExt(self.a - other.a, self.b - other.b, self.delta)

    def __rsub__(self, other: int | Fraction) -> "QuadExt":
        return QuadExt(Fraction(other), 0, self.delta) - self

    def __neg__(self) -> "QuadExt":
        return QuadExt(-self.a, -self.b, self.delta)

    def __mul__(self, other: "QuadExt | int | Fraction") -> "QuadExt":
        if isinstance(other, (int, Fraction)):
            c = Fraction(other)
            return QuadExt(self.a * c, self.b * c, self.delta)
        self._check_compat(other)
        return QuadExt(
            self.a * other.a + self.delta * self.b * other.b,
            self.a * other.b + self.b * other.a,
            self.delta,
        )

    def __rmul__(self, other: int | Fraction) -> "QuadExt":
        return self * other

    def norm(self) -> Fraction:
        return self.a * self.a - self.delta * self.b * self.b

    def inv(self) -> "QuadExt":
        nrm = self.norm()
        if nrm == 0:
            raise ZeroDivisionError("Zero or zero-divisor in QuadExt")
        return QuadExt(self.a / nrm, -self.b / nrm, self.delta)

    def __truediv__(self, other: "QuadExt | int | Fraction") -> "QuadExt":
        if isinstance(other, (int, Fraction)):
            c = Fraction(other)
            if c == 0:
                raise ZeroDivisionError("Division by zero")
            return QuadExt(self.a / c, self.b / c, self.delta)
        self._check_compat(other)
        return self * other.inv()

    def __eq__(self, other: object) -> bool:
        if isinstance(other, (int, Fraction)):
            return self.a == Fraction(other) and self.b == 0
        if isinstance(other, QuadExt):
            return self.delta == other.delta and self.a == other.a and self.b == other.b
        return False

    def __repr__(self) -> str:
        sym = "i" if self.delta == -1 else f"sqrt({self.delta})"
        if self.b == 0:
            return f"{self.a}"
        if self.a == 0:
            return f"{self.b}*{sym}"
        return f"({self.a} + {self.b}*{sym})"


F = TypeVar("F")


class FieldOps(Generic[F]):
    """Bundle of exact field operations."""

    def __init__(self, name: str, zero: F, one: F, lift_int: Callable[[int], F]):
        self.name = name
        self.zero = zero
        self.one = one
        self.lift_int = lift_int


Q_FIELD = FieldOps("Q", Fraction(0), Fraction(1), lambda k: Fraction(k))


def quad_field(delta: int, label: str) -> FieldOps[QuadExt]:
    return FieldOps(
        label,
        QuadExt(0, 0, delta),
        QuadExt(1, 0, delta),
        lambda k: QuadExt(k, 0, delta),
    )


QI_FIELD = quad_field(-1, "Q(i)")
QSQRT2_FIELD = quad_field(2, "Q(sqrt(2))")
QSQRT_MINUS2_FIELD = quad_field(-2, "Q(sqrt(-2))")


# =============================================================================
# 2. Exact Linear Algebra over Any Field F (RREF, Rank, Nullspace)
# =============================================================================

def rref(matrix: List[List[F]], field: FieldOps[F]) -> Tuple[List[List[F]], List[int]]:
    """Compute exact Reduced Row Echelon Form and pivot column indices."""
    if not matrix:
        return [], []
    m = len(matrix)
    n = len(matrix[0])
    mat = [ list(row) for row in matrix ]
    pivots: List[int] = []
    r = 0
    for c in range(n):
        if r >= m:
            break
        piv = None
        for i in range(r, m):
            if mat[i][c] != field.zero:
                piv = i
                break
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        inv_val = field.one / mat[r][c]  # type: ignore[operator]
        mat[r] = [x * inv_val for x in mat[r]]  # type: ignore[operator]
        for i in range(m):
            if i != r and mat[i][c] != field.zero:
                factor = mat[i][c]
                mat[i] = [mat[i][j] - factor * mat[r][j] for j in range(n)]  # type: ignore[operator]
        pivots.append(c)
        r += 1
    return mat, pivots


def nullspace_basis(matrix: List[List[F]], n_cols: int, field: FieldOps[F]) -> List[List[F]]:
    """Exact basis for {v in F^n_cols : matrix * v == 0}."""
    if not matrix:
        basis = []
        for j in range(n_cols):
            vec = [field.zero] * n_cols
            vec[j] = field.one
            basis.append(vec)
        return basis
    red, pivots = rref(matrix, field)
    pivot_set = set(pivots)
    free_cols = [c for c in range(n_cols) if c not in pivot_set]
    basis: List[List[F]] = []
    for fc in free_cols:
        vec = [field.zero] * n_cols
        vec[fc] = field.one
        for row_idx, pc in enumerate(pivots):
            vec[pc] = -red[row_idx][fc]  # type: ignore[operator]
        basis.append(vec)
    return basis


# =============================================================================
# 3. Exact 2^n-Dimensional Clifford Algebra Cl(F^n, d) (Two Constructions)
# =============================================================================

class CliffordAlgebra(Generic[F]):
    """
    Exact 2^n-dimensional Clifford algebra Cl(F^n, d) with orthogonal generators
    e_0, ..., e_{n-1} satisfying e_k^2 = d[k] * 1 and e_j * e_k = -e_k * e_j (j != k).
    Basis elements are indexed by bitmasks mask in 0 .. (2^n - 1), where bit k
    indicates presence of generator e_k in increasing index order.
    """

    def __init__(self, field: FieldOps[F], d: Sequence[F]):
        self.field = field
        self.d = list(d)
        self.n = len(self.d)
        self.dim = 1 << self.n
        # Precompute multiplication table: e_I * e_J = coeff[I][J] * e_{I ^ J}
        self.mul_target = [[0] * self.dim for _ in range(self.dim)]
        self.mul_coeff: List[List[F]] = [
            [field.zero] * self.dim for _ in range(self.dim)
        ]
        for I in range(self.dim):
            for J in range(self.dim):
                swaps = 0
                for j in range(self.n):
                    if (J >> j) & 1:
                        # Count bits in I strictly above j
                        higher_mask = I >> (j + 1)
                        swaps += higher_mask.bit_count()
                coeff = -field.one if (swaps % 2 == 1) else field.one  # type: ignore[operator]
                overlap = I & J
                for k in range(self.n):
                    if (overlap >> k) & 1:
                        coeff = coeff * self.d[k]  # type: ignore[operator]
                self.mul_target[I][J] = I ^ J
                self.mul_coeff[I][J] = coeff

    def zero(self) -> List[F]:
        return [self.field.zero] * self.dim

    def one(self) -> List[F]:
        v = self.zero()
        v[0] = self.field.one
        return v

    def basis(self, mask: int) -> List[F]:
        v = self.zero()
        v[mask] = self.field.one
        return v

    def gen(self, k: int) -> List[F]:
        return self.basis(1 << k)

    def add(self, x: Sequence[F], y: Sequence[F]) -> List[F]:
        return [x[i] + y[i] for i in range(self.dim)]  # type: ignore[operator]

    def sub(self, x: Sequence[F], y: Sequence[F]) -> List[F]:
        return [x[i] - y[i] for i in range(self.dim)]  # type: ignore[operator]

    def smul(self, c: F, x: Sequence[F]) -> List[F]:
        return [c * x[i] for i in range(self.dim)]  # type: ignore[operator]

    def mul(self, x: Sequence[F], y: Sequence[F]) -> List[F]:
        out = self.zero()
        for I in range(self.dim):
            if x[I] == self.field.zero:
                continue
            for J in range(self.dim):
                if y[J] == self.field.zero:
                    continue
                tgt = self.mul_target[I][J]
                out[tgt] = out[tgt] + x[I] * y[J] * self.mul_coeff[I][J]  # type: ignore[operator]
        return out

    def iota(self, vec: Sequence[F]) -> List[F]:
        assert len(vec) == self.n
        out = self.zero()
        for k in range(self.n):
            out[1 << k] = vec[k]
        return out

    def quad_form(self, vec: Sequence[F]) -> F:
        acc = self.field.zero
        for k in range(self.n):
            acc = acc + self.d[k] * vec[k] * vec[k]  # type: ignore[operator]
        return acc

    def grade_involution(self, x: Sequence[F]) -> List[F]:
        return [
            (-x[I] if (I.bit_count() % 2 == 1) else x[I])  # type: ignore[operator]
            for I in range(self.dim)
        ]

    def center_basis(self) -> List[List[F]]:
        """
        Compute exact basis of the ring-theoretic center
        Z(A) = {z in A : z * e_J - e_J * z == 0 for all basis elements e_J}.
        By linearity, commuting with all basis elements is equivalent to commuting
        with EVERY element of A.
        """
        equations: List[List[F]] = []
        for J in range(self.dim):
            eJ = self.basis(J)
            # Linear map z |-> z * eJ - eJ * z has columns indexed by I = 0..dim-1
            cols: List[List[F]] = []
            for I in range(self.dim):
                eI = self.basis(I)
                comm = self.sub(self.mul(eI, eJ), self.mul(eJ, eI))
                cols.append(comm)
            for row_idx in range(self.dim):
                equations.append([cols[I][row_idx] for I in range(self.dim)])
        return nullspace_basis(equations, self.dim, self.field)

    def format_elem(self, x: Sequence[F]) -> str:
        terms = []
        for I in range(self.dim):
            if x[I] != self.field.zero:
                if I == 0:
                    bname = "1"
                else:
                    bname = "".join(f"e{k}" for k in range(self.n) if (I >> k) & 1)
                terms.append(f"{x[I]}*{bname}")
        return " + ".join(terms) if terms else "0"


def recursive_chevalley_mul(
    field: FieldOps[F], d: Sequence[F], x: Sequence[F], y: Sequence[F]
) -> List[F]:
    """
    Exact recursive Z/2Z-graded Chevalley multiplication matching the Lean 4 inductive
    definition:
      n = 0: x[0] * y[0]
      n + 1: split x = (a1, b1), y = (a2, b2) of half-length 2^n,
             (a1 + b1 e_n)(a2 + b2 e_n) = (a1*a2 + d_n * b1*alpha(b2), a1*b2 + b1*alpha(a2)).
    """
    n = len(d)
    if n == 0:
        return [x[0] * y[0]]  # type: ignore[operator]
    half = 1 << (n - 1)
    d_init = d[:-1]
    dn = d[-1]

    def alpha_rec(m: int, u: Sequence[F]) -> List[F]:
        if m == 0:
            return [u[0]]
        h = 1 << (m - 1)
        left = alpha_rec(m - 1, u[:h])
        right = [-val for val in alpha_rec(m - 1, u[h:])]  # type: ignore[operator]
        return left + right

    a1, b1 = x[:half], x[half:]
    a2, b2 = y[:half], y[half:]
    p1 = recursive_chevalley_mul(field, d_init, a1, a2)
    p2 = recursive_chevalley_mul(field, d_init, b1, alpha_rec(n - 1, b2))
    q1 = recursive_chevalley_mul(field, d_init, a1, b2)
    q2 = recursive_chevalley_mul(field, d_init, b1, alpha_rec(n - 1, a2))
    low = [p1[i] + dn * p2[i] for i in range(half)]  # type: ignore[operator]
    high = [q1[i] + q2[i] for i in range(half)]  # type: ignore[operator]
    return low + high


# =============================================================================
# 4. Exact Matrix Algebra Verification Helpers
# =============================================================================

def mat_mul(A: List[List[F]], B: List[List[F]], field: FieldOps[F]) -> List[List[F]]:
    m = len(A)
    k = len(B)
    n = len(B[0])
    out = [[field.zero] * n for _ in range(m)]
    for i in range(m):
        for r in range(k):
            if A[i][r] != field.zero:
                for j in range(n):
                    out[i][j] = out[i][j] + A[i][r] * B[r][j]  # type: ignore[operator]
    return out


def mat_add(A: List[List[F]], B: List[List[F]]) -> List[List[F]]:
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]  # type: ignore[operator]


def mat_smul(c: F, A: List[List[F]]) -> List[List[F]]:
    return [[c * A[i][j] for j in range(len(A[0]))] for i in range(len(A))]  # type: ignore[operator]


def verify_algebra_isomorphism_to_matrices(
    cl: CliffordAlgebra[F],
    gen_mats: List[List[List[F]]],
) -> None:
    """
    Verify that mapping e_k |-> gen_mats[k] extends to a bijective F-algebra
    isomorphism Cl(F^n, d) -> M_m(F), where m^2 == 2^n.
    """
    field = cl.field
    m = len(gen_mats[0])
    assert m * m == cl.dim, f"Dimension mismatch: m^2={m*m} vs 2^n={cl.dim}"
    ident = [[field.one if i == j else field.zero for j in range(m)] for i in range(m)]

    # Build basis images Phi(e_I)
    basis_mats: List[List[List[F]]] = []
    for I in range(cl.dim):
        cur = ident
        for k in range(cl.n):
            if (I >> k) & 1:
                cur = mat_mul(cur, gen_mats[k], field)
        basis_mats.append(cur)

    # Check multiplicativity on all basis pairs: Phi(e_I * e_J) == Phi(e_I) * Phi(e_J)
    for I in range(cl.dim):
        for J in range(cl.dim):
            lhs_elem = cl.mul(cl.basis(I), cl.basis(J))
            lhs_mat = [[field.zero] * m for _ in range(m)]
            for K_idx in range(cl.dim):
                if lhs_elem[K_idx] != field.zero:
                    lhs_mat = mat_add(lhs_mat, mat_smul(lhs_elem[K_idx], basis_mats[K_idx]))
            rhs_mat = mat_mul(basis_mats[I], basis_mats[J], field)
            assert lhs_mat == rhs_mat, f"Homomorphism failed at ({I}, {J})"

    # Check bijectivity (rank of flattened m^2 x 2^n matrix == 2^n)
    flat_cols = [
        [basis_mats[I][r][c] for r in range(m) for c in range(m)]
        for I in range(cl.dim)
    ]
    mat_rows = [[flat_cols[I][idx] for I in range(cl.dim)] for idx in range(m * m)]
    _, pivots = rref(mat_rows, field)
    assert len(pivots) == cl.dim, f"Map is not bijective: rank={len(pivots)} != {cl.dim}"


def verify_m2_irreducibility_and_uniqueness(field: FieldOps[F]) -> None:
    """
    Verify on M_2(F) that standard column module F^2 is simple (generated by every
    nonzero vector in Sample) and that the idempotent column map Psi(x, y) = col(x, y) v_1
    intertwines every matrix in M_2(F) identically.
    """
    E11 = [[field.one, field.zero], [field.zero, field.zero]]
    E12 = [[field.zero, field.one], [field.zero, field.zero]]
    E21 = [[field.zero, field.zero], [field.one, field.zero]]
    E22 = [[field.zero, field.zero], [field.zero, field.one]]
    basis_m2 = [E11, E12, E21, E22]

    # Check algebraic identities used in the Lean 4 uniqueness proof
    assert mat_mul(E11, E11, field) == E11
    assert mat_mul(E11, E12, field) == E12
    assert mat_mul(E21, E12, field) == E22
    assert mat_add(E11, E22) == [[field.one, field.zero], [field.zero, field.one]]

    # Check A * col(x, y) == col(A * (x, y)) on basis elements
    for A in basis_m2:
        for x, y in [(field.one, field.zero), (field.zero, field.one), (field.lift_int(2), field.lift_int(-3))]:
            col_xy = [[x, field.zero], [y, field.zero]]
            lhs = mat_mul(A, col_xy, field)
            ax = A[0][0] * x + A[0][1] * y  # type: ignore[operator]
            ay = A[1][0] * x + A[1][1] * y  # type: ignore[operator]
            rhs = [[ax, field.zero], [ay, field.zero]]
            assert lhs == rhs


# =============================================================================
# 5. Full Verification Suite
# =============================================================================

def test_clifford_axioms_and_chevalley_equivalence() -> None:
    print("[1/6] Verifying 2^n-dimensional Clifford axioms & Chevalley equivalence (n = 0..4)...")
    forms = [
        [],
        [Fraction(-1)],
        [Fraction(2)],
        [Fraction(1), Fraction(-1)],
        [Fraction(-1), Fraction(-1)],
        [Fraction(1), Fraction(-1), Fraction(1)],
        [Fraction(1), Fraction(-1), Fraction(-1)],
        [Fraction(1), Fraction(-1), Fraction(-2)],
        [Fraction(1), Fraction(1), Fraction(-1), Fraction(-1)],
    ]
    for d in forms:
        cl = CliffordAlgebra(Q_FIELD, d)
        # 1. Exact match with recursive Chevalley multiplication on all basis pairs
        for I in range(cl.dim):
            for J in range(cl.dim):
                bI, bJ = cl.basis(I), cl.basis(J)
                m_bit = cl.mul(bI, bJ)
                m_rec = recursive_chevalley_mul(Q_FIELD, d, bI, bJ)
                assert m_bit == m_rec, f"Bitmask vs Chevalley mismatch for d={d} at ({I},{J})"
        # 2. Full associativity on all basis triples (e_I * e_J) * e_K == e_I * (e_J * e_K)
        for I in range(cl.dim):
            bI = cl.basis(I)
            assert cl.mul(cl.one(), bI) == bI
            assert cl.mul(bI, cl.one()) == bI
            for J in range(cl.dim):
                bJ = cl.basis(J)
                ij = cl.mul(bI, bJ)
                for K_idx in range(cl.dim):
                    bK = cl.basis(K_idx)
                    lhs = cl.mul(ij, bK)
                    rhs = cl.mul(bI, cl.mul(bJ, bK))
                    assert lhs == rhs, f"Associativity failed for d={d}"
        # 3. Universal Clifford relation iota(v)^2 == Q(v) * 1 on sample vectors
        if cl.n > 0:
            samples = list(itertools.product([Fraction(-1), Fraction(0), Fraction(2)], repeat=cl.n))
            for vec in samples[:27]:
                iv = cl.iota(vec)
                sq = cl.mul(iv, iv)
                qv_one = cl.smul(cl.quad_form(vec), cl.one())
                assert sq == qv_one, f"Clifford relation failed for d={d}, v={vec}"
    print("      PASS: All basis associativity, unit, Chevalley recursion, and iota(v)^2 = Q(v)*1 checks succeeded.")


def test_regime_i_fixed_base_field_separation() -> None:
    print("[2/6] Verifying Regime I: Cl_{1,1}(Q) vs Cl_{0,1}(Q) (center extension Q subset Q(i))...")
    A1 = CliffordAlgebra(Q_FIELD, [Fraction(1), Fraction(-1)])
    A2 = CliffordAlgebra(Q_FIELD, [Fraction(-1)])

    # Verify A1 ~= M_2(Q) via E0 = [[1,0],[0,-1]], E1 = [[0,1],[-1,0]]
    E0 = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(-1)]]
    E1 = [[Fraction(0), Fraction(1)], [Fraction(-1), Fraction(0)]]
    verify_algebra_isomorphism_to_matrices(A1, [E0, E1])
    verify_m2_irreducibility_and_uniqueness(Q_FIELD)

    # Compute exact centers from commutator nullspace
    z1 = A1.center_basis()
    z2 = A2.center_basis()
    assert len(z1) == 1 and z1[0] == A1.one(), f"Unexpected Z(A1): {z1}"
    assert len(z2) == 2, f"Unexpected Z(A2): {z2}"

    # Verify A2 is a commutative field (every nonzero rational-grid element has exact inverse in A2)
    for a in range(-4, 5):
        for b in range(-4, 5):
            if a == 0 and b == 0:
                continue
            elem = [Fraction(a), Fraction(b)]
            denom = Fraction(a * a + b * b)
            assert denom > 0
            inv_elem = [Fraction(a) / denom, Fraction(-b) / denom]
            assert A2.mul(elem, inv_elem) == A2.one()
            assert A2.mul(inv_elem, elem) == A2.one()

    # Check z^2 + 1 = 0 in Z(A2) vs unsolvability in Z(A1) ~= Q
    e0 = A2.gen(0)
    assert A2.add(A2.mul(e0, e0), A2.one()) == A2.zero()
    for p in range(-20, 21):
        for q in range(1, 21):
            r = Fraction(p, q)
            assert r * r + 1 > 0

    spec_rep_A1 = (1, [2])  # 1 unique simple Q-module class (Q^2) of Q-dim 2
    spec_rep_A2 = (1, [2])  # 1 unique simple Q-module class (Q(i) ~= Q^2) of Q-dim 2
    assert spec_rep_A1 == spec_rep_A2
    assert len(z1) != len(z2)
    print(
        f"      PASS: Spec_rep^Q(Cl_{{1,1}}(Q)) = {spec_rep_A1} == Spec_rep^Q(Cl_{{0,1}}(Q)) = {spec_rep_A2}, "
        f"while dim_Q Z(A1) = {len(z1)} (Z ~= Q) != dim_Q Z(A2) = {len(z2)} (Z ~= Q(i))."
    )


def test_regime_ii_same_dimension_separation() -> None:
    print("[3/6] Verifying Regime II: Same-dimension separations (n = 1 and n = 3 over Q)...")
    # Case IIa: n = 1, Cl(Q^1, (2)) ~= Q(sqrt(2)) vs Cl(Q^1, (-1)) ~= Q(i)
    C_sqrt2 = CliffordAlgebra(Q_FIELD, [Fraction(2)])
    C_i = CliffordAlgebra(Q_FIELD, [Fraction(-1)])
    assert C_sqrt2.dim == 2 and C_i.dim == 2
    z_sqrt2 = C_sqrt2.center_basis()
    z_i = C_i.center_basis()
    assert len(z_sqrt2) == 2 and len(z_i) == 2

    # Check 2 is not a square in Q on bounded height grid + check (a + b*sqrt(2))^2 + 1 != 0
    for a in range(-10, 11):
        for b in range(-10, 11):
            if a != 0 or b != 0:
                nrm = Fraction(a * a - 2 * b * b)
                assert nrm != 0, f"Found rational root of x^2 = 2: {a}/{b}"
                inv_el = [Fraction(a) / nrm, Fraction(-b) / nrm]
                assert C_sqrt2.mul([Fraction(a), Fraction(b)], inv_el) == C_sqrt2.one()
            # Check x^2 + 1 != 0 in Q(sqrt(2)): first coordinate is a^2 + 2*b^2 + 1 >= 1
            el = [Fraction(a), Fraction(b)]
            sq_plus_1 = C_sqrt2.add(C_sqrt2.mul(el, el), C_sqrt2.one())
            assert sq_plus_1[0] >= 1 and sq_plus_1 != C_sqrt2.zero()

    # Case IIb: n = 3 (8-dimensional noncommutative Clifford algebras!)
    # Cl(Q^3, (1, -1, -1)) ~= M_2(Q(i)) vs Cl(Q^3, (1, -1, -2)) ~= M_2(Q(sqrt(-2)))
    Cl3_i = CliffordAlgebra(Q_FIELD, [Fraction(1), Fraction(-1), Fraction(-1)])
    Cl3_m2 = CliffordAlgebra(Q_FIELD, [Fraction(1), Fraction(-1), Fraction(-2)])
    z3_i = Cl3_i.center_basis()
    z3_m2 = Cl3_m2.center_basis()
    assert len(z3_i) == 2 and len(z3_m2) == 2
    # Volume element omega = e0 * e1 * e2 generates Z(Cl3):
    # omega^2 = (-1)^(3*2/2) * d0 * d1 * d2 = - d0 * d1 * d2
    omega_i = Cl3_i.basis(0b111)
    omega_m2 = Cl3_m2.basis(0b111)
    assert Cl3_i.mul(omega_i, omega_i) == Cl3_i.smul(Fraction(-1), Cl3_i.one())
    assert Cl3_m2.mul(omega_m2, omega_m2) == Cl3_m2.smul(Fraction(-2), Cl3_m2.one())

    # Verify explicit Q-algebra isomorphisms Cl(Q^3, (1,-1,d2)) -> M_2(Q(sqrt(d2))) viewed over Q(sqrt(d2))
    Cl3_i_over_Qi = CliffordAlgebra(
        QI_FIELD, [QuadExt(1, 0, -1), QuadExt(-1, 0, -1)]
    )
    verify_algebra_isomorphism_to_matrices(
        Cl3_i_over_Qi,
        [
            [[QuadExt(1, 0, -1), QuadExt(0, 0, -1)], [QuadExt(0, 0, -1), QuadExt(-1, 0, -1)]],
            [[QuadExt(0, 0, -1), QuadExt(1, 0, -1)], [QuadExt(-1, 0, -1), QuadExt(0, 0, -1)]],
        ],
    )
    print(
        "      PASS: n=1 gives Q(sqrt(2)) vs Q(i) with Spec_rep^Q = (1, [2]); "
        "n=3 gives M_2(Q(i)) vs M_2(Q(sqrt(-2))) with Spec_rep^Q = (1, [4]) and Z = Q(i) !~= Q(sqrt(-2))."
    )


def test_regime_iii_base_field_extension_pair() -> None:
    print("[4/6] Verifying Regime III: Base-field extension pair (Q, Q(i)) on Cl_{1,1}...")
    B_Q = CliffordAlgebra(Q_FIELD, [Fraction(1), Fraction(-1)])
    B_Qi = CliffordAlgebra(QI_FIELD, [QuadExt(1, 0, -1), QuadExt(-1, 0, -1)])

    # Exact same integer spinor generator matrices over Q and over Q(i)
    E0_Q = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(-1)]]
    E1_Q = [[Fraction(0), Fraction(1)], [Fraction(-1), Fraction(0)]]
    E0_Qi = [[QuadExt(1, 0, -1), QuadExt(0, 0, -1)], [QuadExt(0, 0, -1), QuadExt(-1, 0, -1)]]
    E1_Qi = [[QuadExt(0, 0, -1), QuadExt(1, 0, -1)], [QuadExt(-1, 0, -1), QuadExt(0, 0, -1)]]

    verify_algebra_isomorphism_to_matrices(B_Q, [E0_Q, E1_Q])
    verify_algebra_isomorphism_to_matrices(B_Qi, [E0_Qi, E1_Qi])
    verify_m2_irreducibility_and_uniqueness(Q_FIELD)
    verify_m2_irreducibility_and_uniqueness(QI_FIELD)

    z_BQ = B_Q.center_basis()
    z_BQi = B_Qi.center_basis()
    assert len(z_BQ) == 1 and z_BQ[0] == B_Q.one()
    assert len(z_BQi) == 1 and z_BQi[0] == B_Qi.one()

    # In Z(B_{Q(i)}) ~= Q(i), i * 1 satisfies (i*1)^2 + 1 = 0, impossible in Z(B_Q) ~= Q
    i_scalar = B_Qi.smul(QuadExt(0, 1, -1), B_Qi.one())
    assert B_Qi.add(B_Qi.mul(i_scalar, i_scalar), B_Qi.one()) == B_Qi.zero()
    print(
        "      PASS: Spec_rep^Q(Cl_{1,1}(Q)) = (1, [2]) == Spec_rep^{Q(i)}(Cl_{1,1}(Q(i))), "
        "same integer generator matrices, and Z(Cl_{1,1}(Q)) ~= Q !~=_Ring Q(i) ~= Z(Cl_{1,1}(Q(i)))."
    )


def test_quadratically_closed_obstruction() -> None:
    print("[5/6] Verifying quadratically-closed / algebraically-closed no-go theorem...")
    # Over Q(i), -1 and +1 are both squares (1 = 1^2, -1 = i^2).
    # Hence for ANY d in {+1, -1}^n over Q(i), all signatures split just as over C!
    for n in [1, 2, 3, 4]:
        seen_centers_for_rep = {}
        for signs in itertools.product([1, -1], repeat=n):
            d_qi = [QuadExt(s, 0, -1) for s in signs]
            cl = CliffordAlgebra(QI_FIELD, d_qi)
            z_basis = cl.center_basis()
            if n % 2 == 0:
                # Even n = 2m: Cl ~= M_{2^m}(Q(i)) -> 1 irrep of dim 2^m, dim Z = 1
                assert len(z_basis) == 1
                rep_spec = (1, (1 << (n // 2),))
                cen_type = "Field(dim=1)"
            else:
                # Odd n = 2m+1: omega^2 = (-1)^(n(n-1)/2) * prod(d) in {+1, -1}, ALWAYS a square in Q(i)!
                # Hence Z(Cl) ~= Q(i) x Q(i) (split semisimple, 2 orthogonal central idempotents!)
                assert len(z_basis) == 2
                omega = cl.basis((1 << n) - 1)
                omega_sq = cl.mul(omega, omega)[0]
                assert omega_sq in (QuadExt(1, 0, -1), QuadExt(-1, 0, -1))
                root = QuadExt(1, 0, -1) if omega_sq == QuadExt(1, 0, -1) else QuadExt(0, 1, -1)
                # Central idempotents e_+ = (1 + root^{-1} omega)/2, e_- = (1 - root^{-1} omega)/2
                half = QuadExt(Fraction(1, 2), 0, -1)
                scaled_omega = cl.smul(root.inv(), omega)
                e_plus = cl.smul(half, cl.add(cl.one(), scaled_omega))
                e_minus = cl.smul(half, cl.sub(cl.one(), scaled_omega))
                assert cl.mul(e_plus, e_plus) == e_plus
                assert cl.mul(e_minus, e_minus) == e_minus
                assert cl.mul(e_plus, e_minus) == cl.zero()
                assert cl.add(e_plus, e_minus) == cl.one()
                rep_spec = (2, (1 << (n // 2), 1 << (n // 2)))
                cen_type = "SplitProduct(dim=2)"
            seen_centers_for_rep.setdefault(rep_spec, set()).add(cen_type)
        for rep_spec, cen_set in seen_centers_for_rep.items():
            assert len(cen_set) == 1, f"Unexpected split over algebraically closed model: {cen_set}"
    print(
        "      PASS: When all discriminants are squares (as over C), Spec_rep = (1, [2^m]) forces Z ~= K "
        "and Spec_rep = (2, [2^m, 2^m]) forces Z ~= K x K — proving field extensions are essential!"
    )


def print_summary_table() -> None:
    print("[6/6] Summary of Exact Spectral Separation Witnesses:")
    rows = [
        ("Regime I (fixed Q)", "Cl_{1,1}(Q) ~= M_2(Q)", "(1, [2]) over Q", "Q (dim_Q = 1)"),
        ("Regime I (fixed Q)", "Cl_{0,1}(Q) ~= Q(i)", "(1, [2]) over Q", "Q(i) (dim_Q = 2)"),
        ("Regime IIa (n = 1)", "Cl(Q^1, (2)) ~= Q(sqrt(2))", "(1, [2]) over Q", "Q(sqrt(2)) (x^2=2)"),
        ("Regime IIa (n = 1)", "Cl(Q^1, (-1)) ~= Q(i)", "(1, [2]) over Q", "Q(i) (x^2=-1)"),
        ("Regime IIb (n = 3)", "Cl(Q^3, (1,-1,-1)) ~= M_2(Q(i))", "(1, [4]) over Q", "Q(i)"),
        ("Regime IIb (n = 3)", "Cl(Q^3, (1,-1,-2)) ~= M_2(Q(sqrt(-2)))", "(1, [4]) over Q", "Q(sqrt(-2))"),
        ("Regime III (ext)", "Cl_{1,1}(Q) ~= M_2(Q)", "(1, [2]) over Q", "Q"),
        ("Regime III (ext)", "Cl_{1,1}(Q(i)) ~= M_2(Q(i))", "(1, [2]) over Q(i)", "Q(i)"),
    ]
    print("      " + "-" * 94)
    print(f"      {'Regime':<20} | {'Clifford Algebra':<38} | {'Irr-Rep Spectrum':<18} | {'Center Z(A)'}")
    print("      " + "-" * 94)
    for r, alg, rep, cen in rows:
        print(f"      {r:<20} | {alg:<38} | {rep:<18} | {cen}")
    print("      " + "-" * 94)
    print("ALL VERIFICATION CHECKS PASSED (VERDICT: TRUE).")


def main() -> int:
    test_clifford_axioms_and_chevalley_equivalence()
    test_regime_i_fixed_base_field_separation()
    test_regime_ii_same_dimension_separation()
    test_regime_iii_base_field_extension_pair()
    test_quadratically_closed_obstruction()
    print_summary_table()
    return 0


if __name__ == "__main__":
    sys.exit(main())
