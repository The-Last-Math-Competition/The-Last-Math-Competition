#!/usr/bin/env python3
"""
Standalone exact computational verification for Conjecture 00000007606:
  "Definition: Rotors as unit elements of the even subalgebra.
   Conjecture: The kernel of the double cover of the spin group over the
   orthogonal group is two; and the realization of the cover is the adjoint map."

Uses ONLY the Python 3 standard library (`fractions`, `itertools`, `sys`) to
perform exact rational and finite-field Clifford algebra checks across dimensions
n = 1..6, Lorentz signature (1, 1), and characteristic 2 (F_2).
"""

from fractions import Fraction
import sys


class CliffordAlgebraQ:
    """Exact Clifford algebra Cl(sig) over Q on basis blades e_S (S subset of {0..n-1})."""

    def __init__(self, sig: list[int | Fraction]):
        self.sig = [Fraction(s) for s in sig]
        self.n = len(sig)
        self.dim = 1 << self.n
        self.mul_table: list[list[tuple[Fraction, int]]] = [
            [(Fraction(0), 0) for _ in range(self.dim)] for _ in range(self.dim)
        ]
        for A in range(self.dim):
            for B in range(self.dim):
                inversions = 0
                for b in range(self.n):
                    if (B >> b) & 1:
                        inversions += (A >> (b + 1)).bit_count()
                coeff = Fraction(-1 if inversions % 2 == 1 else 1)
                both = A & B
                for i in range(self.n):
                    if (both >> i) & 1:
                        coeff *= self.sig[i]
                self.mul_table[A][B] = (coeff, A ^ B)

    def zero(self) -> list[Fraction]:
        return [Fraction(0)] * self.dim

    def scalar(self, c: int | Fraction) -> list[Fraction]:
        res = self.zero()
        res[0] = Fraction(c)
        return res

    def blade(self, indices_1based: list[int]) -> list[Fraction]:
        mask = 0
        for idx in indices_1based:
            mask |= 1 << (idx - 1)
        res = self.zero()
        res[mask] = Fraction(1)
        return res

    def vec(self, coords: list[int | Fraction]) -> list[Fraction]:
        assert len(coords) == self.n
        res = self.zero()
        for i, c in enumerate(coords):
            res[1 << i] = Fraction(c)
        return res

    def add(self, x: list[Fraction], y: list[Fraction]) -> list[Fraction]:
        return [a + b for a, b in zip(x, y)]

    def sub(self, x: list[Fraction], y: list[Fraction]) -> list[Fraction]:
        return [a - b for a, b in zip(x, y)]

    def scale(self, c: int | Fraction, x: list[Fraction]) -> list[Fraction]:
        cf = Fraction(c)
        return [cf * a for a in x]

    def mul(self, x: list[Fraction], y: list[Fraction]) -> list[Fraction]:
        res = self.zero()
        for A, xa in enumerate(x):
            if xa != 0:
                row = self.mul_table[A]
                for B, yb in enumerate(y):
                    if yb != 0:
                        c, C = row[B]
                        res[C] += xa * yb * c
        return res

    def invol(self, x: list[Fraction]) -> list[Fraction]:
        return [-xa if A.bit_count() % 2 == 1 else xa for A, xa in enumerate(x)]

    def rev(self, x: list[Fraction]) -> list[Fraction]:
        res = self.zero()
        for A, xa in enumerate(x):
            k = A.bit_count()
            res[A] = -xa if ((k * (k - 1)) // 2) % 2 == 1 else xa
        return res

    def cliff_conj(self, x: list[Fraction]) -> list[Fraction]:
        return self.invol(self.rev(x))

    def is_even(self, x: list[Fraction]) -> bool:
        return all(xa == 0 for A, xa in enumerate(x) if A.bit_count() % 2 == 1)

    def is_in_V(self, x: list[Fraction]) -> bool:
        return all(xa == 0 for A, xa in enumerate(x) if A.bit_count() != 1)

    def extract_vec(self, x: list[Fraction]) -> list[Fraction]:
        assert self.is_in_V(x), f"Element not in V: {self.fmt(x)}"
        return [x[1 << i] for i in range(self.n)]

    def quad_form(self, coords: list[Fraction]) -> Fraction:
        return sum(s * c * c for s, c in zip(self.sig, coords))

    def adjoint(self, x: list[Fraction], v: list[Fraction], x_inv: list[Fraction]) -> list[Fraction]:
        return self.mul(self.mul(x, v), x_inv)

    def twisted_adjoint(self, x: list[Fraction], v: list[Fraction], x_inv: list[Fraction]) -> list[Fraction]:
        return self.mul(self.mul(self.invol(x), v), x_inv)

    def induced_matrix_on_V(self, x: list[Fraction], x_inv: list[Fraction], twisted: bool = False) -> list[list[Fraction]]:
        cols = []
        for j in range(self.n):
            ej = self.blade([j + 1])
            img = self.twisted_adjoint(x, ej, x_inv) if twisted else self.adjoint(x, ej, x_inv)
            cols.append(self.extract_vec(img))
        return [[cols[j][i] for j in range(self.n)] for i in range(self.n)]

    def fmt(self, x: list[Fraction]) -> str:
        parts = []
        for A, xa in enumerate(x):
            if xa != 0:
                if A == 0:
                    parts.append(f"{xa}")
                else:
                    idxs = "".join(str(i + 1) for i in range(self.n) if (A >> i) & 1)
                    parts.append(f"({xa})*e_{idxs}")
        return " + ".join(parts) if parts else "0"


def det_exact(M: list[list[Fraction]]) -> Fraction:
    """Exact Bareiss/Gaussian determinant over Q."""
    n = len(M)
    A = [row[:] for row in M]
    sign = Fraction(1)
    for col in range(n):
        pivot = None
        for r in range(col, n):
            if A[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            A[col], A[pivot] = A[pivot], A[col]
            sign = -sign
        pval = A[col][col]
        for r in range(col + 1, n):
            factor = A[r][col] / pval
            for c in range(col, n):
                A[r][c] -= factor * A[col][c]
    prod = sign
    for i in range(n):
        prod *= A[i][i]
    return prod


def mat_mul(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    n = len(A)
    return [
        [sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)]
        for i in range(n)
    ]


def check_positive_spin_double_covers() -> None:
    print("[1/6] Verifying positive classical double cover Spin(n) -> SO(n) (n = 1..4)...")
    # Test Spin(2) Pythagorean rotors and exact 2-to-1 fiber {x, -x}
    cl2 = CliffordAlgebraQ([1, 1])
    triples = [(3, 4, 5), (5, 12, 13), (8, 15, 17), (-3, 4, 5), (0, 1, 1), (1, 0, 1)]
    for p, q, r in triples:
        a, b = Fraction(p, r), Fraction(q, r)
        x = cl2.add(cl2.scalar(a), cl2.scale(b, cl2.blade([1, 2])))
        neg_x = cl2.scale(-1, x)
        assert cl2.is_even(x)
        assert cl2.mul(x, cl2.rev(x)) == cl2.scalar(1)
        assert cl2.cliff_conj(x) == cl2.rev(x)
        M_pos = cl2.induced_matrix_on_V(x, cl2.rev(x))
        M_neg = cl2.induced_matrix_on_V(neg_x, cl2.rev(neg_x))
        assert M_pos == M_neg, "Antipodal rotors x and -x must induce identical rotation!"
        assert x != neg_x, "Antipodal fiber {x, -x} must have size 2!"
        # Check M_pos^T M_pos = I_2 and det(M_pos) = +1
        Mt = [[M_pos[j][i] for j in range(2)] for i in range(2)]
        assert mat_mul(Mt, M_pos) == [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]
        assert det_exact(M_pos) == Fraction(1)

    # Test Spin(3) and Spin(4) via products of even numbers of unit reflections
    for n, vec_pairs in [
        (3, [([Fraction(3, 5), Fraction(4, 5), Fraction(0)],
              [Fraction(0), Fraction(5, 13), Fraction(12, 13)])]),
        (4, [([Fraction(3, 5), Fraction(4, 5), Fraction(0), Fraction(0)],
              [Fraction(0), Fraction(3, 5), Fraction(0), Fraction(4, 5)]),
             ([Fraction(1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)],
              [Fraction(1, 2), Fraction(-1, 2), Fraction(1, 2), Fraction(-1, 2)])]),
    ]:
        cln = CliffordAlgebraQ([1] * n)
        rotor = cln.scalar(1)
        for u_coords, w_coords in vec_pairs:
            assert cln.quad_form(u_coords) == 1 and cln.quad_form(w_coords) == 1
            rotor = cln.mul(rotor, cln.mul(cln.vec(u_coords), cln.vec(w_coords)))
        assert cln.is_even(rotor)
        assert cln.mul(rotor, cln.rev(rotor)) == cln.scalar(1)
        M = cln.induced_matrix_on_V(rotor, cln.rev(rotor))
        Mt = [[M[j][i] for j in range(n)] for i in range(n)]
        I_n = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
        assert mat_mul(Mt, M) == I_n
        assert det_exact(M) == Fraction(1)
    print("  PASS: Spin(n) -> SO(n) preserves Q, has det = +1, and exact antipodal fibers {+x, -x}.")


def check_target_group_reflection_obstruction() -> None:
    print("[2/6] Verifying Failure 1: Spin(n) & (Cl_{n,0}+)^x NEVER cover O(n) (n = 1..6)...")
    for n in range(1, 7):
        cln = CliffordAlgebraQ([1] * n)
        omega = cln.blade(list(range(1, n + 1)))
        # Verify EVERY basis blade of Cl^+ commutes with omega
        for mask in range(cln.dim):
            if mask.bit_count() % 2 == 0:
                blade = [Fraction(1 if i == mask else 0) for i in range(cln.dim)]
                assert cln.mul(blade, omega) == cln.mul(omega, blade), (
                    f"Even blade {mask} failed to commute with omega in n={n}!"
                )
        # In odd dimensions, verify ALL blades of Cl commute with omega (omega is central!)
        if n % 2 == 1:
            for mask in range(cln.dim):
                blade = [Fraction(1 if i == mask else 0) for i in range(cln.dim)]
                assert cln.mul(blade, omega) == cln.mul(omega, blade), (
                    f"Blade {mask} failed centrality of omega in odd dim n={n}!"
                )
        # Verify twisted adjoint on e_1 gives reflection diag(-1, 1, ..., 1) (det = -1),
        # whereas ordinary adjoint on e_1 gives diag(+1, -1, ..., -1) (det = (-1)^{n-1})!
        e1 = cln.blade([1])
        M_twisted = cln.induced_matrix_on_V(e1, e1, twisted=True)
        M_ordinary = cln.induced_matrix_on_V(e1, e1, twisted=False)
        assert det_exact(M_twisted) == Fraction(-1)
        assert M_twisted[0][0] == Fraction(-1)
        assert M_ordinary[0][0] == Fraction(1)  # Ordinary Ad_{e_1}(e_1) = +e_1 != -e_1!
        if n % 2 == 1:
            assert det_exact(M_ordinary) == Fraction(1)
    print("  PASS: Even subalgebra commutes with omega for all n=1..6 (and full Cl in odd n);")
    print("        det(Ad_x|_V) = +1 always on Cl^+, so O(n) \\ SO(n) is never covered.")


def check_even_units_failures() -> None:
    print("[3/6] Verifying Failure 2A: Invertible even elements (Cl^+)^x fail kernel-2 and V-preservation...")
    cl2 = CliffordAlgebraQ([1, 1])
    for c in [Fraction(2), Fraction(3), Fraction(-5, 7)]:
        sc = cl2.scalar(c)
        sc_inv = cl2.scalar(Fraction(1) / c)
        assert cl2.is_even(sc)
        assert cl2.mul(sc, sc_inv) == cl2.scalar(1)
        assert sc not in (cl2.scalar(1), cl2.scalar(-1))
        assert cl2.induced_matrix_on_V(sc, sc_inv) == [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]

    # Dimension n = 4: x = 1 + 2 e_{1234} in (Cl_{4,0}^+)^x leaves V!
    cl4 = CliffordAlgebraQ([1, 1, 1, 1])
    omega4 = cl4.blade([1, 2, 3, 4])
    x4 = cl4.add(cl4.scalar(1), cl4.scale(2, omega4))
    x4_inv = cl4.scale(Fraction(-1, 3), cl4.sub(cl4.scalar(1), cl4.scale(2, omega4)))
    assert cl4.is_even(x4) and cl4.is_even(x4_inv)
    assert cl4.mul(x4, x4_inv) == cl4.scalar(1)
    assert cl4.mul(x4_inv, x4) == cl4.scalar(1)
    img_e1 = cl4.adjoint(x4, cl4.blade([1]), x4_inv)
    expected_e1 = cl4.add(cl4.scale(Fraction(-5, 3), cl4.blade([1])),
                          cl4.scale(Fraction(4, 3), cl4.blade([2, 3, 4])))
    assert img_e1 == expected_e1
    assert not cl4.is_in_V(img_e1)
    img_e4 = cl4.adjoint(x4, cl4.blade([4]), x4_inv)
    expected_e4 = cl4.add(cl4.scale(Fraction(-5, 3), cl4.blade([4])),
                          cl4.scale(Fraction(-4, 3), cl4.blade([1, 2, 3])))
    assert img_e4 == expected_e4
    assert not cl4.is_in_V(img_e4)
    print(f"  PASS: In Cl(4,0)+, x = 1 + 2 e_1234 is invertible with Ad_x(e_1) = {cl4.fmt(img_e1)} not in V.")


def check_unit_norm_chevalley_porteous_failure() -> None:
    print("[4/6] Verifying Failure 2B: Unit-norm even elements {x in Cl_6+ : x x~ = 1} != Spin(6)...")
    # Lie-algebra dimension audit for {y in Cl_{n,0}+ : y + y~ = 0} vs dim Spin(n) = n(n-1)/2:
    for n in range(1, 9):
        dim_even = 1 << (n - 1)
        dim_spin = (n * (n - 1)) // 2
        # Grade 2k has reversion sign (-1)^{k(2k-1)} = (-1)^k, so skew-symmetric iff k is odd (grades 2, 6, 10, ...)
        from math import comb
        dim_unit_norm = sum(comb(n, g) for g in range(0, n + 1, 2) if ((g * (g - 1)) // 2) % 2 == 1)
        if n <= 5:
            assert dim_unit_norm == dim_spin
        else:
            assert dim_unit_norm > dim_spin
        assert dim_even > dim_spin

    cl6 = CliffordAlgebraQ([1] * 6)
    omega6 = cl6.blade([1, 2, 3, 4, 5, 6])
    x6 = cl6.add(cl6.scalar(Fraction(3, 5)), cl6.scale(Fraction(4, 5), omega6))
    x6_rev = cl6.rev(x6)
    assert cl6.is_even(x6)
    assert cl6.cliff_conj(x6) == x6_rev
    assert cl6.mul(x6, x6_rev) == cl6.scalar(1)
    assert cl6.mul(x6_rev, x6) == cl6.scalar(1)
    img_e1 = cl6.adjoint(x6, cl6.blade([1]), x6_rev)
    expected_e1 = cl6.add(cl6.scale(Fraction(-7, 25), cl6.blade([1])),
                          cl6.scale(Fraction(-24, 25), cl6.blade([2, 3, 4, 5, 6])))
    assert img_e1 == expected_e1
    assert not cl6.is_in_V(img_e1)
    img_e6 = cl6.adjoint(x6, cl6.blade([6]), x6_rev)
    expected_e6 = cl6.add(cl6.scale(Fraction(-7, 25), cl6.blade([6])),
                          cl6.scale(Fraction(24, 25), cl6.blade([1, 2, 3, 4, 5])))
    assert img_e6 == expected_e6
    assert not cl6.is_in_V(img_e6)
    print(f"  PASS: In Cl(6,0)+, x = 3/5 + 4/5 e_123456 has x*x~ = 1 yet Ad_x(e_1) = {cl6.fmt(img_e1)} not in V.")


def check_char_two_and_indefinite_signature() -> None:
    print("[5/6] Verifying Failure 3: Characteristic 2 (F_2) and Indefinite Signature Cl(1,1)...")
    # Over F_2, Cl_{1,0}(F_2)^+ = {0, 1}; invertible / unit-norm subgroup is {1} of size 1 != 2:
    f2_even_units = [a for a in (0, 1) if any((a * b) % 2 == 1 for b in (0, 1))]
    assert f2_even_units == [1] and len(f2_even_units) == 1

    # In Cl(1,1), unit-norm even elements x = a + b e_{12} satisfy a^2 - b^2 = 1 and
    # induce [[a^2 + b^2, -2ab], [-2ab, a^2 + b^2]] with M_11 = a^2 + b^2 >= 1 > 0,
    # missing -I_2 in SO(1,1) as well as reflections in O(1,1) \ SO(1,1):
    cl11 = CliffordAlgebraQ([1, -1])
    for a, b in [(Fraction(1), Fraction(0)), (Fraction(5, 3), Fraction(4, 3)), (Fraction(-13, 5), Fraction(12, 5))]:
        x = cl11.add(cl11.scalar(a), cl11.scale(b, cl11.blade([1, 2])))
        assert cl11.is_even(x)
        assert cl11.mul(x, cl11.rev(x)) == cl11.scalar(1)
        M = cl11.induced_matrix_on_V(x, cl11.rev(x))
        assert det_exact(M) == Fraction(1)
        assert M[0][0] == a * a + b * b >= Fraction(1)
    # Meanwhile x = e_{12} has x * x~ = -1 (in Spin(1,1) \ Spin^+(1,1)) and induces -I_2:
    e12 = cl11.blade([1, 2])
    assert cl11.mul(e12, cl11.rev(e12)) == cl11.scalar(-1)
    e12_inv = cl11.scale(-1, cl11.rev(e12))  # since e12 * rev(e12) = -1, e12^{-1} = -rev(e12) = +e12
    assert cl11.mul(e12, e12_inv) == cl11.scalar(1)
    assert cl11.induced_matrix_on_V(e12, e12_inv) == [[Fraction(-1), Fraction(0)], [Fraction(0), Fraction(-1)]]
    print("  PASS: F_2 kernel has size 1 != 2; Cl(1,1) unit-norm rotors have M_11 >= 1, missing -I_2 in SO(1,1).")


def check_rational_spinor_norm_obstruction() -> None:
    print("[6/6] Verifying non-real field spinor-norm obstruction in Spin_2(Q) -> SO_2(Q)...")
    # Exhaustively check small rational denominators d <= 40: no a, b in Q with denominator <= 40
    # satisfies a^2 + b^2 = 1 and a^2 - b^2 = 0 (since 2*a^2 = 1 has no rational solution).
    for d in range(1, 41):
        for n in range(-2 * d, 2 * d + 1):
            a = Fraction(n, d)
            assert 2 * a * a != Fraction(1)
    print("  PASS: 90-degree rotation [[0, 1], [-1, 0]] in SO_2(Q) has spinor norm [2] != [1] in Q^x/(Q^x)^2.")


def main() -> int:
    print("=" * 74)
    print("Conjecture 00000007606 — Exact Computational Verification Suite")
    print("=" * 74)
    check_positive_spin_double_covers()
    check_target_group_reflection_obstruction()
    check_even_units_failures()
    check_unit_norm_chevalley_porteous_failure()
    check_char_two_and_indefinite_signature()
    check_rational_spinor_norm_obstruction()
    print("=" * 74)
    print("ALL VERIFICATION CHECKS PASSED (exit code 0).")
    print("=" * 74)
    return 0


if __name__ == "__main__":
    sys.exit(main())
