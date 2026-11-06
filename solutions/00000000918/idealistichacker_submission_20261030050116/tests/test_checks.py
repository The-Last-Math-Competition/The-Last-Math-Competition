import unittest

from checks import (F, I, ONE, U3, ZERO, Z3, aadd, amul, astar, atom, cadd, cmul,
                    coordinate, corner, matrix_identity, matrix_samples, matrix_trace,
                    mmul, mstar, norm_sq, regression, validate_algebra, validate_complex,
                    validate_matrix)


class ExactQuasitraceDiagnostics(unittest.TestCase):
    def test_complex_conjugation_and_square(self):
        z = (F(3, 2), -F(2, 3))
        self.assertEqual(cmul(astar((z, ZERO, ZERO))[0], z), (norm_sq(z), 0))

    def test_actual_three_distinct_coordinates(self):
        self.assertEqual(tuple(tuple(coordinate(i, atom(j)) for j in range(3)) for i in range(3)),
                         ((ONE, ZERO, ZERO), (ZERO, ONE, ZERO), (ZERO, ZERO, ONE)))

    def test_pointwise_algebra_operations(self):
        self.assertEqual(amul(atom(0), atom(1)), Z3)
        self.assertEqual(amul(U3, atom(1)), atom(1))
        self.assertEqual(coordinate(2, aadd(atom(2), atom(2))), (2, 0))

    def test_complex_linearity_is_not_real_only(self):
        a = (I, ONE, ZERO)
        self.assertEqual(coordinate(0, amul((I, I, I), a)), cmul(I, coordinate(0, a)))

    def test_real_affine_minor_not_a_single_pair_test(self):
        p1, p2 = atom(1), atom(2)
        rows = tuple(tuple(coordinate(i, p)[0] - coordinate(0, p)[0] for p in (p1, p2)) for i in (1, 2))
        self.assertEqual(rows, ((1, 0), (0, 1)))

    def test_matrix_identity_trace_must_not_be_normalized(self):
        self.assertEqual(matrix_trace(0, matrix_identity()), (2, 0))
        self.assertNotEqual(matrix_trace(0, matrix_identity()), ONE)

    def test_corner_is_not_the_diagonal_identity_copy(self):
        for i in range(3):
            self.assertEqual(matrix_trace(i, corner(U3)), ONE)
            self.assertNotEqual(matrix_trace(i, matrix_identity()), matrix_trace(i, corner(U3)))

    def test_matrix_star_is_conjugate_transpose(self):
        X = ((atom(0), (I, ZERO, ZERO)), (atom(1), atom(2)))
        self.assertEqual(mstar(X)[1][0], ((0, -1), ZERO, ZERO))
        self.assertEqual(mstar(mstar(X)), X)

    def test_cyclic_trace_without_commuting_matrices(self):
        E01 = ((Z3, U3), (Z3, Z3))
        E10 = ((Z3, Z3), (U3, Z3))
        self.assertNotEqual(mmul(E01, E10), mmul(E10, E01))
        self.assertEqual(matrix_trace(2, mmul(E01, E10)), matrix_trace(2, mmul(E10, E01)))

    def test_all_exact_regression_cases(self):
        report = regression()
        self.assertEqual(report["algebra_coordinate_pair_checks"], 12288)
        self.assertEqual(report["affine_minor"], "1")

    def test_float_boolean_and_malformed_complex_rejected(self):
        for value in ((1.0, 0), (True, 0), (1,), [1, 0]):
            with self.subTest(value=value), self.assertRaises(ValueError):
                validate_complex(value)

    def test_bad_dimensions_and_indices_rejected(self):
        with self.assertRaises(ValueError):
            validate_algebra((ONE, ONE))
        with self.assertRaises(ValueError):
            validate_matrix(((U3, Z3),))
        for value in (-1, 3, True):
            with self.subTest(value=value), self.assertRaises(ValueError):
                coordinate(value, U3)


if __name__ == "__main__":
    unittest.main()
