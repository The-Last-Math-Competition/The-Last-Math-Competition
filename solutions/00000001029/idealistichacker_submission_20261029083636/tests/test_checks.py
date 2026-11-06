import unittest

from checks import actual_design_gf2, carrier_members, catalogue_gf2, subspace_gf2, subspaces_gf2, valid_two_label_tables


class IndependentFiniteChecks(unittest.TestCase):
    def test_zero_dimension_has_one_subspace(self):
        self.assertEqual(subspaces_gf2(0, 0), (1,))

    def test_actual_closure_rejects_missing_zero_and_sum(self):
        self.assertFalse(subspace_gf2(0, 2))
        self.assertFalse(subspace_gf2(2, 2))
        self.assertFalse(subspace_gf2(7, 2))
        self.assertTrue(subspace_gf2(15, 2))

    def test_dimension_two_subspaces_of_cube(self):
        spaces = subspaces_gf2(3, 2)
        self.assertEqual(len(spaces), 7)
        self.assertTrue(all(len(carrier_members(s, 3)) == 4 for s in spaces))

    def test_whole_plane_catalogue(self):
        self.assertEqual(catalogue_gf2(2, 2), ((15,),))

    def test_all_two_spaces_catalogue(self):
        self.assertEqual(catalogue_gf2(3, 2), (subspaces_gf2(3, 2),))

    def test_whole_cube_catalogue(self):
        self.assertEqual(catalogue_gf2(3, 3), ((255,),))

    def test_invalid_parameters_do_not_create_vacuous_designs(self):
        for n, k in ((0, 0), (1, 1), (3, 1), (2, 3), (3, -1)):
            with self.subTest(n=n, k=k):
                self.assertEqual(catalogue_gf2(n, k), ())
                self.assertFalse(actual_design_gf2(n, k, ()))

    def test_empty_missing_or_duplicate_blocks_are_rejected(self):
        family = subspaces_gf2(3, 2)
        self.assertFalse(actual_design_gf2(3, 2, ()))
        self.assertFalse(actual_design_gf2(3, 2, family[:-1]))
        self.assertFalse(actual_design_gf2(3, 2, family + (family[0],)))

    def test_wrong_dimension_block_is_rejected(self):
        self.assertFalse(actual_design_gf2(3, 2, (255,)))

    def test_both_raw_labellings_of_the_two_element_field(self):
        tables = valid_two_label_tables()
        self.assertEqual(len(tables), 2)
        self.assertEqual({(t[0], t[1]) for t in tables}, {(0, 1), (1, 0)})
        canonical = next(t for t in tables if t[:2] == (0, 1))
        self.assertEqual(canonical[2], (0, 1, 1, 0))
        self.assertEqual(canonical[3], (0, 0, 0, 1))

    def test_diagnostic_resource_bound_is_explicit(self):
        for n in (-1, 4, True):
            with self.subTest(n=n), self.assertRaises(ValueError):
                catalogue_gf2(n, 2)
        with self.assertRaises(ValueError):
            carrier_members(16, 2)


if __name__ == "__main__":
    unittest.main()
