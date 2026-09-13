/-
  Axiom audit for the refutation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below must report only core axioms (`propext`, `Quot.sound`,
  possibly `Classical.choice`); in particular none may report `sorryAx` and none
  depends on Mathlib.  The concrete `decide` theorems are expected to be
  axiom-free.
-/

import Main

open Tlmc1109

-- General lemma: distinctness forces multiplicity one
#print axioms count_eq_one_of_nodup

-- Pairwise distinctness of the exponents of H3, H4, I2(m)
#print axioms h3_nodup
#print axioms h4_nodup
#print axioms i2_nodup

-- No exponent has multiplicity >= 2
#print axioms h3_no_repeat
#print axioms h4_no_repeat
#print axioms i2_no_repeat

-- The collected refutation (universal reading over irreducible types)
#print axioms conjecture_00000001109_false

-- The (h, 1) reading: h is a degree, not an exponent
#print axioms h3_h_not_exponent
#print axioms h4_h_not_exponent
#print axioms h3_with_h_no_repeat
#print axioms h4_with_h_no_repeat

-- Honest scope boundary: the reducible group A1 x H3
#print axioms reducible_has_repeated
#print axioms reducible_count_one
