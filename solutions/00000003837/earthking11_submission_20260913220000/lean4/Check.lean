/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only core axioms (`propext`, `Quot.sound`);
  in particular none may report `sorryAx` and none depends on Mathlib.
-/

import Main

open StarParity837

-- The crystal B(ω₁): two elements, one arrow
#print axioms B1_card
#print axioms f1_top
#print axioms e1_bottom

-- The star involution: involutive, arrow-reversing, weight-negating
#print axioms star_involutive
#print axioms star_reverses_f
#print axioms star_reverses_e
#print axioms wt_star
#print axioms star_apply

-- The refutation: 0 fixed points at λ = ω₁
#print axioms star_fixedCount
#print axioms star_even
#print axioms star_lt_three
#print axioms conjecture_00000003837_false
#print axioms star_conjecture_false

-- Robustness: every involution of B(ω₁) has even fixed count (< 3)
#print axioms fixedCount_eq
#print axioms involution_fixedCount_even
#print axioms involution_fixedCount_lt_three
#print axioms arrow_reversing_involution_eq_star
#print axioms no_weight_preserving_arrow_reversal
