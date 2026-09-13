/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only core axioms (`propext` and possibly
  `Quot.sound`); in particular none may report `sorryAx`, and none depends on
  Mathlib.
-/

import Main

open Tlmc1203

-- Closed forms and period facts for the primary witness S = {1,3}
#print axioms g_eq
#print axioms g_period
#print axioms least_period_two
#print axioms not_least_period_four
#print axioms two_not_dvd_seven

-- Closed form and period facts for the clause-1 witness S = {1,2}
#print axioms g12_eq
#print axioms g12_period
#print axioms least_period_three_12
#print axioms three_dvd_two_sq_sub_one
#print axioms clause1_fails_charitable

-- The packaged disproof of conjecture 00000001203
#print axioms conjecture_00000001203_false
