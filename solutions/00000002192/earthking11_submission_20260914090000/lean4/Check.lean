/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake build
      lake env lean Check.lean

  Every theorem should report only core axioms (`propext`, `Quot.sound`,
  possibly `Classical.choice`); in particular none may report `sorryAx`.
-/

import Main

open Tlmc2192

-- Basic facts about the standard example S_2
#print axioms ltS2_irrefl
#print axioms ltS2_asymm
#print axioms ltS2_03
#print axioms ltS2_12
#print axioms not_ltS2_01
#print axioms not_ltS2_10
#print axioms no_three_chain
#print axioms height_two

-- Two linear extensions realizing S_2
#print axioms isLinExt_L1
#print axioms isLinExt_L2
#print axioms inter_L1_L2
#print axioms inter_singleton

-- The lower bound: no single linear extension realizes S_2
#print axioms no_single
#print axioms not_dim_le_one
#print axioms not_dim_le_zero

-- The dimension is exactly 2
#print axioms dim_le_two
#print axioms dim_eq_two

-- The conjectured value and the contradiction
#print axioms formula_at_four
#print axioms conjecture_00000002192_false
