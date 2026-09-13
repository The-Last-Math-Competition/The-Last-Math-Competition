/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem below should report only core axioms (here: none at all, since
  all statements are closed by `decide`).  In particular none may report
  `sorryAx` and none depends on Mathlib.
-/

import Main

open Tlmc8419

-- The code, its weights, and its minimum distance
#print axioms gAB_eq
#print axioms code_closed
#print axioms weights
#print axioms minWeight_eq_three
#print axioms no_codeword_of_other_weight

-- The minimum-weight codewords
#print axioms gA_is_min
#print axioms gB_is_min
#print axioms minWeightWords_spec

-- The dual distance
#print axioms dualDistance_eq_two
#print axioms dual_word_of_weight_two
#print axioms no_dual_word_of_weight_one

-- The supports are {2,3,5} and {1,4,5}
#print axioms support_gA
#print axioms support_gB

-- The putative design fails the 1-design property
#print axioms blocks_length
#print axioms multiplicity_five
#print axioms multiplicity_one
#print axioms multiplicity_two
#print axioms multiplicity_three
#print axioms multiplicity_four
#print axioms isTDesign_one_false
#print axioms not_one_design

-- The conjecture's hypothesis holds but the conclusion fails
#print axioms hypothesis_holds
#print axioms conjecture_00000008419_false
