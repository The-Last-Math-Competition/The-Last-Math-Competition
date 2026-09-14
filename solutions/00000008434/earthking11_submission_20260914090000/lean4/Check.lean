/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem should report only core axioms (`propext`, `Quot.sound`,
  possibly `Classical.choice`); in particular none may report `sorryAx`.
-/

import Main

open Tlmc8434

-- Concrete data: the 14 blocks, their sizes, distinctness
#print axioms blocks_length
#print axioms blocks_size_four
#print axioms blocks_distinct

-- The 3-(8,4,1) property: 56 triples, each in exactly one block
#print axioms triples_length
#print axioms each_triple_in_one_block
#print axioms ag32_is_3_8_4_1

-- The spectrum: 91 pairs, only values 0 and 2
#print axioms spectrum_length
#print axioms spectrum_values
#print axioms spec_count_zero
#print axioms spec_count_one
#print axioms spec_count_two
#print axioms s0_eq
#print axioms s1_eq
#print axioms one_absent

-- MAIN: the interval [s0,s1] is not fully covered -> clause 1 is false
#print axioms intervalFull_false
#print axioms interval_missing_value
#print axioms intervalSpectrum_false
#print axioms conjecture_first_clause_false

-- The second clause fails for 1-designs (Pasch)
#print axioms pasch_length
#print axioms pasch_block_size
#print axioms pasch_spectrum_length
#print axioms pasch_spectrum_all_one
#print axioms pasch_s0_eq_s1
#print axioms pasch_is_1_design
#print axioms pasch_not_symmetric
#print axioms second_clause_fails
