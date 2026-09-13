/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below must report only axioms from core Lean (typically only
  `propext`); in particular none may report `sorryAx`, and none depends on
  Mathlib.  If `sorryAx` appears anywhere, the disproof is not formalised.
-/

import Main

open Tlmc418

-- Enumeration of the 8 words of length 3 over {1,2}
#print axioms allWords3_length

-- Prefix condition and the two Yamanouchi words of weight (2,1)
#print axioms word_112_isYam
#print axioms word_121_isYam
#print axioms word_211_not_yam
#print axioms yamWords21_eq
#print axioms card_yamWords21
#print axioms numYam21_eq

-- Standard tableaux of shape (2,1) and their lattice reading words
#print axioms card_syts21
#print axioms latticeReading_syt21a
#print axioms latticeReading_syt21b
#print axioms latticeReadings21_eq
#print axioms yam_eq_latticeReadings
#print axioms every_yam_is_latticeReading
#print axioms numLattice21_A_eq

-- Reading (B): entry reading words are permutations of weight (1,1,1)
#print axioms entryReading_syt21a
#print axioms entryReading_syt21b
#print axioms entryReading_weight_111
#print axioms numLattice21_B_eq

-- Hook lengths, f^(2,1), n!, K_(2,1),(2,1)
#print axioms hookProduct21_eq
#print axioms fact3_eq
#print axioms f21_eq
#print axioms f21_eq_card_syts21
#print axioms ssyt21_21_eq
#print axioms K21_eq

-- The numeric contradiction
#print axioms claimNum_eq
#print axioms claimDen_eq
#print axioms propNumA_eq
#print axioms propDenA_eq
#print axioms propNumB_eq
#print axioms propDenB_eq
#print axioms proportionA_is_one
#print axioms claim_not_one
#print axioms proportionA_ne_claim
#print axioms cross_values
#print axioms twelve_ne_four
#print axioms proportionB_ne_claim

-- The asserted maximum 1/2^{n-1}
#print axioms quarter_lt_one
#print axioms proportionA_exceeds_max

-- The "maximisers are rectangles" clause
#print axioms f3_eq
#print axioms f111_eq
#print axioms nonrectangle_beats_rectangles
#print axioms rectangle_not_max
#print axioms max_claim_wrong_for_formula

-- The collected refutation
#print axioms conjecture_00000000418_refuted
