/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem should report only core axioms (`propext`, `Quot.sound`,
  possibly `Classical.choice`); in particular none may report `sorryAx`.
-/

import Main

open Tlmc2308

-- The multiplication table and inverses
#print axioms inv_left

-- The two generators and the closure checks
#print axioms genClosure_subset
#print axioms generators_generate

-- Cardinality and trivial center
#print axioms card_S3
#print axioms center_trivial

-- The inner automorphisms
#print axioms inn_injective
#print axioms card_inn
#print axioms inn_le_aut

-- The generator-based enumeration of endomorphisms / automorphisms
#print axioms card_hom
#print axioms card_aut
#print axioms aut_eq_inn

-- Solvability: A_3 abelian and normal of index 2
#print axioms A3_abelian
#print axioms A3_normal
#print axioms A3_index2

-- The semidirect-product decomposition S_3 = A_3 ⋊ T2
#print axioms A3_inter_T2
#print axioms A3T2_eq_S3
#print axioms tau_order_two
#print axioms sigma_order_three
#print axioms solvable_S3

-- The order bound and the collected refutation
#print axioms six_lt_6144
#print axioms conjecture_00000002308_false
