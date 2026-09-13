/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only `propext` (and possibly `Quot.sound`,
  introduced through the standard library lemmas used by `decide`); in
  particular none may report `sorryAx`, and none depends on Mathlib.
-/

import Main

open Tlmc3955

-- GF(2) rank: sanity checks on small matrices
#print axioms rankGF2_zero
#print axioms rankGF2_one
#print axioms rankGF2_all_ones
#print axioms rankGF2_two
#print axioms rankGF2_rectangle

-- The cut matrix of a bipartition of K4
#print axioms cutMat_eq

-- All sixteen labelled cuts, and the seven bipartitions
#print axioms cutRank_table
#print axioms cutRank_max
#print axioms cutRank_complement
#print axioms all_nontrivial_cuts_rank_one
#print axioms seven_rep_1
#print axioms seven_rep_2
#print axioms seven_rep_4
#print axioms seven_rep_8
#print axioms seven_rep_3
#print axioms seven_rep_5
#print axioms seven_rep_9
#print axioms seven_bipartitions_cut_rank_one

-- Rank-width value used for K4
#print axioms rankWidthK4_eq_one

-- Treewidth: orderings, explicit decomposition, computed value
#print axioms allOrders_length
#print axioms elimWidth_K4_order
#print axioms treewidth_K4
#print axioms deg_K4_three

-- Minimum-degree lower bound
#print axioms min_degree_le_of_treewidthLe
#print axioms not_deg_K4_le_two
#print axioms not_treewidthLe_K4_two
#print axioms treewidthLe_K4_three

-- The disproof
#print axioms inequality_fails_for_K4
#print axioms three_gt_three_times_one_minus_one
#print axioms conjecture_00000003955_false
