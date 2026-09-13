/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake build
      lake env lean Check.lean

  Every theorem below should report only `propext` and `Quot.sound` (introduced
  by `decide`, `rw`, and `funext`); in particular none may report `sorryAx`, and
  none depends on Mathlib.
-/

import Main

open Tlmc8234

-- The two EF1 allocations and the classification that they are the only ones
#print axioms ef1_alloc01
#print axioms ef1_alloc10
#print axioms not_ef1_alloc00
#print axioms not_ef1_alloc11
#print axioms ef1_classification
#print axioms ef1_iff_bool
#print axioms exactly_two_ef1

-- Exhaustiveness of the four allocations and fairness of the case analysis
#print axioms fin2_forall
#print axioms alloc_cases22

-- The swap graph: no edge joins two EF1 allocations
#print axioms no_adj_ef1

-- Reachability: every walk from an EF1 allocation is trivial
#print axioms reachN_eq

-- The two EF1 allocations are distinct and not connected
#print axioms alloc01_ne_alloc10
#print axioms no_path_between_diagonals
#print axioms not_ef1_connected

-- The claimed diameter bound fails
#print axioms bound_value
#print axioms claimed_diameter_bound_fails

-- The collected disproof of the first conjunct
#print axioms conjecture_00000008234_refuted
