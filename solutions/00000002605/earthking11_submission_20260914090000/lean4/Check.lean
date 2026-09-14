/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem must report only core axioms (and, for the `decide`-checked
  Boolean computations, in fact *no* axioms at all).  In particular none may
  report `sorryAx`, and none may depend on Mathlib (there is no Mathlib here).
-/

import Main

open Tlmc2605

-- Order relation derived from the covers
#print axioms le_refl
#print axioms le_antisymm
#print axioms le_trans
#print axioms le_decomp
#print axioms cover_derived_eq

-- Lattice axioms: meet is a GLB, join is a LUB
#print axioms meet_is_glb
#print axioms join_is_lub

-- Rank function derived as longest-chain length
#print axioms rank_zero
#print axioms rank_cov
#print axioms rank_mono

-- Whitney numbers of the second kind
#print axioms W_zero
#print axioms W_one
#print axioms W_two
#print axioms W_three
#print axioms W_four

-- Failure of log-concavity
#print axioms logConcavity_fails
#print axioms strictLogConcavity_fails

-- The class membership facts
#print axioms upperSemimodular_true
#print axioms distributive_true

-- Not geometric (not atomistic)
#print axioms atoms_eq
#print axioms joinAtoms_eq
#print axioms not_atomistic

-- MAIN
#print axioms conjecture_00000002605_false
