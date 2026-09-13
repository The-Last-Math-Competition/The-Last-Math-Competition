/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report at most `propext` (coming from the standard
  library lemmas used by `decide`/`rw`/`omega`); in particular none may report
  `sorryAx` or `Lean.ofReduceBool`, and none depends on Mathlib.
-/

import Main

open Tlmc226

-- Periodicity modulo 3 (period 6)
#print axioms two_pow_mod_three_period6
#print axioms mul_two_pow_mod6
#print axioms cullen_period6
#print axioms woodall_period6

-- The two equivalences
#print axioms cullen_div3_iff
#print axioms woodall_div3_iff
#print axioms W_mod3_eq_add_two
#print axioms woodall_W_div3_iff

-- Oddness: least prime factor 3 means divisible by 3
#print axioms cullen_odd
#print axioms woodall_odd

-- The residue table
#print axioms residue_table

-- The proportions do not sum to 1
#print axioms proportions_sum
#print axioms two_thirds_ne_one
#print axioms four_ne_six

-- The collected disproof
#print axioms conjecture_00000000226_false
