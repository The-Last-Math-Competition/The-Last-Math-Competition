/-
  Axiom audit for the rule-3 disproof of conjecture 00000000938.

  Expected: each theorem depends only on the standard core axioms
  `propext` and `Quot.sound` (plus possibly `Classical.choice`), and in
  particular NOT on `sorryAx` or `Lean.ofReduceBool` (`ofReduceBool`).
-/
import Main

open Tlmc938

#print axioms max_abs_eq
#print axioms T_isometry
#print axioms maps_diamond_to_square
#print axioms one_sq_ne_two_nat
#print axioms one_sq_ne_two_int
#print axioms conjecture_00000000938_false
