/-
  Axiom audit for the rule-3 disproof of conjecture 00000000277.

  Expected: every theorem depends only on the standard core axioms (for these
  purely computational `decide` proofs, none at all), and in particular NOT on
  `sorryAx` or `Lean.ofReduceBool` (`ofReduceBool`).
-/
import Main

open Tlmc277

#print axioms r2_1
#print axioms r2_5
#print axioms r2_25
#print axioms r2_125
#print axioms multiplicity_exceeds_six
#print axioms trace_constraint_of_order_thirtytwo
#print axioms conjecture_00000000277_false
