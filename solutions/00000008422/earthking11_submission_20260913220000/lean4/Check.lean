/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only core axioms (`propext`, `Quot.sound`,
  possibly `Classical.choice`); in particular none may report `sorryAx` and
  none depends on Mathlib or on `Lean.ofReduceBool` (we use `decide`, not
  `native_decide`).
-/

import Main

open Tlmc8422

-- Cardinalities of the point-pair / block enumeration
#print axioms triples_len
#print axioms pairs_len

-- Existence: explicit 2-(6,3,2) and 2-(6,3,4) designs
#print axioms design2_is
#print axioms design2_len
#print axioms design4_is
#print axioms design4_len

-- Non-existence: no 2-(6,3,1) and no 2-(6,3,3) design
#print axioms no_design_1
#print axioms no_design_3
#print axioms spectrum_6_3

-- The criterion's predicted sets and the forced-out values
#print axioms criterion_6_3
#print axioms criterion_22_3
#print axioms forced_out_6_3
#print axioms budget_6_3
#print axioms forced_out_22_3
#print axioms budget_22_3

-- The arithmetic kernel of the divisibility argument
#print axioms parity_6_3
#print axioms parity_22_3
#print axioms no_odd_lambda_22_3

-- The decisive (22,3) package
#print axioms decisive_22_3
