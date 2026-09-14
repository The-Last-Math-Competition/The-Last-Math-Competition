/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem should report only core axioms (`propext`, `Quot.sound`);
  in particular none may report `sorryAx` or `Lean.ofReduceBool`
  (the latter is added by `native_decide`, which is deliberately NOT used).
-/

import Main

open Tlmc1067

-- Translation machinery (`decide` on Fin 19)
#print axioms add_inj
#print axioms add_inj_raw
#print axioms step
#print axioms sub_self
#print axioms sub_pos
#print axioms sub_lt

-- Translation invariance of the Sidon property
#print axioms sidon_translate

-- The decidable core with one element fixed to 0
#print axioms no_sidon5_zero

-- MAIN: there is no strong Sidon 5-set in F_19
#print axioms no_sidon5

-- The explicit strong Sidon 4-set {0,1,3,7}
#print axioms sidon4_witness

-- The counting obstruction 5*4 > 19-1 and the ceiling sqrt(19) = 5
#print axioms count_obstruction
#print axioms ceil_sqrt19

-- The packaged statement that refutes conjecture 00000001067
#print axioms conjecture_00000001067_false
