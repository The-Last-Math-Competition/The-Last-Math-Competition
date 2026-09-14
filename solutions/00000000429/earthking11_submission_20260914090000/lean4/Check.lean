/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem should report only core axioms (`propext`, `Quot.sound`);
  in particular none may report `sorryAx`.
-/

import Main

open Tlmc429

-- The q-binomial recursion at q = -1
#print axioms qb

-- Concrete values
#print axioms qb_6_2
#print axioms qb_8_4
#print axioms qb_7_3
#print axioms qb_10_2
#print axioms qb_2_1

-- 3 is not a signed power of two
#print axioms pow2_ne_three
#print axioms negpow2_ne_three
#print axioms six_eq_two_mul_three

-- MAIN: the conjecture fails, unsigned and signed
#print axioms not_pow2_unsigned
#print axioms not_pow2_signed
#print axioms conjecture_00000000429_false
#print axioms conjecture_00000000429_false_signed
