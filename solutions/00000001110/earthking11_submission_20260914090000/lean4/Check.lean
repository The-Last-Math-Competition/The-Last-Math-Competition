/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:

      lake env lean Check.lean

  The submission standard is to avoid `Lean.ofReduceBool` (which would be
  introduced by `native_decide`, because that axiom trusts the compiler).
  Every theorem below is closed either by the kernel `decide` or by a short
  proof term, so the expected footprint is at most `propext`, `Quot.sound`
  and `Classical.choice`, and in particular contains neither `sorryAx` nor
  `Lean.ofReduceBool`.  No theorem in this file uses `native_decide`.
-/

import Main

open Tlmc1110

-- The custom factorial
#print axioms fact_five
#print axioms fact_fifteen

-- The staircase hook lengths and their product
#print axioms hooks5_length
#print axioms hookProd5_closed
#print axioms hookProd5_value

-- The hook-length evaluation of #Red(w0) in S_6
#print axioms reducedWordsW0S6_eq
#print axioms reducedWordsW0S6_factorisation

-- The two primes above h = 6 that divide the count
#print axioms eleven_dvd
#print axioms thirteen_dvd
#print axioms six_lt_eleven
#print axioms six_lt_thirteen

-- The refutation
#print axioms not_six_smooth
#print axioms two_primes_above_h
#print axioms conjecture_00000001110_false
