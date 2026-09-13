/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only standard core axioms (typically
  `propext`), and in particular none may report `sorryAx` or `ofReduceBool`.
  `ofReduceBool` is what `native_decide` introduces; this project never uses
  `native_decide`.  No Mathlib is imported.
-/

import Main

open Tlmc1192

-- Prime-divisor products ∏_{p | n} p
#print axioms prodPrimeDiv_two
#print axioms prodPrimeDiv_three
#print axioms prodPrimeDiv_four
#print axioms prodPrimeDiv_six

-- The claimed leading coefficients LC(2), LC(3), LC(4), LC(6)
#print axioms lc_two
#print axioms lc_three
#print axioms lc_four
#print axioms lc_six
#print axioms lc_raw_two

-- Non-integrality of the leading coefficient
#print axioms lc2_not_integer
#print axioms lc3_not_integer
#print axioms lc4_not_integer
#print axioms no_integer_poly_has_lc_two

-- The integer-valued reading also fails
#print axioms lc2_times_two_not_integer
#print axioms lc2_degree_factorial_times_lc_not_integer
#print axioms lc3_degree_factorial_times_lc_not_integer
#print axioms lc3_degree_factorial_times_lc_not_integer_reduced

-- The collected disproof
#print axioms conjecture_00000001192_false
