/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only core axioms (`propext` and possibly
  `Classical.choice`); in particular none may report `sorryAx`, and none
  depends on Mathlib (`import Std` only).
-/

import Main

open Tlmc1260

-- The closed form agrees with the substitution on a prefix
#print axioms tm_prefix_agrees

-- p(3) ≥ 6, the six factors, and p(3) = 6
#print axioms tm_p3_ge_6
#print axioms tm_six_factors
#print axioms tm_p3_eq_6

-- The bound p(n) ≤ n + 2 fails at n = 3
#print axioms tm_refutes_bound

-- The substitution is primitive: its incidence matrix is positive
#print axioms incidence_positive

-- The packaged refutation
#print axioms conjecture_00000001260_false
