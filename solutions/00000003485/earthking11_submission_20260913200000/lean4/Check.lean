/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only `propext` (introduced through the
  standard library lemmas used by `decide` and `rw`); in particular none may
  report `sorryAx`, and none depends on Mathlib. The purely computational
  theorems `kernelMasks5_nil`, `kernelMasks5_count`, `outdeg5_le_one`,
  `girth5_ge_five`, `girth5_le_five` are expected to be axiom-free.
-/

import Main

open Tlmc3485

-- The witness C₅: out-degree and girth
#print axioms outdeg5_le_one
#print axioms outdeg5_eq_one
#print axioms girth5_ge_five
#print axioms girth5_le_five

-- The directed 5-cycle has no kernel (universal statement over the 32 subsets)
#print axioms no_kernel5
#print axioms no_kernel5_exists

-- The same fact as an explicit brute force over the 32 bitmasks
#print axioms kernelMasks5_nil
#print axioms kernelMasks5_count

-- The odd cycles C₃ and C₇
#print axioms no_kernel3
#print axioms no_kernel7

-- The refutation
#print axioms C5_in_class
#print axioms conjecture_00000003485_false
#print axioms conjecture_00000003485_refuted
