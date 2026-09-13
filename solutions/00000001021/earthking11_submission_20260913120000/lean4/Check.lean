/-
  Axiom audit for the disproof of conjecture 00000001021.

  Run from the `lean4` directory with:

      export PATH="/opt/homebrew/bin:$PATH"
      lake env lean Check.lean

  Every theorem below should print `'Tlmc1021.<name>' does not depend on any
  axioms`.  In particular no `sorryAx` and no `Lean.ofReduceBool` (which
  `native_decide` would introduce) may appear.
-/

import Main

open Tlmc1021

#print axioms layer_sizes
#print axioms layer_sum
#print axioms treeSize_five
#print axioms too_small
#print axioms treeSize_mono
#print axioms treeSizeFull_five
#print axioms conjecture_00000001021_false
