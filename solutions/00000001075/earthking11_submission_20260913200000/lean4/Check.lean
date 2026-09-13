/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only `propext`; in particular none may
  report `sorryAx`, and none uses `Lean.ofReduceBool` (which `native_decide`
  would introduce).  All proofs are closed by `decide`/`rw`, so the audit is
  the machine-checkable statement that the disproof uses no unproved step.
-/

import Main

open Tlmc1075

-- The witness is an equality configuration: #supp(f) + #supp(f_hat) = 6
#print axioms witness_supp
#print axioms witness_fhat_supp
#print axioms witness_equality

-- The explicit transform values: f_hat(xi) = 1 - omega^xi
#print axioms witness_fhat_values

-- No time-frequency translate of an affine function is the witness
#print axioms not_tfTrans_affine
#print axioms not_tfTrans_affine_dft

-- The collected disproof
#print axioms conjecture_00000001075_refuted
