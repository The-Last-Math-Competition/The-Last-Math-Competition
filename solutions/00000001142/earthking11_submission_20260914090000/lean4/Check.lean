/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  EXPECTED OUTPUT: every theorem reports
      'Tlmc1142.Witt3.<name>' does not depend on any axioms

  In particular none reports `sorryAx` (a missing proof) and none reports
  `Lean.ofReduceBool` (which would appear only if the heavy 3^9 enumeration had
  been delegated to `native_decide`).

  DISCLOSURE.  The enumeration is discharged by the KERNEL `decide` tactic
  (definitional reduction), NOT by `native_decide`.  This is deliberate: our
  submission convention forbids `native_decide` because it introduces the
  `Lean.ofReduceBool` axiom.  The kernel route was made fast enough
  (~50 s, ~4.4 GB peak RSS) by coding each 3x3 matrix as a single base-3 `Nat`,
  inlining the nine structure constants, and keeping the predicate a small
  `Bool` checked only on the nine basis pairs.  See `README.md` for the
  measured `lake build` wall time.
-/

import Main

open Tlmc1142.Witt3

-- There are 3^9 = 19683 candidate matrices.
#print axioms num_mats

-- MAIN: exactly 24 of the 11232 invertible matrices preserve the bracket,
-- so |Aut(W(1;1))| = 24 at p = 3.
#print axioms aut_count_3

-- The conjecture's value p(p-1) = 3*2 = 6 is refuted.
#print axioms claim_false_3
