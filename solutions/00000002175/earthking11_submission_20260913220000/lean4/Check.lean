/-
  Axiom audit for the formalisation in `Main.lean`.

  Build / run with:

      lake build
      lake env lean Check.lean

  Every theorem below should report only core axioms (`propext`, `Quot.sound`,
  and possibly `Classical.choice`); in particular none may report `sorryAx`, and
  none depends on Mathlib.
-/

import Main

open Tlmc2175

-- The four members and the family are the expected ones.
#print axioms F_eq
#print axioms witness_members_pairwise_distinct

-- The explicit four-triple intersection check: every triple meets in size 1.
#print axioms triple_123
#print axioms triple_124
#print axioms triple_134
#print axioms triple_234
#print axioms witness_all_triples_meet_in_one

-- The family is 3-wise odd-intersecting (and the Boolean checker accepts it).
#print axioms witness_oddTriples
#print axioms witness_check

-- The witness has four members and breaks the claimed bound 2^{4-3} = 2.
#print axioms witness_length
#print axioms claimed_bound_n4
#print axioms witness_breaks_bound
#print axioms witness_refutes_size_claim

-- The true maximum at n = 4 is at least 5 > 2 = 2^{4-3}.
#print axioms G5_oddTriples
#print axioms G5_check
#print axioms G5_length
#print axioms true_max_n4_exceeds_claim
#print axioms n4_max_at_least_five
