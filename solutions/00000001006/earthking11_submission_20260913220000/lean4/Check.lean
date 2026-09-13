/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report no axioms at all (all finite facts are
  closed by `decide`, which produces axiom-free proofs), and in particular none
  may report `sorryAx`.  No Mathlib is imported.
-/

import Main

open Tlmc1006

-- The point set, the line set, and completeness of the explicit lines
#print axioms pointsE_length
#print axioms pointsE_eq
#print axioms lines15_is_all_lines
#print axioms allLinesE_length
#print axioms lines15_size
#print axioms linesP_shape

-- The encoding round-trips
#print axioms enc_mk_range
#print axioms mk_enc_points

-- The explicit ovoid O
#print axioms O_card
#print axioms O_map_enc
#print axioms O_is_ovoid

-- The complement O^c is a 2-ovoid
#print axioms Ocomp_card
#print axioms Ocomp_map_enc
#print axioms Ocomp_is_2ovoid
#print axioms O_and_Ocomp_partition

-- The divisibility failure and the packaged disproof
#print axioms two_not_dvd_three
#print axioms two_ovoid_exists
#print axioms conjecture_00000001006_false
