/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake build
      lake env lean Check.lean

  Every theorem below should report either no axioms at all or only core axioms
  (`propext`, `Quot.sound`, `Classical.choice`).  In particular none may report
  `sorryAx`, and none depends on Mathlib.
-/

import Main

open Tlmc1682

-- The graph model and the triangle predicate
#print axioms gp11_triangleFreeCheck
#print axioms gp11_triangle_free
#print axioms gp11_no_triangle
#print axioms gp11_triangle_count
#print axioms gp6_triangle_count
#print axioms gp12_triangle_count

-- Cycles and pancyclicity
#print axioms pancyclic_gp11_gives_3cycle
#print axioms list_length_three
#print axioms has3cycle_gp11_gives_triangle
#print axioms gp11_no_3cycle
#print axioms gp11_not_pancyclic

-- The packaged refutation of conjecture 00000001682
#print axioms conjecture_00000001682_false
