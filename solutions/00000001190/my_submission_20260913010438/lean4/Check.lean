import Main

open Tlmc1190

-- The three machine-checked counts
#eval (matrices.filter isGl).length                                  -- expect 2016
#eval (matrices.filter (fun m => isGl m && isOrder2 m)).length       -- expect 57
#eval (matrices.filter (fun m => isGl m && isOrder3 m)).length       -- expect 170

-- The formula side
#eval theta2                                                         -- expect 49

-- Axiom audit: every line must print "'... ' does not depend on any axioms"
#print axioms count_gl2
#print axioms count_order2
#print axioms count_order3
#print axioms formula2
#print axioms refute
#print axioms refute_counts
