import Main

open Tlmc1668

-- The circular-distance toolkit.
#print axioms circDist_lt
#print axioms circDist_pos
#print axioms circDist_self

-- The bridge between the computable and the propositional form of `(p,q)`.
#print axioms isPQ_iff
#print axioms proper_is_pq

-- The two finite certificates.
#print axioms gp51_has_5_2_colouring
#print axioms gp61_has_2_1_colouring
#print axioms gp61_proper
#print axioms gp61_bipartite

-- The refutation, branch by branch.
#print axioms gp61_below_3
#print axioms gp51_below_4
#print axioms branch_S3_refuted
#print axioms branch_otherwise_refuted

-- The conclusion.
#print axioms conjecture_00000001668_false
