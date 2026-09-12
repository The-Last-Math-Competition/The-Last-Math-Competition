import Main

open Tlmc1072

-- Values of G at the counterexample points
#eval G 2 1 2   -- expected: 6
#eval G 2 1 3   -- expected: 12
#eval G 3 1 2   -- expected: 28
#eval 2 ^ 1 - 1 -- expected: 1
#eval 2 ^ 2 - 1 -- expected: 3
#eval 3 ^ 2 - 1 -- expected: 8

-- Axiom audit: each theorem must print
-- "'...' does not depend on any axioms"
#print axioms Tlmc1072.G212
#print axioms Tlmc1072.G213
#print axioms Tlmc1072.G312
#print axioms Tlmc1072.q21
#print axioms Tlmc1072.q22
#print axioms Tlmc1072.refute_I
#print axioms Tlmc1072.refute_II
