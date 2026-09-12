/-
  Verification of the refutation of conjecture 00000005400.

  Builds on Main.lean and (1) re-checks the complete enumerations, (2) lists
  the refuting theorems, (3) prints the axiom audit for every theorem — all
  must be axiom-free.

  Run with:  lake env lean Check.lean
-/
import Main

open Tlmc5400

-- 1. the enumeration of S₄: all 256 image vectors, 24 bijections
#eval allVecs.length                    -- 256
#eval permVecs.length                   -- 24
#eval permVecs                          -- the 24 permutations of the 4-point set

-- permAt indexes exactly this enumeration (kernel-checked certificate)
#check permAtTable_eq
#print axioms permAtTable_eq

-- 2. Identity I: orbit profile determines periodic point count
#check count_from_profile_sum
#check profile_det_count

-- sample profiles over all 256 self-maps: 11 distinct, each with one count
#eval (((List.finRange 256).map (fun w => orbitProfile (ofW w))).foldr
  (fun a acc => if acc.contains a then acc else a :: acc) []).length
#eval (List.finRange 256).filter
  (fun w => periodicCount (ofW w) != (orbitProfile (ofW w)).sum)  -- []

-- 3. Identity II: conjugation preserves pointwise periods
#check conj_preserves_period

-- 4. the concrete pair f = (0 1)(2 3), τ = (1 2 3), g = τ f τ⁻¹
#eval (List.finRange 4).map gEx         -- image vector of (0 2)(1 3)
#eval pairTable                         -- [(2,2), (2,2), (2,2), (2,2)]
#check pairTable_all_two

-- 5. the refutation: no conjugate pair separates the periods
#eval conjWitnessExists                 -- false
#check conjWitnessExists_false
#check refute

-- 6. axiom audit: every theorem must be axiom-free
#print axioms allVecs_length
#print axioms permVecs_length
#print axioms permVecs_bij
#print axioms permAtTable_eq
#print axioms count_from_profile_sum
#print axioms profile_det_count
#print axioms conj_preserves_period
#print axioms conjWitnessExists_false
#print axioms pairTable_all_two
#print axioms refute
