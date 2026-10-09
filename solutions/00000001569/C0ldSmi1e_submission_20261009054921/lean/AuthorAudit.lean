import Solution

/-! Inspection only. The mathematical argument is entirely in Solution.lean. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (`Conjecture1569).isPrefixOf name then
      logInfo m!"Compiled declaration: {name}"

#print axioms Conjecture1569.Plane
#print axioms Conjecture1569.UniformQuadraticLowerBound
#print axioms Conjecture1569.angleSet
#print axioms Conjecture1569.angleSet.eq_1
#print axioms Conjecture1569.arbitrarily_large_counterexamples
#print axioms Conjecture1569.axisPoint
#print axioms Conjecture1569.axisPoint._proof_1
#print axioms Conjecture1569.axisPoint.eq_1
#print axioms Conjecture1569.axisPoint_injective
#print axioms Conjecture1569.axis_collinear
#print axioms Conjecture1569.configuration
#print axioms Conjecture1569.configuration.eq_1
#print axioms Conjecture1569.configuration_angleSet_card_le
#print axioms Conjecture1569.configuration_angleSet_card_le._proof_2
#print axioms Conjecture1569.configuration_angleSet_subset
#print axioms Conjecture1569.configuration_angle_zero_or_pi
#print axioms Conjecture1569.configuration_angle_zero_or_pi._proof_2
#print axioms Conjecture1569.configuration_angle_zero_or_pi._proof_3
#print axioms Conjecture1569.configuration_card
#print axioms Conjecture1569.configuration_mem_axis
#print axioms Conjecture1569.mem_angleSet_iff
#print axioms Conjecture1569.mem_angleSet_iff._proof_1
#print axioms Conjecture1569.mem_angleSet_iff._proof_2
#print axioms Conjecture1569.mem_angleSet_iff._proof_3
#print axioms Conjecture1569.not_uniformQuadraticLowerBound
#print axioms Conjecture1569.original_conjunction_false

#check Conjecture1569.mem_angleSet_iff
#check Conjecture1569.configuration_card
#check Conjecture1569.configuration_angleSet_card_le
#check Conjecture1569.arbitrarily_large_counterexamples
#check Conjecture1569.not_uniformQuadraticLowerBound
#check Conjecture1569.original_conjunction_false
