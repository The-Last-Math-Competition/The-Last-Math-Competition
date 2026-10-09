import Audit
import Lean.Util.CollectAxioms

/- Independent inspection of all declarations owned by submitted modules.
   Ownership rather than namespace selection includes private/generated constants. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut solutionCount := 0
  let mut auditCount := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    if owner == `Solution || owner == `Audit then
      if owner == `Solution then solutionCount := solutionCount + 1
      else auditCount := auditCount + 1
      let axioms ← Lean.collectAxioms name
      logInfo m!"OWNED {owner} :: {name} :: AXIOMS {axioms}"
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Disallowed axiom {ax} in {name}"
      match info with
      | .axiomInfo _ => throwError "Submitted axiom declaration {name}"
      | _ => pure ()
      if info.isUnsafe then throwError "Unsafe submitted declaration {name}"
  if solutionCount == 0 then throwError "No Solution declarations were inspected"
  logInfo m!"OWNER_TOTAL Solution={solutionCount} Audit={auditCount}"

#print Conjecture1569.Plane
#print Conjecture1569.angleSet
#print Conjecture1569.axisPoint
#print Conjecture1569.configuration
#print Conjecture1569.UniformQuadraticLowerBound
#print axioms Conjecture1569.configuration_angle_zero_or_pi
#print axioms Conjecture1569.arbitrarily_large_counterexamples
#print axioms Conjecture1569.not_uniformQuadraticLowerBound
#print axioms Conjecture1569.original_conjunction_false
#check EuclideanGeometry.angle
#check EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi
#check Conjecture1569.mem_angleSet_iff
#check Conjecture1569.configuration_card
#check Conjecture1569.configuration_angleSet_card_le
#check Conjecture1569.arbitrarily_large_counterexamples
#check Conjecture1569.not_uniformQuadraticLowerBound
#check Conjecture1569.original_conjunction_false

-- Independently written endpoints spell out the exact uniform proposition
-- and its fully quantified strict violation in the standard Euclidean plane.
example : ¬ (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = n →
      (n : ℝ)^2 - C * (n : ℝ) ≤ ((Conjecture1569.angleSet S).card : ℝ)) :=
  Conjecture1569.not_uniformQuadraticLowerBound

example (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = n ∧
      ((Conjecture1569.angleSet S).card : ℝ) < (n : ℝ)^2 - C*(n : ℝ) :=
  Conjecture1569.arbitrarily_large_counterexamples C N
