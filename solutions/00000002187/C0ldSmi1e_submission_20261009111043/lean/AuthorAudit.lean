import Conjecture2187
import Lean.Util.CollectAxioms

/-!
This audit checks every declaration originating in the mathematical module,
including generated and private declarations. It rejects unsafe/partial
definitions, owned axioms, and any transitive axiom other than the three
standard logical axioms. It introduces no mathematical assumption.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    if env.header.moduleNames[idx.toNat]! != `Conjecture2187 then continue
    count := count + 1
    let safe : Bool := match info with
      | .axiomInfo _ => false
      | .defnInfo d => d.safety == .safe
      | .opaqueInfo d => !d.isUnsafe
      | .ctorInfo d => !d.isUnsafe
      | .recInfo d => !d.isUnsafe
      | .inductInfo d => !d.isUnsafe
      | .thmInfo _ => true
      | .quotInfo _ => false
    unless safe do throwError "Unsafe, partial, or axiomatic owned declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} used by {name}"
    logInfo m!"AUDITED {name}; safe; axioms = {axioms}"
  unless count > 0 do throwError "No owned declarations found"
  logInfo m!"PASS: {count} owned declarations checked."

#print Conjecture2187.Contains
#print Conjecture2187.Attainable
#print Conjecture2187.minimumEdges
#print Conjecture2187.ClaimedAsymptotic
#check Conjecture2187.minimumEdges_attained
#check Conjecture2187.minimumEdges_le
#check Conjecture2187.minimumEdges_eq
#check Conjecture2187.pathMinimum_eq
#check Conjecture2187.pathMinimum_succ
#check Conjecture2187.pathMinimum_ratio_tendsto_one
#check Conjecture2187.pathMinimum_ratio_not_tendsto_three
#check Conjecture2187.conjecture_false

#print axioms Conjecture2187.minimumEdges_eq
#print axioms Conjecture2187.pathMinimum_eq
#print axioms Conjecture2187.pathMinimum_ratio_tendsto_one
#print axioms Conjecture2187.pathMinimum_ratio_not_tendsto_three
#print axioms Conjecture2187.conjecture_false
