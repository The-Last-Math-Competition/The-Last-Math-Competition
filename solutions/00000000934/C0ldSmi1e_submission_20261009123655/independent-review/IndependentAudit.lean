import Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true

#print Conjecture934.Circle
#print Conjecture934.μ
#print Conjecture934.L1
#print Conjecture934.L2
#print Conjecture934.conjecture
#print Conjecture934.strengthened_conjecture
#print Conjecture934.inclusionLinear_exists
#print Conjecture934.inclusionLinear
#print Conjecture934.inclusionLinear_apply
#print Conjecture934.inclusion_exists
#print Conjecture934.inclusion
#print Conjecture934.inclusion_apply
#print Conjecture934.inclusion_norm_le
#print MeasureTheory.Lp
#print MeasureTheory.AEEqFun
#print AddCircle
#print AddCircle.haarAddCircle
#print HasSum
#print Summable

run_cmd do
  let env ← getEnv
  let owned := (env.constants.toList.filterMap fun (n, _) =>
    match env.getModuleIdxFor? n with
    | some idx => if env.header.moduleNames[idx.toNat]! == `Solution then some n else none
    | none => none).toArray.qsort Name.lt
  unless owned.size == 36 do
    throwError "Unexpected source-owned inventory size {owned.size}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending := owned
  let mut visited : NameSet := {}
  let mut axiomNames : NameSet := {}
  for n in owned do
    let ci ← getConstInfo n
    if ci.isUnsafe then throwError "Unsafe source-owned constant {n}"
    if let .axiomInfo _ := ci then throwError "Source-owned axiom {n}"
    let axioms ← Lean.collectAxioms n
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected collected axiom {ax} for {n}"
    logInfo m!"INDEPENDENT_OWNED {n}\nACTUAL_TYPE {ci.type}\nACTUAL_BODY {ci.value? (allowOpaque := true)}\nAXIOMS {axioms}"
  while pending.size > 0 do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    let ci ← getConstInfo n
    if ci.isUnsafe then throwError "Unsafe closure member {n}"
    match ci with
    | .axiomInfo _ =>
      axiomNames := axiomNames.insert n
      unless allowed.contains n do throwError "Unexpected closure axiom {n}"
    | _ => pure ()
    pending := pending ++ ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  let closure := visited.toArray.qsort Name.lt
  let axiomInventory := axiomNames.toArray.qsort Name.lt
  liftIO <| IO.FS.writeFile "../review-logs/independent-transitive-constants.txt"
    (String.intercalate "\n" (closure.toList.map Name.toString) ++ "\n")
  liftIO <| IO.FS.writeFile "../review-logs/independent-owned-constants.txt"
    (String.intercalate "\n" (owned.toList.map Name.toString) ++ "\n")
  logInfo m!"INDEPENDENT_PASS owned={owned.size} transitive={closure.size} axioms={axiomInventory}"
