import Bergman930
import Lean

open Lean Elab Command

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def allowedAxiom (n : Name) : Bool :=
  [``propext, ``Classical.choice, ``Quot.sound].contains n

/-- Reviewer-only traversal of every reachable constant's type and available body. -/
def auditClosure (roots : Array Name) : CoreM Unit := do
  let env ← getEnv
  let mut todo := roots
  let mut visited : NameSet := {}
  let mut axiomNames : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | throwError "AUDIT FAIL missing constant {n}"
    if ci.isUnsafe then throwError "AUDIT FAIL unsafe constant {n}"
    if ci.isPartial then throwError "AUDIT FAIL partial constant {n}"
    if n == ``sorryAx || n.toString.startsWith "Lean.ofReduceBool" then
      throwError "AUDIT FAIL forbidden constant {n}"
    match ci with
    | .axiomInfo _ =>
      axiomNames := axiomNames.push n
      unless allowedAxiom n do throwError "AUDIT FAIL forbidden axiom {n}"
    | _ => pure ()
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? true then todo := todo ++ v.getUsedConstants
  logInfo m!"AUDIT PASS rootCount={roots.size} reachableCount={visited.toList.length} axioms={axiomNames} unsafe=0 partial=0 missing=0"

elab "audit_names " "[" ns:ident,* "]" : command => do
  let names ← ns.getElems.mapM (fun n => liftCoreM <| realizeGlobalConstNoOverloadWithInfo n)
  liftCoreM <| auditClosure names

elab "audit_fixed_signature " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let some ci := (← getEnv).find? name | throwError "Missing signature"
  unless ci.levelParams.isEmpty do throwError "Universe parameters present: {ci.levelParams}"
  if ci.type.isForall then throwError "Extra top-level binders found in {name}"
  logInfo m!"FIXED SIGNATURE {name} : {ci.type}; universeParameters=[]; topLevelBinders=0"

audit_names [Bergman930.l2Space_isClosed]
audit_names [Bergman930.not_continuum]
audit_names [Bergman930.disk,
  Bergman930.area,
  Bergman930.disk_open,
  Bergman930.disk_measurable,
  Bergman930.zero_mem_disk,
  Bergman930.space,
  Bergman930.A2,
  Bergman930.holomorphic,
  Bergman930.square_integrable,
  Bergman930.zero_off_disk,
  Bergman930.ext,
  Bergman930.zero_apply,
  Bergman930.add_apply,
  Bergman930.sub_apply,
  Bergman930.smul_apply,
  Bergman930.one,
  Bergman930.one_apply,
  Bergman930.one_ne_zero,
  Bergman930.shift,
  Bergman930.shift_apply,
  Bergman930.dslope_memLp,
  Bergman930.dividedDifference,
  Bergman930.dividedDifference_apply,
  Bergman930.division_identity,
  Bergman930.commuting_map_apply,
  Bergman930.commuting_idempotent_eq_zero_or_id,
  Bergman930.Invariant,
  Bergman930.invariant_complemented_eq_bot_or_top,
  Bergman930.uniformCauchy_on_smaller_disk,
  Bergman930.exists_pointwise_limit,
  Bergman930.l2Space_isClosed,
  Bergman930.areaConstant,
  Bergman930.integral_norm_le,
  Bergman930.evaluation_bound,
  Bergman930.toL2,
  Bergman930.toL2_injective,
  Bergman930.l2Space,
  Bergman930.functionEquivL2,
  Bergman930.l2Shift,
  Bergman930.inner_toL2,
  Bergman930.circle_mean,
  Bergman930.circle_mean_symmetric,
  Bergman930.polar_eq_circle,
  Bergman930.integral_ball_polar,
  Bergman930.disk_mean_zero,
  Bergman930.disk_mean,
  Bergman930.shift_norm_le,
  Bergman930.l2Shift_norm_le,
  Bergman930.bergmanShift,
  Bergman930.IsReducing,
  Bergman930.isReducing_iff_adjoint,
  Bergman930.reducing_eq_bot_or_top,
  Bergman930.reducing_bot,
  Bergman930.reducing_top,
  Bergman930.ReducingSubspace,
  Bergman930.reducingFromBool,
  Bergman930.reducingFromBool_bijective,
  Bergman930.reducing_cardinality,
  Bergman930.not_continuum]
audit_fixed_signature Bergman930.l2Space_isClosed
audit_fixed_signature Bergman930.reducing_cardinality
audit_fixed_signature Bergman930.not_continuum

#print axioms Bergman930.l2Space_isClosed
#print axioms Bergman930.l2Space_complete
#print axioms Bergman930.isReducing_iff_adjoint
#print axioms Bergman930.reducing_eq_bot_or_top
#print axioms Bergman930.reducing_cardinality
#print axioms Bergman930.not_continuum
#check @Bergman930.reducing_eq_bot_or_top
#check @Bergman930.isReducing_iff_adjoint
#print Bergman930.disk
#print Bergman930.area
#print Bergman930.space
#print Bergman930.l2Space
#print Bergman930.bergmanShift
#print Bergman930.IsReducing
#print Bergman930.ReducingSubspace

example : IsClosed (Bergman930.l2Space : Set (MeasureTheory.Lp ℂ 2 Bergman930.area)) :=
  Bergman930.l2Space_isClosed
example : Cardinal.mk Bergman930.ReducingSubspace = 2 := Bergman930.reducing_cardinality
example : Cardinal.mk Bergman930.ReducingSubspace ≠ Cardinal.continuum := Bergman930.not_continuum
