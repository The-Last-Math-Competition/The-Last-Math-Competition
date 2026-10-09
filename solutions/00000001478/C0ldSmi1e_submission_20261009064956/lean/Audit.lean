import Solution
import AuthorAudit
import Lean

open Lean Elab Command

/- Verification code only: no mathematical assumptions are introduced here.
   All declarations owned by the mathematical module are inventoried, including
   private declarations and compiler execution artifacts. The exact execution
   artifact names below are bound to the frozen sources and complete inventory by
   verify.py; this is NOT a wildcard exemption based on name shape. All are
   compiler-generated execution definitions; every owned axiomInfo is rejected.
   No unsafe declaration, including these, may occur anywhere in the type/value
   dependency closure of ANY safe mathematical declaration. -/
-- No exception is assumed: the fresh frozen-candidate inventory is measured first.
private def executionArtifacts : Array Name := #[]

-- Fill only after the authoritative freeze establishes actual mathematical ownership.
private def authoredModules : Array Name := #[`NuclearNorm, `PolynomialCone, `Solution]

run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  let mut roots : Array Name := #[]
  for (name, info) in env.constants.toList.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    unless authoredModules.contains moduleName do continue
    let execution := executionArtifacts.contains name
    if info.isUnsafe && !execution then
      throwError "Unsafe authored declaration: {name}"
    if execution && !info.isUnsafe then
      throwError "Compiler execution artifact changed safety: {name}"
    if info.isAxiom then
      throwError "Authored axiom declaration: {name}"
    let axioms ← collectAxioms name
    if execution then
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound, `lcProof].contains ax do
          throwError "Forbidden compiler execution axiom {ax} in {name}"
    unless execution do
      roots := roots.push name
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Forbidden transitive axiom {ax} in {name}"
    let kind : String := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive"
    let typeText : String := (← liftTermElabM <| Meta.ppExpr info.type).pretty
    let refs := info.type.getUsedConstants ++
      ((info.value? true).map Expr.getUsedConstants |>.getD #[])
    let refs := refs.toList.eraseDups.toArray.qsort Name.lt
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson moduleName.toString),
      ("kind", toJson kind), ("unsafe", toJson info.isUnsafe),
      ("role", toJson (if execution then "compiler_execution" else "kernel_mathematics")),
      ("type", toJson typeText),
      ("transitive_axioms", toJson (axioms.qsort Name.lt |>.map Name.toString)),
      ("direct_constants", toJson (refs.map Name.toString))]
    logInfo m!"AUDITED {name}: {kind}; execution={execution}; axioms={axioms.qsort Name.lt}"
  if roots.isEmpty then throwError "No mathematical declarations found"
  -- Traverse imported intermediates as well as owned declarations. Both types
  -- and values (including theorem proof values) contribute edges.
  let mut todo := roots.toList
  let mut seen : NameSet := {}
  let mut foundations : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "Missing proof dependency: {name}"
    if info.isUnsafe then throwError "Unsafe proof dependency: {name}"
    if info.isAxiom then
      unless #[`propext, `Classical.choice, `Quot.sound].contains name do
        throwError "Forbidden proof dependency axiom: {name}"
      foundations := foundations.insert name
    let refs := info.type.getUsedConstants ++
      ((info.value? true).map Expr.getUsedConstants |>.getD #[])
    todo := refs.toList ++ todo
  let closure := Json.mkObj [
    ("root_names", toJson (roots.qsort Name.lt |>.map Name.toString)),
    ("reachable_constant_names", toJson (seen.toList.toArray.qsort Name.lt |>.map Name.toString)),
    ("reachable_constant_count", toJson seen.size),
    ("unsafe_count", toJson (0 : Nat)),
    ("axioms", toJson (foundations.toList.toArray.qsort Name.lt |>.map Name.toString)),
    ("edge_sources", toJson #["types", "values_including_theorem_proofs"])]
  liftIO <| IO.FS.createDirAll "logs"
  liftIO <| IO.FS.writeFile "logs/proof-dependency-closure.json" (Json.pretty closure ++ "\n")
  liftIO <| IO.FS.writeFile "logs/declarations.json" (Json.pretty (Json.arr rows) ++ "\n")
  logInfo m!"PASS: inventoried {rows.size} owned declarations; checked all {roots.size} safe mathematical roots and {seen.size} reachable constants, with no unsafe dependency"
