import Lean

/-! Independent compiled-environment audit. This is an inspection tool, not part
of the mathematical proof. It inventories declarations by originating module,
then follows every constant in types, bodies (including opaque bodies), recursor
rules, and inductive constructor declarations. Its output records every edge. -/

open Lean Elab Command Meta

namespace Verification

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def names (s : NameSet) : Array Name :=
  s.toList.toArray.qsort (fun a b => a.toString < b.toString)

private def dependencies (ci : ConstantInfo) : Array Name := Id.run do
  let mut found : NameSet := ci.type.foldConsts {} (fun n s => s.insert n)
  if let some value := ci.value? true then
    found := value.foldConsts found (fun n s => s.insert n)
  match ci with
  | .recInfo info =>
    for rule in info.rules do
      found := rule.rhs.foldConsts found (fun n s => s.insert n)
  | .inductInfo info =>
    for n in info.ctors ++ info.all do found := found.insert n
  | _ => pure ()
  return names found

private def moduleName (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx]!.toString
  | none => env.header.mainModule.toString

private def closure (env : Environment) (roots : Array Name) :
    Except String (Array Name) := do
  let mut seen : NameSet := {}
  let mut pending := roots.toList
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !seen.contains n then
      let some ci := env.find? n | throw s!"Missing constant {n}"
      if ci.isUnsafe then throw s!"unsafe dependency {n}"
      seen := seen.insert n
      pending := (dependencies ci).toList ++ pending
  return names seen

private def strings (xs : Array Name) : Json := toJson (xs.map Name.toString)

syntax (name := auditModules) "#audit_modules " "[" ident,* "]" str : command

elab_rules : command
  | `(#audit_modules [$mods:ident,*] $output:str) => do
    let env ← getEnv
    let wanted := mods.getElems.map (fun s => s.getId.toString)
    let roots := (env.constants.toList.filterMap fun (n, _) =>
      if wanted.contains (moduleName env n) then some n else none).toArray.qsort
        (fun a b => a.toString < b.toString)
    if roots.isEmpty then throwError "No declarations in requested modules"
    let mut inventory : Array Json := #[]
    let mut allNames : NameSet := {}
    let mut failures : Array String := #[]
    let permitted := #[`propext, `Classical.choice, `Quot.sound]
    for n in roots do
      let some ci := env.find? n | throwError "Missing local declaration {n}"
      let reachable ← match closure env #[n] with
        | .ok xs => pure xs
        | .error msg => throwError msg
      let axioms := reachable.filter fun k => match env.find? k with
        | some (.axiomInfo _) => true
        | _ => false
      let unsafeNames := reachable.filter fun k => (env.find? k).any ConstantInfo.isUnsafe
      let kernelAxioms ← liftCoreM <| collectAxioms n
      for a in axioms do
        if !permitted.contains a then failures := failures.push s!"{n}: forbidden axiom {a}"
      for u in unsafeNames do failures := failures.push s!"{n}: unsafe dependency {u}"
      for a in kernelAxioms do
        if !axioms.contains a then failures := failures.push s!"{n}: collector discrepancy {a}"
      for k in reachable do allNames := allNames.insert k
      let typeText ← liftTermElabM <| withOptions (fun o =>
        o.setBool `pp.universes true |>.setBool `pp.fullNames true |>.setBool `pp.explicit true)
        do return (← ppExpr ci.type).pretty
      inventory := inventory.push <| Json.mkObj [
        ("name", toJson n.toString), ("module", toJson (moduleName env n)),
        ("kind", toJson (kind ci)), ("unsafe", toJson ci.isUnsafe),
        ("type", toJson typeText), ("raw_type", toJson (reprStr ci.type)),
        ("dependencies", strings (dependencies ci)),
        ("closure", strings reachable), ("axioms", strings axioms),
        ("lean_collectAxioms", strings kernelAxioms), ("unsafe_dependencies", strings unsafeNames)]
    let graph := (names allNames).map fun n =>
      let ci := (env.find? n).get!
      Json.mkObj [("name", toJson n.toString), ("module", toJson (moduleName env n)),
        ("kind", toJson (kind ci)), ("unsafe", toJson ci.isUnsafe),
        ("dependencies", strings (dependencies ci))]
    let result := Json.mkObj [
      ("requested_modules", toJson wanted), ("imported_modules", strings env.header.moduleNames),
      ("local_declaration_count", toJson roots.size),
      ("closure_declaration_count", toJson allNames.size),
      ("declarations", toJson inventory), ("dependency_graph", toJson graph),
      ("permitted_axioms", strings permitted), ("failures", toJson failures)]
    liftIO <| IO.FS.writeFile output.getString (result.pretty ++ "\n")
    logInfo m!"Audited {roots.size} local declarations; {allNames.size} reachable declarations."
    unless failures.isEmpty do
      throwError "Dependency audit failed: {String.intercalate "; " failures.toList}"

end Verification
