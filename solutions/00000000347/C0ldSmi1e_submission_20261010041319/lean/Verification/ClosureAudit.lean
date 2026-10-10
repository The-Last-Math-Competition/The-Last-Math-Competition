import Lean

/-! Inspection only. All declarations are selected by originating module, never
by namespace. The exported graph follows constants in types, values (including
opaque values), recursor rules, and inductive mutual/constructor declarations.
`#audit_modules` enforces trust for every root; `#audit_kernel_modules` enforces
it for every kernel-safe root while still exporting all compiler runtime roots.
The Python verifier separately rejects authored unsafe source declarations.
`#inspect_modules` inventories runtime
verification/configuration code without treating it as mathematical evidence. -/

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

private def exprNames (e : Expr) : Array Name :=
  names <| e.foldConsts {} (fun n s => s.insert n)

private def bodyNames (ci : ConstantInfo) : Array Name :=
  match ci.value? true with
  | some value => exprNames value
  | none => #[]

private def ruleNames (ci : ConstantInfo) : Array Name := Id.run do
  let mut found : NameSet := {}
  if let .recInfo info := ci then
    for rule in info.rules do
      found := rule.rhs.foldConsts found (fun n s => s.insert n)
  return names found

private def inductiveNames (ci : ConstantInfo) : Array Name :=
  match ci with
  | .inductInfo info => names <| (info.ctors ++ info.all).foldl NameSet.insert {}
  | _ => #[]

private def dependencies (ci : ConstantInfo) : Array Name :=
  names <| (exprNames ci.type ++ bodyNames ci ++ ruleNames ci ++ inductiveNames ci).foldl
    NameSet.insert {}

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
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := (dependencies ci).toList ++ pending
  return names seen

private def strings (xs : Array Name) : Json := toJson (xs.map Name.toString)

private def edgeFields (ci : ConstantInfo) : List (String × Json) := [
  ("dependencies", strings (dependencies ci)),
  ("type_dependencies", strings (exprNames ci.type)),
  ("body_dependencies", strings (bodyNames ci)),
  ("recursor_dependencies", strings (ruleNames ci)),
  ("inductive_dependencies", strings (inductiveNames ci))]

private def audit (wanted : Array String) (output : String) (strict kernelOnly : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let roots := (env.constants.toList.filterMap fun (n, _) =>
    if wanted.contains (moduleName env n) then some n else none).toArray.qsort
      (fun a b => a.toString < b.toString)
  for m in wanted do
    unless env.header.moduleNames.any (fun n => n.toString == m) do
      throwError "Requested originating module is not imported: {m}"
  let mut inventory : Array Json := #[]
  let mut allNames : NameSet := {}
  let mut failures : Array String := #[]
  let mut runtimeFindings : Array String := #[]
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
    let mut rootFindings : Array String := #[]
    for a in axioms do
      if !permitted.contains a then rootFindings := rootFindings.push s!"{n}: forbidden axiom {a}"
    for u in unsafeNames do rootFindings := rootFindings.push s!"{n}: unsafe dependency {u}"
    for a in kernelAxioms do
      if !axioms.contains a then rootFindings := rootFindings.push s!"{n}: collector discrepancy {a}"
    for k in reachable do
      if (env.find? k).isNone then rootFindings := rootFindings.push s!"{n}: missing dependency {k}"
    if kernelOnly && ci.isUnsafe then
      runtimeFindings := runtimeFindings ++ rootFindings
    else
      failures := failures ++ rootFindings
    for k in reachable do allNames := allNames.insert k
    let typeText ← liftTermElabM <| withOptions (fun o =>
      o.setBool `pp.universes true |>.setBool `pp.fullNames true |>.setBool `pp.explicit true)
      do return (← ppExpr ci.type).pretty
    inventory := inventory.push <| Json.mkObj <| [
      ("name", toJson n.toString), ("module", toJson (moduleName env n)),
      ("kind", toJson (kind ci)), ("unsafe", toJson ci.isUnsafe),
      ("trust_enforced", toJson (strict && (!kernelOnly || !ci.isUnsafe))),
      ("type", toJson typeText), ("raw_type", toJson (reprStr ci.type)),
      ("closure", strings reachable), ("axioms", strings axioms),
      ("lean_collectAxioms", strings kernelAxioms), ("unsafe_dependencies", strings unsafeNames)] ++
      edgeFields ci
  let graph := (names allNames).map fun n =>
    match env.find? n with
    | some ci => Json.mkObj <| [("name", toJson n.toString), ("module", toJson (moduleName env n)),
        ("kind", toJson (kind ci)), ("unsafe", toJson ci.isUnsafe)] ++ edgeFields ci
    | none => Json.mkObj [("name", toJson n.toString), ("module", toJson "unavailable"),
        ("kind", toJson "unavailable"), ("unsafe", toJson false),
        ("dependencies", strings #[]), ("type_dependencies", strings #[]),
        ("body_dependencies", strings #[]), ("recursor_dependencies", strings #[]),
        ("inductive_dependencies", strings #[])]
  let moduleCounts := wanted.map fun m => Json.mkObj [
    ("module", toJson m),
    ("declarations", toJson <| roots.filter (fun n => moduleName env n == m) |>.size)]
  let result := Json.mkObj [
    ("requested_modules", toJson wanted), ("imported_modules", strings env.header.moduleNames),
    ("module_counts", toJson moduleCounts), ("strict_proof_check", toJson strict),
    ("kernel_roots_only", toJson kernelOnly),
    ("local_declaration_count", toJson roots.size),
    ("closure_declaration_count", toJson allNames.size),
    ("declarations", toJson inventory), ("dependency_graph", toJson graph),
    ("permitted_axioms", strings permitted), ("failures", toJson failures),
    ("compiler_runtime_findings", toJson runtimeFindings)]
  liftIO <| IO.FS.writeFile output (result.pretty ++ "\n")
  logInfo m!"Inventoried {roots.size} local declarations; {allNames.size} reachable declarations."
  if strict && !failures.isEmpty then
    throwError "Dependency audit failed: {String.intercalate "; " failures.toList}"

syntax (name := auditModules) "#audit_modules " "[" ident,* "]" str : command
syntax (name := auditKernelModules) "#audit_kernel_modules " "[" ident,* "]" str : command
syntax (name := inspectModules) "#inspect_modules " "[" ident,* "]" str : command

elab_rules : command
  | `(#audit_modules [$mods:ident,*] $output:str) =>
    audit (mods.getElems.map (fun s => s.getId.toString)) output.getString true false
  | `(#audit_kernel_modules [$mods:ident,*] $output:str) =>
    audit (mods.getElems.map (fun s => s.getId.toString)) output.getString true true
  | `(#inspect_modules [$mods:ident,*] $output:str) =>
    audit (mods.getElems.map (fun s => s.getId.toString)) output.getString false false

end Verification
