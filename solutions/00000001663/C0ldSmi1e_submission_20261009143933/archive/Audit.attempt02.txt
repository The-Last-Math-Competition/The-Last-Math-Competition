import Verification
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ownedModule := fun (n : Name) =>
    n == `Conjecture1663 || n == `Verification || (`Conjecture1663).isPrefixOf n
  let moduleOf := fun (n : Name) =>
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let all := env.constants.toList
  let mut roots : Array Name := #[]
  for (n, _) in all do
    if ownedModule (moduleOf n) then
      roots := roots.push n
  if roots.size < 35 then throwError "Too few owned declarations: {roots.size}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for n in roots do
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless allowed.contains ax do
        throwError "Forbidden axiom {ax} in owned declaration {n}"
    IO.println s!"OWNED\t{n}\t{moduleOf n}\t{axs}"
  for n in env.header.moduleNames do
    IO.println s!"MODULE\t{n}"
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut visited := 0
  let mut axioms : NameSet := {}
  for _ in [:1000000] do
    if pending.isEmpty then break
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    visited := visited + 1
    let some ci := env.find? n | throwError "Missing declaration {n}"
    if ci.isUnsafe then throwError "Unsafe dependency {n}"
    match ci with
    | .defnInfo d =>
      unless d.safety == .safe do throwError "Non-safe definition dependency {n}"
    | .axiomInfo _ =>
      axioms := axioms.insert n
      unless allowed.contains n do throwError "Forbidden reachable axiom {n}"
    | _ => pure ()
    let kind := match ci with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient primitive"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let body := ci.value?
    IO.println s!"REACHABLE\t{n}\t{moduleOf n}\t{kind}\tbody={body.isSome}"
    let deps := ci.type.foldConsts ({} : NameSet) (fun dep acc => acc.insert dep)
    let deps := match body with
      | some value => value.foldConsts deps (fun dep acc => acc.insert dep)
      | none => deps
    for dep in deps do
      if !(seen.contains dep) then pending := pending.push dep
  unless pending.isEmpty do throwError "Dependency traversal fuel exhausted"
  IO.println s!"AUDIT_OK\towned={roots.size}\treachable={visited}\taxioms={axioms.toList}"
