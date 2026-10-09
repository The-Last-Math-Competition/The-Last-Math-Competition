import Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

-- This command inspects every declaration whose defining module is Solution,
-- including automatically generated declarations. collectAxioms traverses each
-- declaration's dependencies, rather than checking only its direct references.
run_cmd do
  let env ← getEnv
  let mut owned : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if env.header.moduleNames[idx.toNat]! == `Solution then
        owned := owned.push n
  owned := owned.qsort Name.lt
  if owned.isEmpty then throwError "No owned declarations found"
  for n in owned do
    let info ← getConstInfo n
    if info.isUnsafe then throwError "Unsafe owned declaration: {n}"
    if let .axiomInfo _ := info then throwError "Owned axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Disallowed transitive axiom {ax} in {n}"
    logInfo m!"OWNED {n}\nTYPE {info.type}\nAXIOMS {axs}"
  -- Independently walk all constants in types and bodies of the owned declarations.
  -- This includes library constants and generated proof/equation helper bodies.
  let mut pending := owned
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let info ← getConstInfo n
    if info.isUnsafe then throwError "Unsafe transitive declaration: {n}"
    if let .axiomInfo _ := info then
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Disallowed axiom in explicit transitive closure: {n}"
    for dep in info.type.getUsedConstants do
      pending := pending.push dep
    if let some body := info.value? (allowOpaque := true) then
      for dep in body.getUsedConstants do
        pending := pending.push dep
  let closure := seen.toArray.qsort Name.lt
  liftIO <| IO.FS.writeFile "logs/transitive-constants.txt"
    (String.intercalate "\n" (closure.toList.map Name.toString) ++ "\n")
  logInfo m!"PASS: inspected {owned.size} owned declarations, including generated helpers"
  logInfo m!"PASS: {closure.size} transitive declarations have no unsafe constant and only propext/Classical.choice/Quot.sound axioms"
  logInfo m!"PASS: every owned declaration also passed Lean.collectAxioms independently"
