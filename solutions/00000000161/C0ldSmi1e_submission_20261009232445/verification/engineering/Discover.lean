import Conjecture161
import Lean

open Lean Elab Command

set_option maxRecDepth 100000
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let mut authored : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if m == `Conjecture161 || m == `Conjecture161.Arithmetic then
        logInfo m!"AUTHORED_DECL {n} MODULE {m}"
        if !n.toString.endsWith "._cstage1" && !n.toString.endsWith "._cstage2" then
          authored := authored.push n
        else
          logInfo m!"COMPILER_RUNTIME_ONLY {n}"
  let mut pending := authored
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      let some ci := env.find? n | throwError "Missing dependency {n}"
      let mut deps := ci.type.getUsedConstants
      match ci with
      | .defnInfo v =>
        deps := deps ++ v.value.getUsedConstants
        logInfo m!"DECL_KIND {n} def {repr v.safety}"
      | .thmInfo v =>
        deps := deps ++ v.value.getUsedConstants
        logInfo m!"DECL_KIND {n} theorem"
      | .opaqueInfo v =>
        deps := deps ++ v.value.getUsedConstants
        logInfo m!"DECL_KIND {n} opaque unsafe={v.isUnsafe}"
      | .axiomInfo v => logInfo m!"CLOSURE_AXIOM {n} unsafe={v.isUnsafe}"
      | _ => pure ()
      logInfo m!"CLOSURE_EDGE {n} => {deps.toList}"
      pending := pending ++ deps
  logInfo m!"CLOSURE_COUNT {seen.size}"
