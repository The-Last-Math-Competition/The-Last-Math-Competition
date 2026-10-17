import Main
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let ns := env.constants.fold (init := #[]) fun acc n _ =>
    if (`TLMC8207).isPrefixOf n then acc.push n else acc
  let names := ns.qsort Name.lt
  for n in names do
    let ci := env.find? n |>.get!
    if ci.isUnsafe then throwError "Unsafe declaration: {n}"
    if ci.isAxiom then throwError "Custom axiom: {n}"
    match ci with
    | .opaqueInfo _ => throwError "Opaque declaration: {n}"
    | _ => pure ()
    let axs ← collectAxioms n
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
    logInfo m!"{n}: {axs}"
  logInfo m!"PASS: all {names.size} namespace declarations audited; no unsafe, custom axioms, opaque declarations or unexpected axiom dependencies."
