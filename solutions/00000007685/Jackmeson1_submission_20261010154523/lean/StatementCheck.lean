import Conjecture7685
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Conjecture7685.Statement
    | throwError "STATEMENT_FAIL: module Conjecture7685.Statement is not imported by Conjecture7685"
  let claims := env.const2ModIdx.fold (init := #[]) fun acc n i =>
    match n with
    | .str _ "Claim" => if i == idx then acc.push n else acc
    | _ => acc
  if claims.size != 1 then
    throwError m!"STATEMENT_FAIL: expected exactly one `Claim` in Conjecture7685.Statement, found {claims}"
  let claim := claims[0]!
  unless (← isDefEq (← inferType (mkConst claim)) (mkSort Level.zero)) do
    throwError m!"STATEMENT_FAIL: {claim} is not a Prop"
  let mut ok := false
  for t in [`C7685.main] do
    if (← isDefEq (← getConstInfo t).type (mkConst claim)) then
      IO.println s!"CLAIM_OK {t} : {claim}"
      ok := true
  unless ok do throwError m!"STATEMENT_FAIL: no main theorem has type {claim}"
