import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC92 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC92.complete_counterexample &&
      names.contains `TLMC92.carlitzAction_injective &&
      names.contains `TLMC92.full_action_agreement &&
      names.contains `TLMC92.torsion_membership &&
      names.contains `TLMC92.rootToTorsion_injective &&
      names.contains `TLMC92.extCarlitz_rank &&
      names.contains `TLMC92.divisionPoints_card &&
      names.contains `TLMC92.generic_characteristic do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
