import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC39 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC39.not_eventually_representable &&
      names.contains `TLMC39.arbitrarily_large_counterexamples &&
      names.contains `TLMC39.no_two_powers &&
      names.contains `TLMC39.no_distinct_powers &&
      names.contains `TLMC39.no_one_power &&
      names.contains `TLMC39.bad_mod &&
      names.contains `TLMC39.cover720 do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
