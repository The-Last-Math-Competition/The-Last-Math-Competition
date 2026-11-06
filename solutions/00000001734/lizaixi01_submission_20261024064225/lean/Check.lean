import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC1734 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC1734.group_relation_A &&
      names.contains `TLMC1734.group_relation_B &&
      names.contains `TLMC1734.all_traces_integral &&
      names.contains `TLMC1734.character_family_injective &&
      names.contains `TLMC1734.integral_characters_infinite &&
      names.contains `TLMC1734.integralTraceCurve_iff &&
      names.contains `TLMC1734.actual_integral_points_infinite do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
