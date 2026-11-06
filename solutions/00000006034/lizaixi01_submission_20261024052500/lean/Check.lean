import Main

set_option linter.auxLemma false

-- Audit the actual imported namespace, including every generated declaration.
run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC6034 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC6034.counterexample &&
      names.contains `TLMC6034.isotropy_type_card &&
      names.contains `TLMC6034.coadjoint_orbit_card &&
      names.contains `TLMC6034.moment_map_identity &&
      names.contains `TLMC6034.area_closed &&
      names.contains `TLMC6034.action_pullback_area do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
