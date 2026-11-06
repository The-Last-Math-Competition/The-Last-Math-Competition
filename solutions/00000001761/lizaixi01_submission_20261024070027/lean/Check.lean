import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC1761 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC1761.printed_counterexample &&
      names.contains `TLMC1761.specht_group_algebra_not_semisimple &&
      names.contains `TLMC1761.shape_weight_one &&
      names.contains `TLMC1761.threeCore_eq_empty &&
      names.contains `TLMC1761.polytabloid_column_antisymmetrizer &&
      names.contains `TLMC1761.columnGroup_iff_all_columns &&
      names.contains `TLMC1761.rowEquivalent_iff_all_rows &&
      names.contains `TLMC1761.all_tableaux_represented &&
      names.contains `TLMC1761.spechtAugmentationEquiv_intertwines do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
