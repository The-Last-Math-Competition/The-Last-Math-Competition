import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC553 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC553.complete_counterexample &&
      names.contains `TLMC553.simpleClassEquiv &&
      names.contains `TLMC553.indecomposable_iff_simple &&
      names.contains `TLMC553.ext_vanishing_iff_splitting &&
      names.contains `TLMC553.standardEndFieldEquiv &&
      names.contains `TLMC553.extExchange_zero &&
      names.contains `TLMC553.sequenceClassMap_injective &&
      names.contains `TLMC553.positiveCharacterEquiv &&
      names.contains `TLMC553.mutation_is_formula14 &&
      names.contains `TLMC553.adjacent_charts_glue_by_formula14 &&
      names.contains `TLMC553.every_chart_bijective &&
      names.contains `TLMC553.infiniteGlobalFamily_injective do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
