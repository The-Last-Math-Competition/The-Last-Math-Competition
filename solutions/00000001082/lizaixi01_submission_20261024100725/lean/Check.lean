import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC1082 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC1082.complete_counterexample &&
      names.contains `TLMC1082.extension_degree &&
      names.contains `TLMC1082.extension_card &&
      names.contains `TLMC1082.coordinateSpan &&
      names.contains `TLMC1082.rankWeight_zero_iff &&
      names.contains `TLMC1082.full_minimumDistance &&
      names.contains `TLMC1082.full_distance_attained &&
      names.contains `TLMC1082.code_card_formula &&
      names.contains `TLMC1082.full_isMRD &&
      names.contains `TLMC1082.code_eq_top &&
      names.contains `TLMC1082.RankEquivalent &&
      names.contains `TLMC1082.rankEquivalent_refl &&
      names.contains `TLMC1082.rankEquivalent_symm &&
      names.contains `TLMC1082.rankEquivalent_trans &&
      names.contains `TLMC1082.classCount_one &&
      names.contains `TLMC1082.actual_parameters &&
      names.contains `TLMC1082.arbitrarily_large_prime_failure &&
      names.contains `TLMC1082.relativeError_not_bigO &&
      names.contains `TLMC1082.printed_asymptotic_false do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
