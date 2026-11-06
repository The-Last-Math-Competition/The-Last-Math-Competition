import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC79 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC79.explicit_counterexample_both_countings &&
      names.contains `TLMC79.not_universal_printed_rule &&
      names.contains `TLMC79.first_digit_cylinder &&
      names.contains `TLMC79.nthPrime_prime &&
      names.contains `TLMC79.counts_le_length &&
      names.contains `TLMC79.no_sequence_satisfies_printed_sliding_rule do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
