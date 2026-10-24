import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC2101 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC2101.complete_counterexample &&
      names.contains `TLMC2101.rational_no_sqrt_five &&
      names.contains `TLMC2101.rational_no_quadratic_root &&
      names.contains `TLMC2101.quadratic_degree &&
      names.contains `TLMC2101.conjugation &&
      names.contains `TLMC2101.realEmbedding &&
      names.contains `TLMC2101.realEmbedding_range &&
      names.contains `TLMC2101.quadraticFieldEquivalence &&
      names.contains `TLMC2101.nativeNorm_eq_quadraticNorm &&
      names.contains `TLMC2101.nativeNorm_conjugation_product &&
      names.contains `TLMC2101.goldenElement_norm &&
      names.contains `TLMC2101.actual_real_field_golden_norm &&
      names.contains `TLMC2101.actual_complex_field_golden_norm &&
      names.contains `TLMC2101.no_square_goldenElement &&
      names.contains `TLMC2101.explicitValue_sq &&
      names.contains `TLMC2101.real_square_root_branches &&
      names.contains `TLMC2101.complexEmbedding_range &&
      names.contains `TLMC2101.no_embedded_square_root &&
      names.contains `TLMC2101.complex_square_root_branches &&
      names.contains `TLMC2101.no_unit_square_root &&
      names.contains `TLMC2101.pointwise_claims_impossible do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
