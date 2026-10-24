import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC1537 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC1537.complete_counterexample &&
      names.contains `TLMC1537.quotientDualEquiv &&
      names.contains `TLMC1537.normalizedTensorDualEquiv &&
      names.contains `TLMC1537.hochschild_preserves_normalized &&
      names.contains `TLMC1537.hochschild_full_formula &&
      names.contains `TLMC1537.connes_full_formula &&
      names.contains `TLMC1537.connes_is_signed_rotation_norm &&
      names.contains `TLMC1537.cyclicCochainComplex &&
      names.contains `TLMC1537.HC0_no_add_two_torsion &&
      names.contains `TLMC1537.torsionHC2_nonzero &&
      names.contains `TLMC1537.sourceHochschild_full_formula &&
      names.contains `TLMC1537.sourceConnes_full_formula &&
      names.contains `TLMC1537.sourceCyclicCochainComplex &&
      names.contains `TLMC1537.source_no_degree_two_group_isomorphism do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
