import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC567 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC567.complete_counterexample &&
      names.contains `TLMC567.representationEquivalence &&
      names.contains `TLMC567.envelopeEquivalence &&
      names.contains `TLMC567.explicitImageIso &&
      names.contains `TLMC567.envelope_ext_vanishes &&
      names.contains `TLMC567.realizationBiproduct &&
      names.contains `TLMC567.retractOfDimensionLE &&
      names.contains `TLMC567.retract_dimension_le &&
      names.contains `TLMC567.clusterTilting_iff_nonzero &&
      names.contains `TLMC567.maximalRigid_iff_nonzero &&
      names.contains `TLMC567.indecomposable_iff_dimension_one &&
      names.contains `TLMC567.basic_iff_dimension_le_one &&
      names.contains `TLMC567.allClass_injective &&
      names.contains `TLMC567.basic_class_count &&
      names.contains `TLMC567.a1Roots &&
      names.contains `TLMC567.a1Base &&
      names.contains `TLMC567.simpleIndex &&
      names.contains `TLMC567.rootBasis_is_simple &&
      names.contains `TLMC567.coxeter_number_eq_two &&
      names.contains `TLMC567.coxeter_eigenspace_full &&
      names.contains `TLMC567.coxeter_exponents_eq &&
      names.contains `TLMC567.basic_count_not_predicted do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
