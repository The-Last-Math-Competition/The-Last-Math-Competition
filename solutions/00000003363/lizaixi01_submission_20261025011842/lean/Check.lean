import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if (`TLMC3363).isPrefixOf n || (n.toString.splitOn ".").contains "TLMC3363" then
      some n else none
  let required := [`TLMC3363.Parameter,
    `TLMC3363.Phase,
    `TLMC3363.quadratic,
    `TLMC3363.quadraticPolynomial,
    `TLMC3363.polynomial_eval,
    `TLMC3363.polynomial_degree_two,
    `TLMC3363.quadratic_hasDerivAt,
    `TLMC3363.quadratic_deriv,
    `TLMC3363.quadratic_second_deriv,
    `TLMC3363.unique_nondegenerate_critical,
    `TLMC3363.maps_phase,
    `TLMC3363.logistic,
    `TLMC3363.logistic_val,
    `TLMC3363.logistic_continuous,
    `TLMC3363.phase_compact,
    `TLMC3363.midpoint,
    `TLMC3363.value_at_midpoint,
    `TLMC3363.family_injective,
    `TLMC3363.local_contraction,
    `TLMC3363.iterate_nonexpanding,
    `TLMC3363.ennreal_log_nat,
    `TLMC3363.native_entropy_zero_of_nonexpanding,
    `TLMC3363.entropy,
    `TLMC3363.local_entropy_zero,
    `TLMC3363.leftParameter,
    `TLMC3363.rightParameter,
    `TLMC3363.endpoints_strict,
    `TLMC3363.parameter_interval_open,
    `TLMC3363.parameter_interval_nonempty,
    `TLMC3363.entropy_zero_on_interval,
    `TLMC3363.entropy_monotone_interval,
    `TLMC3363.entropy_antitone_interval,
    `TLMC3363.NowhereMonotone,
    `TLMC3363.printed_nowhere_monotone_false]
  unless required.all names.contains do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
