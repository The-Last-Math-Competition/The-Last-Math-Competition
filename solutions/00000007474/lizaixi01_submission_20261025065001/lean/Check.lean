import Main
set_option linter.auxLemma false
run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if (`TLMC7474).isPrefixOf n || (n.toString.splitOn ".").contains "TLMC7474" then some n else none
  let required := [`TLMC7474.Param,
    `TLMC7474.Poly3,
    `TLMC7474.Poly2,
    `TLMC7474.Operator,
    `TLMC7474.parameterSum,
    `TLMC7474.linearPolynomial,
    `TLMC7474.quadraticPolynomial,
    `TLMC7474.pencil,
    `TLMC7474.parameterSpectrum,
    `TLMC7474.pencil_apply,
    `TLMC7474.polynomial_evaluation,
    `TLMC7474.pencil_polynomial,
    `TLMC7474.pencil_selfAdjoint,
    `TLMC7474.pencil_continuous,
    `TLMC7474.scalar_operator_isUnit_iff,
    `TLMC7474.mem_parameterSpectrum_iff,
    `TLMC7474.parameterSpectrum_eq_plane,
    `TLMC7474.zero_mem_parameterSpectrum,
    `TLMC7474.pencil_at_basis,
    `TLMC7474.basis_not_mem_parameterSpectrum,
    `TLMC7474.linearPolynomial_ne_zero,
    `TLMC7474.quadraticPolynomial_ne_zero,
    `TLMC7474.quadraticPolynomial_homogeneous,
    `TLMC7474.quadraticPolynomial_degree,
    `TLMC7474.chart,
    `TLMC7474.chart_mem,
    `TLMC7474.spectralChart,
    `TLMC7474.chart_recover,
    `TLMC7474.projection,
    `TLMC7474.inclusion,
    `TLMC7474.projection_inclusion,
    `TLMC7474.projection_surjective,
    `TLMC7474.eval_projection,
    `TLMC7474.restriction,
    `TLMC7474.vanishingIdeal,
    `TLMC7474.CoordinateRing,
    `TLMC7474.mem_vanishingIdeal_iff,
    `TLMC7474.vanishingIdeal_eq_projection_ker,
    `TLMC7474.coordinateEquiv,
    `TLMC7474.coordinateRing_dimension,
    `TLMC7474.coordinateRing_not_dimension_one,
    `TLMC7474.affine_parameter_spectrum_counterexample]
  unless required.all names.contains do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
