import Main

-- Frozen audit intentionally includes generated declarations.
set_option linter.auxLemma false

#print axioms TLMC2704.Q5
#print axioms TLMC2704.arbitrarily_small_nonconvergent_orbit
#print axioms TLMC2704.arbitrarily_small_nonconvergent_orbit._simp_1_1
#print axioms TLMC2704.arbitrarily_small_nonzero
#print axioms TLMC2704.counterexample
#print axioms TLMC2704.even_cofinal
#print axioms TLMC2704.even_cofinal._proof_1_1
#print axioms TLMC2704.f
#print axioms TLMC2704.f_apply
#print axioms TLMC2704.forwardLinear
#print axioms TLMC2704.forwardLinear._proof_1
#print axioms TLMC2704.forward_deriv
#print axioms TLMC2704.forward_deriv_nonzero
#print axioms TLMC2704.forward_hasStrictDerivAt
#print axioms TLMC2704.g
#print axioms TLMC2704.g_apply
#print axioms TLMC2704.inverseHomeomorph
#print axioms TLMC2704.inverseHomeomorph._proof_1
#print axioms TLMC2704.inverseHomeomorph._proof_2
#print axioms TLMC2704.inverseLinear
#print axioms TLMC2704.inverseSeries
#print axioms TLMC2704.inverseSeries_radius
#print axioms TLMC2704.inverse_analytic
#print axioms TLMC2704.inverse_series_represents
#print axioms TLMC2704.iterate_even
#print axioms TLMC2704.iterate_norm
#print axioms TLMC2704.iterate_odd
#print axioms TLMC2704.left_inverse
#print axioms TLMC2704.multiplier_norm
#print axioms TLMC2704.no_iterate_limit
#print axioms TLMC2704.odd_cofinal
#print axioms TLMC2704.odd_cofinal._proof_1_1
#print axioms TLMC2704.prime_five
#print axioms TLMC2704.right_inverse

run_cmd do
  let expected : List String := ["TLMC2704.Q5", "TLMC2704.arbitrarily_small_nonconvergent_orbit", "TLMC2704.arbitrarily_small_nonconvergent_orbit._simp_1_1", "TLMC2704.arbitrarily_small_nonzero", "TLMC2704.counterexample", "TLMC2704.even_cofinal", "TLMC2704.even_cofinal._proof_1_1", "TLMC2704.f", "TLMC2704.f_apply", "TLMC2704.forwardLinear", "TLMC2704.forwardLinear._proof_1", "TLMC2704.forward_deriv", "TLMC2704.forward_deriv_nonzero", "TLMC2704.forward_hasStrictDerivAt", "TLMC2704.g", "TLMC2704.g_apply", "TLMC2704.inverseHomeomorph", "TLMC2704.inverseHomeomorph._proof_1", "TLMC2704.inverseHomeomorph._proof_2", "TLMC2704.inverseLinear", "TLMC2704.inverseSeries", "TLMC2704.inverseSeries_radius", "TLMC2704.inverse_analytic", "TLMC2704.inverse_series_represents", "TLMC2704.iterate_even", "TLMC2704.iterate_norm", "TLMC2704.iterate_odd", "TLMC2704.left_inverse", "TLMC2704.multiplier_norm", "TLMC2704.no_iterate_limit", "TLMC2704.odd_cofinal", "TLMC2704.odd_cofinal._proof_1_1", "TLMC2704.prime_five", "TLMC2704.right_inverse"]
  let actual := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC2704 |>.isPrefixOf n then some n.toString else none
  unless actual.all expected.contains && expected.all actual.contains do
    throwError "namespace coverage mismatch: {actual}"
  for n in actual do
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {actual.length}"
