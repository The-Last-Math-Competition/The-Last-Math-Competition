import Main

-- Frozen audit intentionally includes generated declarations.
set_option linter.auxLemma false

#print axioms TLMC2689.IsPreperiodic
#print axioms TLMC2689.canonicalHeight
#print axioms TLMC2689.canonicalHeight_eq
#print axioms TLMC2689.canonicalHeight_two
#print axioms TLMC2689.canonicalHeight_two_pos
#print axioms TLMC2689.canonical_height_limit
#print axioms TLMC2689.counterexample
#print axioms TLMC2689.f
#print axioms TLMC2689.f.eq_1
#print axioms TLMC2689.fPolynomial
#print axioms TLMC2689.fPolynomial.eq_1
#print axioms TLMC2689.forwardOrbit
#print axioms TLMC2689.geometric_sum_two
#print axioms TLMC2689.iterate_eq
#print axioms TLMC2689.log_height_iterate
#print axioms TLMC2689.log_height_two
#print axioms TLMC2689.log_height_two_iterate
#print axioms TLMC2689.meanHeight
#print axioms TLMC2689.meanHeight_eq
#print axioms TLMC2689.meanHeight_le_multiplicative
#print axioms TLMC2689.meanHeight_lower
#print axioms TLMC2689.meanHeight_no_finite_limit
#print axioms TLMC2689.meanHeight_tendsto_atTop
#print axioms TLMC2689.meanHeight_tendsto_atTop._proof_1_1
#print axioms TLMC2689.meanMultiplicativeHeight
#print axioms TLMC2689.meanMultiplicativeHeight_no_finite_limit
#print axioms TLMC2689.meanMultiplicativeHeight_tendsto_atTop
#print axioms TLMC2689.mul_height_two
#print axioms TLMC2689.mul_height_two_iterate
#print axioms TLMC2689.normalizedHeight
#print axioms TLMC2689.normalizedHeight._proof_1
#print axioms TLMC2689.normalizedHeight.eq_1
#print axioms TLMC2689.normalizedHeight_eq
#print axioms TLMC2689.normalizedHeight_eq._simp_1_2
#print axioms TLMC2689.normalizedHeight_eq._simp_1_3
#print axioms TLMC2689.normalizedHeight_eq._simp_1_4
#print axioms TLMC2689.normalizedHeight_eq._simp_1_5
#print axioms TLMC2689.normalizedHeight_eq._simp_1_6
#print axioms TLMC2689.normalizedHeight_eq._simp_1_7
#print axioms TLMC2689.normalizedHeight_eq._simp_1_8
#print axioms TLMC2689.orbit_two_strictMono
#print axioms TLMC2689.polynomial_degree
#print axioms TLMC2689.polynomial_evaluates
#print axioms TLMC2689.pow_two_ge_linear
#print axioms TLMC2689.sum_linear
#print axioms TLMC2689.two_not_preperiodic

run_cmd do
  let expected : List String := ["TLMC2689.IsPreperiodic", "TLMC2689.canonicalHeight", "TLMC2689.canonicalHeight_eq", "TLMC2689.canonicalHeight_two", "TLMC2689.canonicalHeight_two_pos", "TLMC2689.canonical_height_limit", "TLMC2689.counterexample", "TLMC2689.f", "TLMC2689.f.eq_1", "TLMC2689.fPolynomial", "TLMC2689.fPolynomial.eq_1", "TLMC2689.forwardOrbit", "TLMC2689.geometric_sum_two", "TLMC2689.iterate_eq", "TLMC2689.log_height_iterate", "TLMC2689.log_height_two", "TLMC2689.log_height_two_iterate", "TLMC2689.meanHeight", "TLMC2689.meanHeight_eq", "TLMC2689.meanHeight_le_multiplicative", "TLMC2689.meanHeight_lower", "TLMC2689.meanHeight_no_finite_limit", "TLMC2689.meanHeight_tendsto_atTop", "TLMC2689.meanHeight_tendsto_atTop._proof_1_1", "TLMC2689.meanMultiplicativeHeight", "TLMC2689.meanMultiplicativeHeight_no_finite_limit", "TLMC2689.meanMultiplicativeHeight_tendsto_atTop", "TLMC2689.mul_height_two", "TLMC2689.mul_height_two_iterate", "TLMC2689.normalizedHeight", "TLMC2689.normalizedHeight._proof_1", "TLMC2689.normalizedHeight.eq_1", "TLMC2689.normalizedHeight_eq", "TLMC2689.normalizedHeight_eq._simp_1_2", "TLMC2689.normalizedHeight_eq._simp_1_3", "TLMC2689.normalizedHeight_eq._simp_1_4", "TLMC2689.normalizedHeight_eq._simp_1_5", "TLMC2689.normalizedHeight_eq._simp_1_6", "TLMC2689.normalizedHeight_eq._simp_1_7", "TLMC2689.normalizedHeight_eq._simp_1_8", "TLMC2689.orbit_two_strictMono", "TLMC2689.polynomial_degree", "TLMC2689.polynomial_evaluates", "TLMC2689.pow_two_ge_linear", "TLMC2689.sum_linear", "TLMC2689.two_not_preperiodic"]
  let actual := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC2689 |>.isPrefixOf n then some n.toString else none
  unless actual.all expected.contains && expected.all actual.contains do
    throwError "namespace coverage mismatch: {actual}"
  for n in actual do
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {actual.length}"
