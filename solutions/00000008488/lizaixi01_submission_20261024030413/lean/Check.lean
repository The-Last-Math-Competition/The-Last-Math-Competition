import Main

-- Frozen audit intentionally includes generated declarations.
set_option linter.auxLemma false

#print axioms TLMC8488.Stream
#print axioms TLMC8488.X
#print axioms TLMC8488.actual_coverMincard
#print axioms TLMC8488.actual_coverMincard_finite
#print axioms TLMC8488.centers
#print axioms TLMC8488.centers.eq_1
#print axioms TLMC8488.centers_card
#print axioms TLMC8488.centers_cover
#print axioms TLMC8488.centers_cover._proof_1_1
#print axioms TLMC8488.centers_cover_one
#print axioms TLMC8488.centers_net_one
#print axioms TLMC8488.compactX
#print axioms TLMC8488.counterexample
#print axioms TLMC8488.cylinderRel
#print axioms TLMC8488.dyn_prefix_one
#print axioms TLMC8488.dyn_prefix_one._proof_1_1
#print axioms TLMC8488.dyn_prefix_one._proof_1_2
#print axioms TLMC8488.ennreal_log_nat
#print axioms TLMC8488.finiteTimeValue
#print axioms TLMC8488.finiteTimeValue.eq_1
#print axioms TLMC8488.finiteTimeValue_eq
#print axioms TLMC8488.finiteTimeValue_tendsto
#print axioms TLMC8488.log_linear_tendsto
#print axioms TLMC8488.native_topological_entropy_zero
#print axioms TLMC8488.no_harmonic_bound
#print axioms TLMC8488.nonemptyX
#print axioms TLMC8488.prefix_cofinal
#print axioms TLMC8488.prefix_comp
#print axioms TLMC8488.prefix_entropy_zero
#print axioms TLMC8488.prefix_entropy_zero._proof_1_1
#print axioms TLMC8488.prefix_entropy_zero._proof_1_2
#print axioms TLMC8488.prefix_iff_dist
#print axioms TLMC8488.prefix_refl
#print axioms TLMC8488.prefix_representative
#print axioms TLMC8488.prefix_symm
#print axioms TLMC8488.prefix_uniformity
#print axioms TLMC8488.representative
#print axioms TLMC8488.representative.eq_1
#print axioms TLMC8488.representative.eq_2
#print axioms TLMC8488.representative.match_1
#print axioms TLMC8488.representative_injective
#print axioms TLMC8488.representative_prefix_injective
#print axioms TLMC8488.shift
#print axioms TLMC8488.shift._proof_1
#print axioms TLMC8488.shift._proof_2
#print axioms TLMC8488.shift.eq_1
#print axioms TLMC8488.shift_continuous
#print axioms TLMC8488.shift_iterate_apply
#print axioms TLMC8488.spike
#print axioms TLMC8488.spike._proof_1
#print axioms TLMC8488.spike.eq_1
#print axioms TLMC8488.streamMetric
#print axioms TLMC8488.streamMetric._proof_1
#print axioms TLMC8488.uniqueOne
#print axioms TLMC8488.uniqueOne.eq_1
#print axioms TLMC8488.uniqueOne_closed
#print axioms TLMC8488.zero
#print axioms TLMC8488.zero._proof_1
#print axioms TLMC8488.zero.eq_1

run_cmd do
  let expected : List String := ["TLMC8488.Stream", "TLMC8488.X", "TLMC8488.actual_coverMincard", "TLMC8488.actual_coverMincard_finite", "TLMC8488.centers", "TLMC8488.centers.eq_1", "TLMC8488.centers_card", "TLMC8488.centers_cover", "TLMC8488.centers_cover._proof_1_1", "TLMC8488.centers_cover_one", "TLMC8488.centers_net_one", "TLMC8488.compactX", "TLMC8488.counterexample", "TLMC8488.cylinderRel", "TLMC8488.dyn_prefix_one", "TLMC8488.dyn_prefix_one._proof_1_1", "TLMC8488.dyn_prefix_one._proof_1_2", "TLMC8488.ennreal_log_nat", "TLMC8488.finiteTimeValue", "TLMC8488.finiteTimeValue.eq_1", "TLMC8488.finiteTimeValue_eq", "TLMC8488.finiteTimeValue_tendsto", "TLMC8488.log_linear_tendsto", "TLMC8488.native_topological_entropy_zero", "TLMC8488.no_harmonic_bound", "TLMC8488.nonemptyX", "TLMC8488.prefix_cofinal", "TLMC8488.prefix_comp", "TLMC8488.prefix_entropy_zero", "TLMC8488.prefix_entropy_zero._proof_1_1", "TLMC8488.prefix_entropy_zero._proof_1_2", "TLMC8488.prefix_iff_dist", "TLMC8488.prefix_refl", "TLMC8488.prefix_representative", "TLMC8488.prefix_symm", "TLMC8488.prefix_uniformity", "TLMC8488.representative", "TLMC8488.representative.eq_1", "TLMC8488.representative.eq_2", "TLMC8488.representative.match_1", "TLMC8488.representative_injective", "TLMC8488.representative_prefix_injective", "TLMC8488.shift", "TLMC8488.shift._proof_1", "TLMC8488.shift._proof_2", "TLMC8488.shift.eq_1", "TLMC8488.shift_continuous", "TLMC8488.shift_iterate_apply", "TLMC8488.spike", "TLMC8488.spike._proof_1", "TLMC8488.spike.eq_1", "TLMC8488.streamMetric", "TLMC8488.streamMetric._proof_1", "TLMC8488.uniqueOne", "TLMC8488.uniqueOne.eq_1", "TLMC8488.uniqueOne_closed", "TLMC8488.zero", "TLMC8488.zero._proof_1", "TLMC8488.zero.eq_1"]
  let actual := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC8488 |>.isPrefixOf n then some n.toString else none
  unless actual.all expected.contains && expected.all actual.contains do
    throwError "namespace coverage mismatch: {actual}"
  for n in actual do
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {actual.length}"
