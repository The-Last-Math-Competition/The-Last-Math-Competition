import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC1158 |>.isPrefixOf n then some n else none
  let required := [`TLMC1158.complete_counterexample,
    `TLMC1158.commProducts_eq, `TLMC1158.commutatorLength,
    `TLMC1158.commutatorLength_witness, `TLMC1158.commutatorLength_le,
    `TLMC1158.stableCommutatorLength, `TLMC1158.stableCommutatorLength_tendsto,
    `TLMC1158.wordCount_occurrences, `TLMC1158.cancellation_decomposition,
    `TLMC1158.brooks_defect, `TLMC1158.brooks_inverse,
    `TLMC1158.brooks_commProduct, `TLMC1158.c_power_word,
    `TLMC1158.brooks_c_power, `TLMC1158.stable_c_power_lower,
    `TLMC1158.stable_c_power_upper, `TLMC1158.stable_commutator_length_unbounded,
    `TLMC1158.stable_commutator_length_not_bddAbove,
    `TLMC1158.commutatorLength_equiv, `TLMC1158.stableCommutatorLength_equiv,
    `TLMC1158.isomorphic_group_unbounded, `TLMC1158.abelianCoordinates_surjective,
    `TLMC1158.abelianization_not_cyclic,
    `TLMC1158.not_equiv_group_with_cyclic_abelianization]
  unless required.all names.contains do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
