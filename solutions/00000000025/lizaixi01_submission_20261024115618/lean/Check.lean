import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC25 |>.isPrefixOf n then some n else none
  let required := [`TLMC25.complete_counterexample,
    `TLMC25.K, `TLMC25.G, `TLMC25.galEquiv, `TLMC25.extension_galois,
    `TLMC25.extension_degree, `TLMC25.actual_discriminant,
    `TLMC25.chiA, `TLMC25.chiB, `TLMC25.chiA_primitive, `TLMC25.chiB_primitive,
    `TLMC25.chiA_nontrivial, `TLMC25.chiB_nontrivial, `TLMC25.characters_distinct,
    `TLMC25.galoisRepresentation, `TLMC25.galois_character,
    `TLMC25.chiA_irreducible, `TLMC25.chiB_irreducible, `TLMC25.chiA_real,
    `TLMC25.chiB_real, `TLMC25.characters_orthogonal, `TLMC25.no_intertwiner,
    `TLMC25.representations_inequivalent, `TLMC25.ramifiedPrime,
    `TLMC25.ramifiedPrime_prime, `TLMC25.ramifiedPrime_over_two,
    `TLMC25.ramification_index_two, `TLMC25.actual_inertia_two,
    `TLMC25.inertia_invariants_zero, `TLMC25.inertia_fixed_det_one,
    `TLMC25.full_eulerFactor_two, `TLMC25.chiA_eulerFactor_two,
    `TLMC25.chiB_eulerFactor_two, `TLMC25.WindowZero,
    `TLMC25.PrintedRealIff, `TLMC25.PrintedExclusion,
    `TLMC25.no_function_family_satisfies_printed_conjunction,
    `TLMC25.nativeLFunctions, `TLMC25.native_zero_condition,
    `TLMC25.window_nonempty, `TLMC25.native_conjunction_impossible]
  unless required.all names.contains do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
