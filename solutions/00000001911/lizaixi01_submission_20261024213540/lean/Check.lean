import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if (`TLMC1911).isPrefixOf n || (n.toString.splitOn ".").contains "TLMC1911" then
      some n else none
  let required := [`TLMC1911.euclidean_norm,
    `TLMC1911.euclidean_volume,
    `TLMC1911.clipped,
    `TLMC1911.clipped_norm,
    `TLMC1911.clipped_lipschitz,
    `TLMC1911.field,
    `TLMC1911.field_unit,
    `TLMC1911.field_ne_zero,
    `TLMC1911.normalization_bound,
    `TLMC1911.field_lipschitz,
    `TLMC1911.field_radial,
    `TLMC1911.bump,
    `TLMC1911.test,
    `TLMC1911.test_nonneg,
    `TLMC1911.test_le_one,
    `TLMC1911.test_one,
    `TLMC1911.test_zero,
    `TLMC1911.test_memLp,
    `TLMC1911.cone,
    `TLMC1911.cone_norm,
    `TLMC1911.radial_line,
    `TLMC1911.kernel,
    `TLMC1911.cutoff,
    `TLMC1911.conePV,
    `TLMC1911.kernel_zero_outside,
    `TLMC1911.kernel_nonneg,
    `TLMC1911.kernel_integrableOn,
    `TLMC1911.kernel_integrable,
    `TLMC1911.cutoff_integrable,
    `TLMC1911.kernel_plateau,
    `TLMC1911.conePV_lower,
    `TLMC1911.cutoff_eq_conePV,
    `TLMC1911.conePV_tendsto,
    `TLMC1911.no_memLp_cone_lower,
    `TLMC1911.no_L2_PV_representative,
    `TLMC1911.RepresentsFullPV,
    `TLMC1911.no_bounded_fullPV_operator,
    `TLMC1911.printed_untruncated_conjunct_false]
  unless required.all names.contains do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
