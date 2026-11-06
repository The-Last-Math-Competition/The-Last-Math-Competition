import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if (`TLMC2195).isPrefixOf n || (n.toString.splitOn ".").contains "TLMC2195" then
      some n else none
  let required := [`TLMC2195.Perfect,
    `TLMC2195.Perfect.hereditary,
    `TLMC2195.Perfect.iso,
    `TLMC2195.clique_chromatic_eq_of_two_colorable,
    `TLMC2195.perfect_of_two_colorable,
    `TLMC2195.perfect_bot,
    `TLMC2195.substitute,
    `TLMC2195.singletonSurvivorIsEmpty,
    `TLMC2195.singletonSubstitutionIso,
    `TLMC2195.InProduct,
    `TLMC2195.inProduct_of_perfect,
    `TLMC2195.inProduct_iso,
    `TLMC2195.speed,
    `TLMC2195.speed_pos,
    `TLMC2195.bipGraph,
    `TLMC2195.bipColoring,
    `TLMC2195.bip_perfect,
    `TLMC2195.labelledBip,
    `TLMC2195.labelledBip_perfect,
    `TLMC2195.labelledBip_injective,
    `TLMC2195.matrixIntoProduct,
    `TLMC2195.matrixIntoProduct_injective,
    `TLMC2195.actual_speed_lower,
    `TLMC2195.chromatic_iso,
    `TLMC2195.cliqueNum_le_iso,
    `TLMC2195.cliqueNum_iso,
    `TLMC2195.perfect_all_induced,
    `TLMC2195.log_actual_speed_lower,
    `TLMC2195.even_tendsto,
    `TLMC2195.log_even_ratio_tendsto_zero,
    `TLMC2195.no_eventual_log_bound,
    `TLMC2195.PrintedSpeedFormula,
    `TLMC2195.not_printed_speed_formula]
  unless required.all names.contains do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
