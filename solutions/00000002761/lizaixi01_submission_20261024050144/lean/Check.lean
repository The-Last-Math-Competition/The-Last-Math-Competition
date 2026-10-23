import Main

set_option linter.auxLemma false

-- Enumerate the imported environment itself, including generated declarations.
-- Each name is passed to Lean's ordinary #print axioms command.
run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if `TLMC2761 |>.isPrefixOf n then some n else none
  unless names.contains `TLMC2761.native_polynomial_witness &&
      names.contains `TLMC2761.counterexample &&
      names.contains `TLMC2761.centralPolynomial_degree &&
      names.contains `TLMC2761.weak_zero do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
