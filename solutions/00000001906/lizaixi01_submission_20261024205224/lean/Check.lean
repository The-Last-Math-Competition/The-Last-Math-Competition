import Main

set_option linter.auxLemma false

run_cmd do
  let names := (← Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if (`TLMC1906).isPrefixOf n || (n.toString.splitOn ".").contains "TLMC1906" then
      some n else none
  let required := [`TLMC1906.input,
    `TLMC1906.projection,
    `TLMC1906.squareFunction,
    `TLMC1906.Admissible,
    `TLMC1906.singleton_square,
    `TLMC1906.Admissible.singleton,
    `TLMC1906.input_memLp,
    `TLMC1906.input_integrable,
    `TLMC1906.input_fourier,
    `TLMC1906.projection_integral,
    `TLMC1906.phase,
    `TLMC1906.phase_norm,
    `TLMC1906.phase_integrable,
    `TLMC1906.projection_input_double,
    `TLMC1906.projection_input_swap,
    `TLMC1906.kernel,
    `TLMC1906.phase_interval,
    `TLMC1906.projection_input_kernel,
    `TLMC1906.projection_input_kernel_shift,
    `TLMC1906.inv_square_integral,
    `TLMC1906.cosine_integral_bound,
    `TLMC1906.kernel_im,
    `TLMC1906.projection_input_im,
    `TLMC1906.projection_input_im_lower,
    `TLMC1906.input_eLpNorm,
    `TLMC1906.input_exponential_norm,
    `TLMC1906.projection_input_continuous,
    `TLMC1906.Admissible.output_memLp,
    `TLMC1906.output_eLpNorm_lower,
    `TLMC1906.exponential_output_lower,
    `TLMC1906.Admissible.linear_lower,
    `TLMC1906.no_sqrt_bigO,
    `TLMC1906.no_finite_sqrt_coefficient]
  unless required.all names.contains do
    throwError "required complete proof declarations are absent"
  for n in names do
    Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
    Lean.logInfo m!"NAMESPACE_DECL {n}"
  Lean.logInfo m!"NAMESPACE_COVERAGE_OK {names.length}"
