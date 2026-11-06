import Lake
open Lake DSL

package tlmc7686 where
  srcDir := "."

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib TLMC7686 where
  roots := #[`Gaussian, `QOnePresentation, `ModThree, `PeriodicityNegation, `Main, `Check]
  moreLeanArgs := #["-DwarningAsError=true"]
