import Lake
open Lake DSL

package tlmc5838 where
  srcDir := "."

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib TLMC5838 where
  roots := #[`BlockTheory, `Involution, `C2Algebra, `Counterexample, `Main, `Check]
  moreLeanArgs := #["-DwarningAsError=true"]
