import Lake
open Lake DSL

package tlmc2747 where
  version := v!"1.0.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib Main
