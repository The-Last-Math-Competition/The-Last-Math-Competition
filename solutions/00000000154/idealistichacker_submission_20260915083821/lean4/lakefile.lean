import Lake
open Lake DSL

package tlmc154Submission where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

@[default_target]
lean_lib TLMC154Submission where
  roots := #[`Main]
