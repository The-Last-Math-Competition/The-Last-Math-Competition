import Lake
open Lake DSL
package tlmc_neutral where
  leanOptions := #[⟨`warningAsError, true⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"
@[default_target]
lean_lib Proximity
