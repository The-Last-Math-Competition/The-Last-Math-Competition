import Lake
open Lake DSL

package conjecture1624 where
  leanOptions := #[⟨`warningAsError, true⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"

@[default_target]
lean_lib Conjecture1624 where
  roots := #[`Conjecture1624, `Verification]
