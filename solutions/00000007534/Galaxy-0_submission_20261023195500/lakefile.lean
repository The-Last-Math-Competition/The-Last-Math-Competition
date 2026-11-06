import Lake
open Lake DSL
package tlmc7534 where
  leanOptions := #[⟨`warningAsError, true⟩]
@[default_target]
lean_lib Counterexample
