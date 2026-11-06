import Lake
open Lake DSL
package tlmc9343 where
  leanOptions := #[⟨`warningAsError, true⟩]
@[default_target]
lean_lib Exchangeable
