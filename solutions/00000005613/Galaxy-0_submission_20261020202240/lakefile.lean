import Lake
open Lake DSL
package tlmc5613 where
  leanOptions := #[⟨`warningAsError, true⟩]
@[default_target]
lean_lib Subresultant
