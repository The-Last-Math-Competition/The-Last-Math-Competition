import Lake
open Lake DSL
package tlmc5207 where
  leanOptions := #[⟨`warningAsError, true⟩]
@[default_target]
lean_lib RankGap
