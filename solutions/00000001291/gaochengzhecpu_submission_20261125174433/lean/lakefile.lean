import Lake
open Lake DSL

package «conjecture_00000001291» where
  leanOptions := #[
    ⟨`warningAsError, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Conjecture00000001291» where
  roots := #[`Conjecture00000001291]
