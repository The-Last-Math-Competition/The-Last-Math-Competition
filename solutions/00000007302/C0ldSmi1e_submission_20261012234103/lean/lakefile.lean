import Lake
open Lake DSL

package conjecture7302 where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.19.0"

@[default_target]
lean_lib Conjecture7302 where
  roots := #[`Conjecture7302, `GenericExtreme, `TensorNuclear, `DecompositionBridge]
