import Lake
open Lake DSL

package «clifford_decomp» where
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib «CliffordDecomp» where
  roots := #[`CliffordDecomp]
