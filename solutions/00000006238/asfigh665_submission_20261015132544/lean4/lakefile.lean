import Lake
open Lake DSL

package conjecture6238 where
  version := v!"1.0.0"

lean_lib Conjecture6238 where
  roots := #[`Conjecture6238]

@[default_target]
lean_exe verify where
  root := `Main
