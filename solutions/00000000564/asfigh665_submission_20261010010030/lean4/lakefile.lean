import Lake
open Lake DSL

package conjecture564 where
  version := v!"1.0.0"

lean_lib Conjecture564 where
  roots := #[`Conjecture564]

@[default_target]
lean_exe verify where
  root := `Main
