import Lake
open Lake DSL

package conjecture7973 where
  version := v!"1.0.0"

lean_lib Conjecture7973 where
  roots := #[`Conjecture7973]

@[default_target]
lean_exe verify where
  root := `Main
