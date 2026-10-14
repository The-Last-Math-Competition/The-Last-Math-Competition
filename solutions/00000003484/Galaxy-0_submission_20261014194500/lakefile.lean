import Lake
open Lake DSL
package tlmc3484 where
  moreLeanArgs := #["-DwarningAsError=true"]
@[default_target]
lean_lib Main where
  roots := #[`Main]
