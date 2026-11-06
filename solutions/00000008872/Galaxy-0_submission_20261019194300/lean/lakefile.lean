import Lake
open Lake DSL
package «tlmc8872» where
  version := v!"0.1.0"
@[default_target]
lean_lib TLMC8872 where
  roots := #[`Core, `NumberParts, `Sums, `Toggle, `Stabilization, `StarHeap, `OutcomeBridge, `Main]
