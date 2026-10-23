import Lake
open Lake DSL
package «tlmc7978» where
@[default_target]
lean_lib PIR where
  roots := #[`PIR, `Rates, `Approx, `Capacity, `Coupling, `CouplingIndexed]
