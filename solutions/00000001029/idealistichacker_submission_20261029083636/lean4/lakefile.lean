import Lake
open Lake DSL

package tlmc1029 where
  srcDir := "."

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib TLMC1029 where
  roots := #[`FieldTables, `TableFields, `CarrierCodes, `Catalogues,
    `ExplicitLists, `QCatalogue, `FieldExistence, `PrimePowerCatalogues,
    `Transport, `Main, `FamilySets, `Check, `CheckDefinitions, `Demo]
  moreLeanArgs := #["-DwarningAsError=true"]
