import QCatalogue

namespace Steiner1029.Diagnostics

-- These runs are diagnostics, not proofs of the generic statements.
def summary (q n k : Nat) : Option (Nat × List Nat) :=
  (QOnly.catalogue q n k).map (fun r => (r.codes.length, r.codes.map Finset.card))

end Steiner1029.Diagnostics

#eval IO.println "field-table-search-q2"
#eval (Steiner1029.firstFieldTable 2).isSome
#eval IO.println "proof-attached-table-q2"
#eval (Steiner1029.chosenFieldTable 2).isSome
#eval IO.println "invalid-parameter-catalogue"
#eval Steiner1029.Diagnostics.summary 2 0 0
#eval IO.println "no-field-model-q0-q1"
#eval Steiner1029.Diagnostics.summary 0 2 2
#eval Steiner1029.Diagnostics.summary 1 2 2
#eval IO.println "valid-catalogue-q2-n2-k2"
#eval Steiner1029.Diagnostics.summary 2 2 2
