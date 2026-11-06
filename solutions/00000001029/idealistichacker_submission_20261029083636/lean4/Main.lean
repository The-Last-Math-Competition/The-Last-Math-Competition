import PrimePowerCatalogues
import Transport

namespace Steiner1029.QOnly

universe u

noncomputable def modelEquiv {q n : Nat} (r : Result q n)
    (K : Type u) [Field K] [Fintype K] (hK : Fintype.card K = q) :
    letI := fieldOfTable r.fieldTable.val r.fieldTable.property
    TableElem r.fieldTable.val ≃+* K :=
  letI := fieldOfTable r.fieldTable.val r.fieldTable.property
  FiniteField.ringEquivOfCardEq ((result_field_card r).trans hK.symm)

theorem actualDesign_iff_output_over_model {q n k : Nat} {r : Result q n}
    (hr : catalogue q n k = some r) (K : Type u) [Field K] [Fintype K] [DecidableEq K]
    (hK : Fintype.card K = q) :
    letI := fieldOfTable r.fieldTable.val r.fieldTable.property
    ∀ D : Finset (Submodule K (V K n)),
      Catalog.actualDesign K n k D ↔
        ∃! B, B ∈ r.codes ∧
          Transport.familyEquiv (modelEquiv r K hK) n
            (Catalog.decode (TableElem r.fieldTable.val) n B) = D := by
  let := fieldOfTable r.fieldTable.val r.fieldTable.property
  intro D
  rw [catalogue_codes hr]
  simpa only [selectedList, Explicit.mem_catalogueList (TableElem r.fieldTable.val)
    (fieldAlphabet r.fieldTable.val) n (fieldAlphabet_complete r.fieldTable.val)] using
    Transport.actualDesign_iff_existsUnique_source_catalogue (modelEquiv r K hK) n k D

theorem finite_explicit_catalogue_every_model (q n k : Nat) (hq : IsPrimePow q) :
    ∃ r : Result q n, catalogue q n k = some r ∧ r.codes.Nodup ∧
      ∀ (K : Type u) [Field K] [Fintype K] [DecidableEq K] (hK : Fintype.card K = q),
        (letI := fieldOfTable r.fieldTable.val r.fieldTable.property
         ∀ D : Finset (Submodule K (V K n)),
           Catalog.actualDesign K n k D ↔
             ∃! B, B ∈ r.codes ∧
               Transport.familyEquiv (modelEquiv r K hK) n
                 (Catalog.decode (TableElem r.fieldTable.val) n B) = D) := by
  obtain ⟨r, hr⟩ := catalogue_exists_prime_power q n k hq
  refine ⟨r, hr, catalogue_nodup hr, ?_⟩
  intro K _ _ _ hK
  exact actualDesign_iff_output_over_model hr K hK

theorem source_conjecture (q n k : Nat) (hq : IsPrimePow q) (_hdiv : k ∣ n) :
    ∃ r : Result q n, catalogue q n k = some r ∧ r.codes.Nodup ∧
      ∀ (K : Type u) [Field K] [Fintype K] [DecidableEq K] (hK : Fintype.card K = q),
        (letI := fieldOfTable r.fieldTable.val r.fieldTable.property
         ∀ D : Finset (Submodule K (V K n)),
           Catalog.actualDesign K n k D ↔
             ∃! B, B ∈ r.codes ∧
               Transport.familyEquiv (modelEquiv r K hK) n
                 (Catalog.decode (TableElem r.fieldTable.val) n B) = D) :=
  finite_explicit_catalogue_every_model q n k hq

end Steiner1029.QOnly

#check Steiner1029.QOnly.actualDesign_iff_output_over_model
#print axioms Steiner1029.QOnly.actualDesign_iff_output_over_model
#check Steiner1029.QOnly.finite_explicit_catalogue_every_model
#print axioms Steiner1029.QOnly.finite_explicit_catalogue_every_model
#check Steiner1029.QOnly.source_conjecture
#print axioms Steiner1029.QOnly.source_conjecture
#print Steiner1029.QOnly.modelEquiv
#print axioms Steiner1029.QOnly.modelEquiv
