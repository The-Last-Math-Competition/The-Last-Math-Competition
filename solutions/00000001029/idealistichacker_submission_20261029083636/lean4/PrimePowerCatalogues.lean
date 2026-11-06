import FieldExistence
import QCatalogue

namespace Steiner1029.QOnly

theorem chosen_exists_prime_power (q : Nat) (hq : IsPrimePow q) :
    ∃ t, chosenFieldTable q = some t := by
  obtain ⟨t, ht⟩ := firstFieldTable_exists_of_isPrimePow q hq
  unfold chosenFieldTable
  split
  · next hn =>
      rw [hn] at ht
      contradiction
  · exact ⟨_, rfl⟩

theorem catalogue_exists_prime_power (q n k : Nat) (hq : IsPrimePow q) :
    ∃ r, catalogue q n k = some r := by
  obtain ⟨t, ht⟩ := chosen_exists_prime_power q hq
  exact ⟨⟨t, selectedList t n k⟩, by simp only [catalogue, ht, Option.map_some]⟩

theorem finite_explicit_catalogue (q n k : Nat) (hq : IsPrimePow q) :
    ∃ r : Result q n, catalogue q n k = some r ∧ r.codes.Nodup ∧
      Fintype.card (TableElem r.fieldTable.val) = q ∧
      (letI := fieldOfTable r.fieldTable.val r.fieldTable.property
       ∀ D : Finset (Submodule (TableElem r.fieldTable.val) (V (TableElem r.fieldTable.val) n)),
         Catalog.actualDesign (TableElem r.fieldTable.val) n k D ↔
           ∃! B, B ∈ r.codes ∧ Catalog.decode (TableElem r.fieldTable.val) n B = D) := by
  obtain ⟨r, hr⟩ := catalogue_exists_prime_power q n k hq
  exact ⟨r, hr, catalogue_nodup hr, result_field_card r, actualDesign_iff_existsUnique_output hr⟩

theorem finite_explicit_catalogue_of_divides (q n k : Nat) (hq : IsPrimePow q) (_hdiv : k ∣ n) :
    ∃ r : Result q n, catalogue q n k = some r ∧ r.codes.Nodup ∧
      (letI := fieldOfTable r.fieldTable.val r.fieldTable.property
       ∀ D : Finset (Submodule (TableElem r.fieldTable.val) (V (TableElem r.fieldTable.val) n)),
         Catalog.actualDesign (TableElem r.fieldTable.val) n k D ↔
           ∃! B, B ∈ r.codes ∧ Catalog.decode (TableElem r.fieldTable.val) n B = D) := by
  obtain ⟨r, hr, hn, _, hcorrect⟩ := finite_explicit_catalogue q n k hq
  exact ⟨r, hr, hn, hcorrect⟩

end Steiner1029.QOnly

#check Steiner1029.QOnly.chosen_exists_prime_power
#print axioms Steiner1029.QOnly.chosen_exists_prime_power
#check Steiner1029.QOnly.catalogue_exists_prime_power
#print axioms Steiner1029.QOnly.catalogue_exists_prime_power
#check Steiner1029.QOnly.finite_explicit_catalogue
#print axioms Steiner1029.QOnly.finite_explicit_catalogue
#check Steiner1029.QOnly.finite_explicit_catalogue_of_divides
#print axioms Steiner1029.QOnly.finite_explicit_catalogue_of_divides
