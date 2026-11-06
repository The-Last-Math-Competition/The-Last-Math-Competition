import TableFields
import ExplicitLists

namespace Steiner1029.QOnly

def fieldAlphabet {q : Nat} (t : RawFieldTable q) : List (TableElem t) :=
  (List.finRange q).map TableElem.mk

theorem fieldAlphabet_complete {q : Nat} (t : RawFieldTable q) (a : TableElem t) :
    a ∈ fieldAlphabet t := by
  apply List.mem_map.mpr
  exact ⟨a.val, List.mem_finRange _, by cases a; rfl⟩

def selectedList {q : Nat} (t : {t : RawFieldTable q // TableValid t}) (n k : Nat) :
    List (Finset (Finset (V (TableElem t.val) n))) :=
  letI := fieldOfTable t.val t.property
  Explicit.catalogueList (TableElem t.val) (fieldAlphabet t.val) n k

structure Result (q n : Nat) where
  fieldTable : {t : RawFieldTable q // TableValid t}
  codes : List (Finset (Finset (V (TableElem fieldTable.val) n)))

def catalogue (q n k : Nat) : Option (Result q n) :=
  (chosenFieldTable q).map (fun t => ⟨t, selectedList t n k⟩)

theorem catalogue_codes {q n k : Nat} {r : Result q n}
    (hr : catalogue q n k = some r) : r.codes = selectedList r.fieldTable n k := by
  obtain ⟨t, _, heq⟩ := Option.map_eq_some_iff.mp hr
  cases heq
  rfl

theorem catalogue_table {q n k : Nat} {r : Result q n}
    (hr : catalogue q n k = some r) : chosenFieldTable q = some r.fieldTable := by
  obtain ⟨t, ht, heq⟩ := Option.map_eq_some_iff.mp hr
  cases heq
  exact ht

theorem catalogue_exists_of_model (K : Type*) [Field K] [Fintype K]
    (q n k : Nat) (hq : Fintype.card K = q) :
    ∃ r, catalogue q n k = some r := by
  obtain ⟨t, ht⟩ := chosenFieldTable_exists_of_model K q hq
  exact ⟨⟨t, selectedList t n k⟩, by simp only [catalogue, ht, Option.map_some]⟩

theorem catalogue_none_iff (q n k : Nat) :
    catalogue q n k = none ↔ chosenFieldTable q = none := by
  simp [catalogue]

theorem catalogue_nodup {q n k : Nat} {r : Result q n}
    (hr : catalogue q n k = some r) : r.codes.Nodup := by
  rw [catalogue_codes hr]
  let := fieldOfTable r.fieldTable.val r.fieldTable.property
  exact Explicit.catalogueList_nodup (TableElem r.fieldTable.val)
    (fieldAlphabet r.fieldTable.val) n k

theorem catalogue_invalid {q n k : Nat} {r : Result q n}
    (hr : catalogue q n k = some r) (hg : ¬(2 ≤ k ∧ k ≤ n)) : r.codes = [] := by
  rw [catalogue_codes hr]
  let := fieldOfTable r.fieldTable.val r.fieldTable.property
  exact Explicit.catalogueList_invalid (TableElem r.fieldTable.val)
    (fieldAlphabet r.fieldTable.val) n k hg

theorem catalogue_sound {q n k : Nat} {r : Result q n}
    (hr : catalogue q n k = some r) :
    letI := fieldOfTable r.fieldTable.val r.fieldTable.property
    ∀ B ∈ r.codes,
      Catalog.actualDesign (TableElem r.fieldTable.val) n k
        (Catalog.decode (TableElem r.fieldTable.val) n B) := by
  let := fieldOfTable r.fieldTable.val r.fieldTable.property
  intro B hB
  rw [catalogue_codes hr] at hB
  exact Explicit.catalogueList_sound (TableElem r.fieldTable.val)
    (fieldAlphabet r.fieldTable.val) n (fieldAlphabet_complete r.fieldTable.val) k B hB

theorem actualDesign_iff_existsUnique_output {q n k : Nat} {r : Result q n}
    (hr : catalogue q n k = some r) :
    letI := fieldOfTable r.fieldTable.val r.fieldTable.property
    ∀ D : Finset (Submodule (TableElem r.fieldTable.val) (V (TableElem r.fieldTable.val) n)),
      Catalog.actualDesign (TableElem r.fieldTable.val) n k D ↔
        ∃! B, B ∈ r.codes ∧ Catalog.decode (TableElem r.fieldTable.val) n B = D := by
  let := fieldOfTable r.fieldTable.val r.fieldTable.property
  intro D
  rw [catalogue_codes hr]
  exact Explicit.actualDesign_iff_existsUnique_list (TableElem r.fieldTable.val)
    (fieldAlphabet r.fieldTable.val) n (fieldAlphabet_complete r.fieldTable.val) k D

theorem result_field_card {q n : Nat} (r : Result q n) :
    Fintype.card (TableElem r.fieldTable.val) = q :=
  tableElem_card r.fieldTable.val

end Steiner1029.QOnly

#check Steiner1029.QOnly.fieldAlphabet_complete
#print axioms Steiner1029.QOnly.fieldAlphabet_complete
#check Steiner1029.QOnly.catalogue_codes
#print axioms Steiner1029.QOnly.catalogue_codes
#check Steiner1029.QOnly.catalogue_table
#print axioms Steiner1029.QOnly.catalogue_table
#check Steiner1029.QOnly.catalogue_exists_of_model
#print axioms Steiner1029.QOnly.catalogue_exists_of_model
#check Steiner1029.QOnly.catalogue_none_iff
#print axioms Steiner1029.QOnly.catalogue_none_iff
#check Steiner1029.QOnly.catalogue_nodup
#print axioms Steiner1029.QOnly.catalogue_nodup
#check Steiner1029.QOnly.catalogue_invalid
#print axioms Steiner1029.QOnly.catalogue_invalid
#check Steiner1029.QOnly.catalogue_sound
#print axioms Steiner1029.QOnly.catalogue_sound
#check Steiner1029.QOnly.actualDesign_iff_existsUnique_output
#print axioms Steiner1029.QOnly.actualDesign_iff_existsUnique_output
#check Steiner1029.QOnly.result_field_card
#print axioms Steiner1029.QOnly.result_field_card
#print Steiner1029.QOnly.fieldAlphabet
#print axioms Steiner1029.QOnly.fieldAlphabet
#print Steiner1029.QOnly.selectedList
#print axioms Steiner1029.QOnly.selectedList
#print Steiner1029.QOnly.catalogue
#print axioms Steiner1029.QOnly.catalogue
