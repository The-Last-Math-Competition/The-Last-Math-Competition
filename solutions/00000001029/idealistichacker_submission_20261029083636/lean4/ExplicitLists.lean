import Catalogues
import FieldTables
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Dedup

namespace Steiner1029.Explicit

universe u

def subsetCodes {A : Type u} [DecidableEq A] (alphabet : List A) : List (Finset A) :=
  alphabet.sublists.map List.toFinset

theorem mem_subsetCodes {A : Type u} [DecidableEq A] (alphabet : List A) (s : Finset A) :
    s ∈ subsetCodes alphabet ↔ ∀ a ∈ s, a ∈ alphabet := by
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    intro a ha
    exact (List.mem_sublists.mp ht).subset (List.mem_toFinset.mp ha)
  · intro hs
    let t := alphabet.filter (fun a => decide (a ∈ s))
    have ht : t.toFinset = s := by
      ext a
      simp only [t, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun ha => ⟨hs a ha, ha⟩⟩
    exact List.mem_map.mpr ⟨t, List.mem_sublists.mpr List.filter_sublist, ht⟩

variable (K : Type u) [Field K] [Fintype K] [DecidableEq K]
    (alphabet : List K) (n : Nat)

def blockList (k : Nat) : List (Finset (V K n)) :=
  ((subsetCodes (allFunctions alphabet n)).dedup).filter
    (fun W => decide (W ∈ dimCarriers K n k))

theorem mem_blockList (hall : ∀ a, a ∈ alphabet) (k : Nat) (W : Finset (V K n)) :
    W ∈ blockList K alphabet n k ↔ W ∈ dimCarriers K n k := by
  simp only [blockList, List.mem_filter, List.mem_dedup, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hW
    exact ⟨(mem_subsetCodes _ W).2 (fun v _ => mem_allFunctions alphabet hall n v), hW⟩

def catalogueList (k : Nat) : List (Finset (Finset (V K n))) :=
  if 2 ≤ k ∧ k ≤ n then
    ((subsetCodes (blockList K alphabet n k)).filter
      (fun B => decide (Catalog.IncidenceClosed K n B))).dedup
  else []

theorem mem_catalogueList (hall : ∀ a, a ∈ alphabet) (k : Nat)
    (B : Finset (Finset (V K n))) :
    B ∈ catalogueList K alphabet n k ↔ B ∈ Catalog.catalogue K n k := by
  by_cases hg : 2 ≤ k ∧ k ≤ n
  · have hb : B ∈ subsetCodes (blockList K alphabet n k) ↔ B ⊆ dimCarriers K n k := by
      rw [mem_subsetCodes]
      constructor
      · intro h W hW
        exact (mem_blockList K alphabet n hall k W).1 (h W hW)
      · intro h W hW
        exact (mem_blockList K alphabet n hall k W).2 (h hW)
    rw [catalogueList, if_pos hg, Catalog.mem_catalogue]
    simp only [List.mem_dedup, List.mem_filter, decide_eq_true_eq, hb, hg, true_and]
  · simp [catalogueList, hg, Catalog.catalogue]

theorem catalogueList_nodup (k : Nat) : (catalogueList K alphabet n k).Nodup := by
  unfold catalogueList
  split
  · exact List.nodup_dedup _
  · exact List.nodup_nil

theorem catalogueList_invalid (k : Nat) (hg : ¬(2 ≤ k ∧ k ≤ n)) :
    catalogueList K alphabet n k = [] := by
  simp [catalogueList, hg]

theorem catalogueList_sound (hall : ∀ a, a ∈ alphabet) (k : Nat)
    (B : Finset (Finset (V K n))) (hB : B ∈ catalogueList K alphabet n k) :
    Catalog.actualDesign K n k (Catalog.decode K n B) :=
  Catalog.catalogue_sound K n k B ((mem_catalogueList K alphabet n hall k B).1 hB)

theorem catalogueList_complete (hall : ∀ a, a ∈ alphabet) (k : Nat)
    (D : Finset (Submodule K (V K n))) (hD : Catalog.actualDesign K n k D) :
    Catalog.encode K n D ∈ catalogueList K alphabet n k :=
  (mem_catalogueList K alphabet n hall k _).2 (Catalog.catalogue_complete K n k D hD)

theorem actualDesign_iff_existsUnique_list (hall : ∀ a, a ∈ alphabet) (k : Nat)
    (D : Finset (Submodule K (V K n))) :
    Catalog.actualDesign K n k D ↔
      ∃! B, B ∈ catalogueList K alphabet n k ∧ Catalog.decode K n B = D := by
  simpa only [mem_catalogueList K alphabet n hall] using
    Catalog.actualDesign_iff_existsUnique_catalogue K n k D

end Steiner1029.Explicit

#check Steiner1029.Explicit.mem_subsetCodes
#print axioms Steiner1029.Explicit.mem_subsetCodes
#check Steiner1029.Explicit.mem_blockList
#print axioms Steiner1029.Explicit.mem_blockList
#check Steiner1029.Explicit.mem_catalogueList
#print axioms Steiner1029.Explicit.mem_catalogueList
#check Steiner1029.Explicit.catalogueList_nodup
#print axioms Steiner1029.Explicit.catalogueList_nodup
#check Steiner1029.Explicit.catalogueList_invalid
#print axioms Steiner1029.Explicit.catalogueList_invalid
#check Steiner1029.Explicit.catalogueList_sound
#print axioms Steiner1029.Explicit.catalogueList_sound
#check Steiner1029.Explicit.catalogueList_complete
#print axioms Steiner1029.Explicit.catalogueList_complete
#check Steiner1029.Explicit.actualDesign_iff_existsUnique_list
#print axioms Steiner1029.Explicit.actualDesign_iff_existsUnique_list
#print Steiner1029.Explicit.subsetCodes
#print axioms Steiner1029.Explicit.subsetCodes
#print Steiner1029.Explicit.blockList
#print axioms Steiner1029.Explicit.blockList
#print Steiner1029.Explicit.catalogueList
#print axioms Steiner1029.Explicit.catalogueList
