import Main

namespace Steiner1029.SetFamilies

universe u

variable (K : Type u) [Field K] [Fintype K] [DecidableEq K] (n : Nat)

theorem every_family_finite (D : Set (Submodule K (V K n))) : D.Finite := by
  let : Finite (Submodule K (V K n)) :=
    Finite.of_injective (ofSubmodule K n) (Catalog.ofSubmodule_injective K n)
  exact Set.toFinite D

noncomputable def finiteFamily (D : Set (Submodule K (V K n))) :
    Finset (Submodule K (V K n)) :=
  (every_family_finite K n D).toFinset

theorem mem_finiteFamily (D : Set (Submodule K (V K n))) (U : Submodule K (V K n)) :
    U ∈ finiteFamily K n D ↔ U ∈ D := by
  simp only [finiteFamily, Set.Finite.mem_toFinset]

def actualSetDesign (k : Nat) (D : Set (Submodule K (V K n))) : Prop :=
  (2 ≤ k ∧ k ≤ n) ∧
    (∀ W ∈ D, Module.finrank K W = k) ∧
    (∀ U : Submodule K (V K n), Module.finrank K U = 2 →
      ∃! W, W ∈ D ∧ U ≤ W)

theorem actualSetDesign_iff (k : Nat) (D : Set (Submodule K (V K n))) :
    actualSetDesign K n k D ↔ Catalog.actualDesign K n k (finiteFamily K n D) := by
  simp only [actualSetDesign, Catalog.actualDesign, mem_finiteFamily]

theorem finiteFamily_injective : Function.Injective (finiteFamily K n) := by
  intro D E h
  ext U
  rw [← mem_finiteFamily K n D U, ← mem_finiteFamily K n E U, h]

theorem actualSetDesign_iff_output {q k : Nat} {r : QOnly.Result q n}
    (hr : QOnly.catalogue q n k = some r) (hK : Fintype.card K = q) :
    letI := fieldOfTable r.fieldTable.val r.fieldTable.property
    ∀ D : Set (Submodule K (V K n)), actualSetDesign K n k D ↔
      ∃! B, B ∈ r.codes ∧
        Transport.familyEquiv (QOnly.modelEquiv r K hK) n
          (Catalog.decode (TableElem r.fieldTable.val) n B) = finiteFamily K n D := by
  let := fieldOfTable r.fieldTable.val r.fieldTable.property
  intro D
  rw [actualSetDesign_iff]
  exact QOnly.actualDesign_iff_output_over_model hr K hK (finiteFamily K n D)

theorem source_conjecture_sets (q n k : Nat) (hq : IsPrimePow q) (_hdiv : k ∣ n) :
    ∃ r : QOnly.Result q n, QOnly.catalogue q n k = some r ∧ r.codes.Nodup ∧
      ∀ (K : Type u) [Field K] [Fintype K] [DecidableEq K] (hK : Fintype.card K = q),
        (letI := fieldOfTable r.fieldTable.val r.fieldTable.property
         ∀ D : Set (Submodule K (V K n)), actualSetDesign K n k D ↔
           ∃! B, B ∈ r.codes ∧
             Transport.familyEquiv (QOnly.modelEquiv r K hK) n
               (Catalog.decode (TableElem r.fieldTable.val) n B) = finiteFamily K n D) := by
  obtain ⟨r, hr⟩ := QOnly.catalogue_exists_prime_power q n k hq
  refine ⟨r, hr, QOnly.catalogue_nodup hr, ?_⟩
  intro K _ _ _ hK
  exact actualSetDesign_iff_output K n hr hK

end Steiner1029.SetFamilies

#check Steiner1029.SetFamilies.every_family_finite
#print axioms Steiner1029.SetFamilies.every_family_finite
#check Steiner1029.SetFamilies.mem_finiteFamily
#print axioms Steiner1029.SetFamilies.mem_finiteFamily
#check Steiner1029.SetFamilies.actualSetDesign_iff
#print axioms Steiner1029.SetFamilies.actualSetDesign_iff
#check Steiner1029.SetFamilies.finiteFamily_injective
#print axioms Steiner1029.SetFamilies.finiteFamily_injective
#check Steiner1029.SetFamilies.actualSetDesign_iff_output
#print axioms Steiner1029.SetFamilies.actualSetDesign_iff_output
#check Steiner1029.SetFamilies.source_conjecture_sets
#print axioms Steiner1029.SetFamilies.source_conjecture_sets
#print Steiner1029.SetFamilies.actualSetDesign
#print axioms Steiner1029.SetFamilies.actualSetDesign
#print Steiner1029.SetFamilies.finiteFamily
#print axioms Steiner1029.SetFamilies.finiteFamily
