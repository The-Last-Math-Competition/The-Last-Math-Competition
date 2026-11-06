import Catalogues

namespace Steiner1029.Transport

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]

attribute [local instance] RingHomInvPair.of_ringEquiv

def coordinates (e : K ≃+* L) (n : Nat) : V K n ≃ₛₗ[(e : K →+* L)] V L n where
  toFun x i := e (x i)
  invFun y i := e.symm (y i)
  left_inv x := funext (fun i => e.symm_apply_apply (x i))
  right_inv y := funext (fun i => e.apply_symm_apply (y i))
  map_add' x y := funext (fun i => e.map_add (x i) (y i))
  map_smul' a x := funext (fun i => e.map_mul a (x i))

theorem coordinates_apply (e : K ≃+* L) (n : Nat) (x : V K n) (i : Fin n) :
    (coordinates e n).toEquiv x i = e (x i) := rfl

theorem coordinates_symm_apply (e : K ≃+* L) (n : Nat) (y : V L n) (i : Fin n) :
    (coordinates e n).toEquiv.symm y i = e.symm (y i) := rfl

def subspaceIso (e : K ≃+* L) (n : Nat) :
    Submodule K (V K n) ≃o Submodule L (V L n) :=
  Submodule.orderIsoMapComap (coordinates e n)

theorem subspace_le_iff (e : K ≃+* L) (n : Nat) (U W : Submodule K (V K n)) :
    subspaceIso e n U ≤ subspaceIso e n W ↔ U ≤ W :=
  (subspaceIso e n).le_iff_le

theorem mem_subspaceIso (e : K ≃+* L) (n : Nat) (U : Submodule K (V K n))
    (x : V K n) : (coordinates e n).toEquiv x ∈ subspaceIso e n U ↔ x ∈ U := by
  change (coordinates e n).toEquiv x ∈ U.map (coordinates e n).toLinearMap ↔ x ∈ U
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := (coordinates e n).toEquiv.injective hxy
    exact hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem mem_inverse_subspaceIso (e : K ≃+* L) (n : Nat) (U : Submodule L (V L n))
    (x : V K n) : x ∈ (subspaceIso e n).symm U ↔ (coordinates e n).toEquiv x ∈ U :=
  Iff.rfl

theorem subspace_natCard (e : K ≃+* L) (n : Nat) (U : Submodule K (V K n)) :
    Nat.card (subspaceIso e n U) = Nat.card U :=
  (Nat.card_congr ((coordinates e n).submoduleMap U).toEquiv).symm

-- Embedding-based finite-family transport needs no Submodule decidable equality.
def familyEquiv (e : K ≃+* L) (n : Nat) :
    Finset (Submodule K (V K n)) ≃ Finset (Submodule L (V L n)) :=
  (subspaceIso e n).toEquiv.finsetCongr

theorem mem_familyEquiv (e : K ≃+* L) (n : Nat)
    (D : Finset (Submodule K (V K n))) (W : Submodule L (V L n)) :
    W ∈ familyEquiv e n D ↔ (subspaceIso e n).symm W ∈ D := by
  change W ∈ D.map (subspaceIso e n).toEquiv.toEmbedding ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨U, hU, rfl⟩
    simpa using hU
  · intro hW
    exact ⟨(subspaceIso e n).symm W, hW, (subspaceIso e n).apply_symm_apply W⟩

theorem image_mem_familyEquiv (e : K ≃+* L) (n : Nat)
    (D : Finset (Submodule K (V K n))) (U : Submodule K (V K n)) :
    subspaceIso e n U ∈ familyEquiv e n D ↔ U ∈ D := by
  rw [mem_familyEquiv, (subspaceIso e n).symm_apply_apply]

theorem family_card (e : K ≃+* L) (n : Nat) (D : Finset (Submodule K (V K n))) :
    (familyEquiv e n D).card = D.card :=
  Finset.card_map _

theorem family_roundtrip (e : K ≃+* L) (n : Nat) (D : Finset (Submodule K (V K n))) :
    (familyEquiv e n).symm (familyEquiv e n D) = D :=
  (familyEquiv e n).symm_apply_apply D

theorem family_inverse_roundtrip (e : K ≃+* L) (n : Nat)
    (D : Finset (Submodule L (V L n))) :
    familyEquiv e n ((familyEquiv e n).symm D) = D :=
  (familyEquiv e n).apply_symm_apply D

theorem unique_containing_iff (e : K ≃+* L) (n : Nat)
    (D : Finset (Submodule K (V K n))) (U : Submodule K (V K n)) :
    (∃! W, W ∈ familyEquiv e n D ∧ subspaceIso e n U ≤ W) ↔
      ∃! W, W ∈ D ∧ U ≤ W := by
  let f := subspaceIso e n
  constructor
  · rintro ⟨W, ⟨hW, hUW⟩, huniq⟩
    refine ⟨f.symm W, ⟨(mem_familyEquiv e n D W).1 hW, ?_⟩, ?_⟩
    · have h := f.symm.monotone hUW
      rw [f.symm_apply_apply] at h
      exact h
    · intro W' hW'
      apply f.injective
      have h := huniq (f W') ⟨(image_mem_familyEquiv e n D W').2 hW'.1,
        f.monotone hW'.2⟩
      exact h.trans (f.apply_symm_apply W).symm
  · rintro ⟨W, ⟨hW, hUW⟩, huniq⟩
    refine ⟨f W, ⟨(image_mem_familyEquiv e n D W).2 hW, f.monotone hUW⟩, ?_⟩
    rintro W' ⟨hW', hUW'⟩
    have hpre : f.symm W' = W := huniq (f.symm W')
      ⟨(mem_familyEquiv e n D W').1 hW', by
        have h := f.symm.monotone hUW'
        rw [f.symm_apply_apply] at h
        exact h⟩
    calc
      W' = f (f.symm W') := (f.apply_symm_apply W').symm
      _ = f W := congrArg f hpre

variable [Fintype K] [Fintype L]

theorem field_card_eq (e : K ≃+* L) : Fintype.card K = Fintype.card L :=
  Fintype.card_congr e.toEquiv

variable [DecidableEq K] [DecidableEq L]

theorem subspace_finrank (e : K ≃+* L) (n : Nat) (U : Submodule K (V K n)) :
    Module.finrank L (subspaceIso e n U) = Module.finrank K U := by
  have hK : Nat.card U = Fintype.card K ^ Module.finrank K U :=
    (ofSubmodule_card_eq_natCard K n U).symm.trans (ofSubmodule_card_eq_pow_finrank K n U)
  have hL : Nat.card (subspaceIso e n U) =
      Fintype.card L ^ Module.finrank L (subspaceIso e n U) :=
    (ofSubmodule_card_eq_natCard L n _).symm.trans (ofSubmodule_card_eq_pow_finrank L n _)
  apply Nat.pow_right_injective (field_card_two_le K)
  calc
    Fintype.card K ^ Module.finrank L (subspaceIso e n U) =
        Fintype.card L ^ Module.finrank L (subspaceIso e n U) :=
      congrArg (fun q : Nat => q ^ Module.finrank L (subspaceIso e n U)) (field_card_eq e)
    _ = Nat.card (subspaceIso e n U) := hL.symm
    _ = Nat.card U := subspace_natCard e n U
    _ = Fintype.card K ^ Module.finrank K U := hK

theorem inverse_subspace_finrank (e : K ≃+* L) (n : Nat)
    (U : Submodule L (V L n)) :
    Module.finrank K ((subspaceIso e n).symm U) = Module.finrank L U := by
  have h := subspace_finrank e n ((subspaceIso e n).symm U)
  have heq := congrArg (fun W : Submodule L (V L n) => Module.finrank L W)
    ((subspaceIso e n).apply_symm_apply U)
  exact h.symm.trans heq

theorem actualDesign_forward (e : K ≃+* L) (n k : Nat)
    (D : Finset (Submodule K (V K n))) (hD : Catalog.actualDesign K n k D) :
    Catalog.actualDesign L n k (familyEquiv e n D) := by
  refine ⟨hD.1, ?_, ?_⟩
  · intro W hW
    exact (inverse_subspace_finrank e n W).symm.trans
      (hD.2.1 _ ((mem_familyEquiv e n D W).1 hW))
  · intro U hU
    have hpre := (inverse_subspace_finrank e n U).trans hU
    have huniq := (unique_containing_iff e n D ((subspaceIso e n).symm U)).2
      (hD.2.2 _ hpre)
    rw [(subspaceIso e n).apply_symm_apply] at huniq
    exact huniq

theorem actualDesign_reverse (e : K ≃+* L) (n k : Nat)
    (D : Finset (Submodule K (V K n)))
    (hD : Catalog.actualDesign L n k (familyEquiv e n D)) : Catalog.actualDesign K n k D := by
  refine ⟨hD.1, ?_, ?_⟩
  · intro W hW
    exact (subspace_finrank e n W).symm.trans
      (hD.2.1 _ ((image_mem_familyEquiv e n D W).2 hW))
  · intro U hU
    exact (unique_containing_iff e n D U).1
      (hD.2.2 _ ((subspace_finrank e n U).trans hU))

theorem actualDesign_transport_iff (e : K ≃+* L) (n k : Nat)
    (D : Finset (Submodule K (V K n))) :
    Catalog.actualDesign L n k (familyEquiv e n D) ↔ Catalog.actualDesign K n k D :=
  ⟨actualDesign_reverse e n k D, actualDesign_forward e n k D⟩

def designEquiv (e : K ≃+* L) (n k : Nat) :
    {D : Finset (Submodule K (V K n)) // Catalog.actualDesign K n k D} ≃
      {D : Finset (Submodule L (V L n)) // Catalog.actualDesign L n k D} where
  toFun D := ⟨familyEquiv e n D.1, actualDesign_forward e n k D.1 D.2⟩
  invFun D := ⟨(familyEquiv e n).symm D.1,
    (actualDesign_transport_iff e n k _).1 (by
      rw [(familyEquiv e n).apply_symm_apply]
      exact D.2)⟩
  left_inv D := Subtype.ext ((familyEquiv e n).symm_apply_apply D.1)
  right_inv D := Subtype.ext ((familyEquiv e n).apply_symm_apply D.1)

theorem actualDesign_iff_exists_source_catalogue (e : K ≃+* L) (n k : Nat)
    (D : Finset (Submodule L (V L n))) :
    Catalog.actualDesign L n k D ↔ ∃ B ∈ Catalog.catalogue K n k,
      familyEquiv e n (Catalog.decode K n B) = D := by
  constructor
  · intro hD
    have hpre : Catalog.actualDesign K n k ((familyEquiv e n).symm D) :=
      (actualDesign_transport_iff e n k _).1 (by
        rw [(familyEquiv e n).apply_symm_apply]
        exact hD)
    obtain ⟨B, hB, hdec⟩ := (Catalog.actualDesign_iff_exists_catalogue K n k _).1 hpre
    refine ⟨B, hB, ?_⟩
    calc
      familyEquiv e n (Catalog.decode K n B) =
          familyEquiv e n ((familyEquiv e n).symm D) := congrArg (familyEquiv e n) hdec
      _ = D := (familyEquiv e n).apply_symm_apply D
  · rintro ⟨B, hB, hD⟩
    exact hD ▸ actualDesign_forward e n k _ (Catalog.catalogue_sound K n k B hB)

theorem actualDesign_iff_existsUnique_source_catalogue (e : K ≃+* L) (n k : Nat)
    (D : Finset (Submodule L (V L n))) :
    Catalog.actualDesign L n k D ↔ ∃! B, B ∈ Catalog.catalogue K n k ∧
      familyEquiv e n (Catalog.decode K n B) = D := by
  constructor
  · intro hD
    obtain ⟨B, hB, hBD⟩ := (actualDesign_iff_exists_source_catalogue e n k D).1 hD
    refine ⟨B, ⟨hB, hBD⟩, ?_⟩
    rintro C ⟨hC, hCD⟩
    apply Catalog.decode_injective_on_catalogue K n k C B hC hB
    exact (familyEquiv e n).injective (hCD.trans hBD.symm)
  · rintro ⟨B, hB, _⟩
    exact (actualDesign_iff_exists_source_catalogue e n k D).2 ⟨B, hB.1, hB.2⟩

end Steiner1029.Transport

#print Steiner1029.Transport.coordinates
#print axioms Steiner1029.Transport.coordinates
#print Steiner1029.Transport.subspaceIso
#print axioms Steiner1029.Transport.subspaceIso
#print Steiner1029.Transport.familyEquiv
#print axioms Steiner1029.Transport.familyEquiv
#print Steiner1029.Transport.designEquiv
#print axioms Steiner1029.Transport.designEquiv
#check @RingHomInvPair.of_ringEquiv
#print axioms RingHomInvPair.of_ringEquiv

#check @Steiner1029.Transport.coordinates_apply
#print axioms Steiner1029.Transport.coordinates_apply
#check @Steiner1029.Transport.coordinates_symm_apply
#print axioms Steiner1029.Transport.coordinates_symm_apply
#check @Steiner1029.Transport.subspace_le_iff
#print axioms Steiner1029.Transport.subspace_le_iff
#check @Steiner1029.Transport.mem_subspaceIso
#print axioms Steiner1029.Transport.mem_subspaceIso
#check @Steiner1029.Transport.mem_inverse_subspaceIso
#print axioms Steiner1029.Transport.mem_inverse_subspaceIso
#check @Steiner1029.Transport.subspace_natCard
#print axioms Steiner1029.Transport.subspace_natCard
#check @Steiner1029.Transport.mem_familyEquiv
#print axioms Steiner1029.Transport.mem_familyEquiv
#check @Steiner1029.Transport.image_mem_familyEquiv
#print axioms Steiner1029.Transport.image_mem_familyEquiv
#check @Steiner1029.Transport.family_card
#print axioms Steiner1029.Transport.family_card
#check @Steiner1029.Transport.family_roundtrip
#print axioms Steiner1029.Transport.family_roundtrip
#check @Steiner1029.Transport.family_inverse_roundtrip
#print axioms Steiner1029.Transport.family_inverse_roundtrip
#check @Steiner1029.Transport.unique_containing_iff
#print axioms Steiner1029.Transport.unique_containing_iff
#check @Steiner1029.Transport.field_card_eq
#print axioms Steiner1029.Transport.field_card_eq
#check @Steiner1029.Transport.subspace_finrank
#print axioms Steiner1029.Transport.subspace_finrank
#check @Steiner1029.Transport.inverse_subspace_finrank
#print axioms Steiner1029.Transport.inverse_subspace_finrank
#check @Steiner1029.Transport.actualDesign_forward
#print axioms Steiner1029.Transport.actualDesign_forward
#check @Steiner1029.Transport.actualDesign_reverse
#print axioms Steiner1029.Transport.actualDesign_reverse
#check @Steiner1029.Transport.actualDesign_transport_iff
#print axioms Steiner1029.Transport.actualDesign_transport_iff
#check @Steiner1029.Transport.actualDesign_iff_exists_source_catalogue
#print axioms Steiner1029.Transport.actualDesign_iff_exists_source_catalogue
#check @Steiner1029.Transport.actualDesign_iff_existsUnique_source_catalogue
#print axioms Steiner1029.Transport.actualDesign_iff_existsUnique_source_catalogue
