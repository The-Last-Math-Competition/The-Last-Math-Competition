import CarrierCodes

namespace Steiner1029.Catalog

universe u

theorem filter_card_eq_one_iff {α : Type u} (B : Finset α) (p : α → Prop)
    [DecidablePred p] : (B.filter p).card = 1 ↔ ∃! W, W ∈ B ∧ p W := by
  simp only [Finset.card_eq_one_iff_existsUnique, Finset.mem_filter]

variable (K : Type u) [Field K] [Fintype K] [DecidableEq K] (n : Nat)

def IncidenceClosed (B : Finset (Finset (V K n))) : Prop :=
  ∀ U ∈ dimCarriers K n 2, (B.filter (fun W => U ⊆ W)).card = 1

instance instDecidablePredIncidenceClosed : DecidablePred (IncidenceClosed K n) :=
  fun B => by
    unfold IncidenceClosed
    infer_instance

def catalogue (k : Nat) : Finset (Finset (Finset (V K n))) :=
  if 2 ≤ k ∧ k ≤ n then
    (dimCarriers K n k).powerset.filter (IncidenceClosed K n)
  else ∅

def actualDesign (K : Type u) [Field K] [Fintype K] [DecidableEq K]
    (n k : Nat) (D : Finset (Submodule K (V K n))) : Prop :=
  (2 ≤ k ∧ k ≤ n) ∧
    (∀ W ∈ D, Module.finrank K W = k) ∧
    (∀ U : Submodule K (V K n), Module.finrank K U = 2 →
      ∃! W, W ∈ D ∧ U ≤ W)

theorem mem_catalogue (k : Nat) (B : Finset (Finset (V K n))) :
    B ∈ catalogue K n k ↔
      (2 ≤ k ∧ k ≤ n) ∧ B ⊆ dimCarriers K n k ∧ IncidenceClosed K n B := by
  by_cases hg : 2 ≤ k ∧ k ≤ n
  · simp [catalogue, hg]
  · simp [catalogue, hg]

theorem catalogue_eq_empty_of_invalid (k : Nat) (hg : ¬(2 ≤ k ∧ k ≤ n)) :
    catalogue K n k = ∅ := by
  simp [catalogue, hg]

theorem catalogue_zero_zero : catalogue K 0 0 = ∅ := by
  simp [catalogue]

theorem not_actualDesign_of_invalid (k : Nat) (D : Finset (Submodule K (V K n)))
    (hg : ¬(2 ≤ k ∧ k ≤ n)) : ¬actualDesign K n k D :=
  fun hD => hg hD.1

-- Total semantic decoding. The fallback is proved unreachable on catalogue blocks.
def decodeBlock (s : Finset (V K n)) : Submodule K (V K n) :=
  if hs : CarrierClosed K n s then toSubmodule K n s hs else ⊥

theorem decodeBlock_of_closed (s : Finset (V K n)) (hs : CarrierClosed K n s) :
    decodeBlock K n s = toSubmodule K n s hs := by
  simp only [decodeBlock, dif_pos hs]

theorem decodeBlock_ofSubmodule (U : Submodule K (V K n)) :
    decodeBlock K n (ofSubmodule K n U) = U := by
  rw [decodeBlock_of_closed K n _ (ofSubmodule_closed K n U)]
  exact toSubmodule_ofSubmodule K n U

theorem ofSubmodule_decodeBlock (s : Finset (V K n)) (hs : CarrierClosed K n s) :
    ofSubmodule K n (decodeBlock K n s) = s := by
  rw [decodeBlock_of_closed K n s hs]
  exact ofSubmodule_toSubmodule K n s hs

theorem ofSubmodule_injective : Function.Injective (ofSubmodule K n) := by
  intro U W h
  calc
    U = decodeBlock K n (ofSubmodule K n U) := (decodeBlock_ofSubmodule K n U).symm
    _ = decodeBlock K n (ofSubmodule K n W) := congrArg (decodeBlock K n) h
    _ = W := decodeBlock_ofSubmodule K n W

-- Family encoding and decoding are proof-side only, not catalogue dependencies.
noncomputable def encode (D : Finset (Submodule K (V K n))) :
    Finset (Finset (V K n)) :=
  D.image (ofSubmodule K n)

noncomputable def decode (B : Finset (Finset (V K n))) :
    Finset (Submodule K (V K n)) := by
  classical
  exact B.image (decodeBlock K n)

theorem mem_encode (D : Finset (Submodule K (V K n))) (s : Finset (V K n)) :
    s ∈ encode K n D ↔ ∃ W ∈ D, ofSubmodule K n W = s := by
  classical
  exact Finset.mem_image

theorem mem_decode (B : Finset (Finset (V K n))) (U : Submodule K (V K n)) :
    U ∈ decode K n B ↔ ∃ s ∈ B, decodeBlock K n s = U := by
  classical
  exact Finset.mem_image

theorem decode_encode (D : Finset (Submodule K (V K n))) :
    decode K n (encode K n D) = D := by
  classical
  ext U
  constructor
  · intro hU
    obtain ⟨s, hs, hsU⟩ := (mem_decode K n _ U).1 hU
    obtain ⟨W, hW, hWs⟩ := (mem_encode K n D s).1 hs
    have hWU : W = U := by
      calc
        W = decodeBlock K n (ofSubmodule K n W) := (decodeBlock_ofSubmodule K n W).symm
        _ = decodeBlock K n s := congrArg (decodeBlock K n) hWs
        _ = U := hsU
    exact hWU ▸ hW
  · intro hU
    exact (mem_decode K n _ U).2 ⟨ofSubmodule K n U,
      (mem_encode K n D _).2 ⟨U, hU, rfl⟩, decodeBlock_ofSubmodule K n U⟩

theorem encode_decode (B : Finset (Finset (V K n)))
    (hB : ∀ s ∈ B, CarrierClosed K n s) : encode K n (decode K n B) = B := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨U, hU, hUs⟩ := (mem_encode K n _ s).1 hs
    obtain ⟨t, ht, htU⟩ := (mem_decode K n B U).1 hU
    have hts : t = s := by
      calc
        t = ofSubmodule K n (decodeBlock K n t) := (ofSubmodule_decodeBlock K n t (hB t ht)).symm
        _ = ofSubmodule K n U := congrArg (ofSubmodule K n) htU
        _ = s := hUs
    exact hts ▸ ht
  · intro hs
    exact (mem_encode K n _ s).2 ⟨decodeBlock K n s,
      (mem_decode K n B _).2 ⟨s, hs, rfl⟩, ofSubmodule_decodeBlock K n s (hB s hs)⟩

theorem encode_injective : Function.Injective (encode K n) := by
  intro D E h
  calc
    D = decode K n (encode K n D) := (decode_encode K n D).symm
    _ = decode K n (encode K n E) := congrArg (decode K n) h
    _ = E := decode_encode K n E

theorem encode_subset_dim_iff (k : Nat) (D : Finset (Submodule K (V K n))) :
    encode K n D ⊆ dimCarriers K n k ↔ ∀ W ∈ D, Module.finrank K W = k := by
  constructor
  · intro h W hW
    exact (ofSubmodule_mem_dimCarriers K n k W).1
      (h ((mem_encode K n D _).2 ⟨W, hW, rfl⟩))
  · intro h s hs
    obtain ⟨W, hW, rfl⟩ := (mem_encode K n D s).1 hs
    exact (ofSubmodule_mem_dimCarriers K n k W).2 (h W hW)

theorem unique_containing_encode_iff (D : Finset (Submodule K (V K n)))
    (U : Submodule K (V K n)) :
    (∃! s, s ∈ encode K n D ∧ ofSubmodule K n U ⊆ s) ↔
      ∃! W, W ∈ D ∧ U ≤ W := by
  constructor
  · rintro ⟨s, ⟨hs, hUs⟩, huniq⟩
    obtain ⟨W, hW, rfl⟩ := (mem_encode K n D s).1 hs
    refine ⟨W, ⟨hW, (ofSubmodule_subset_iff K n U W).1 hUs⟩, ?_⟩
    intro W' hW'
    apply ofSubmodule_injective K n
    exact huniq (ofSubmodule K n W') ⟨(mem_encode K n D _).2 ⟨W', hW'.1, rfl⟩,
      (ofSubmodule_subset_iff K n U W').2 hW'.2⟩
  · rintro ⟨W, ⟨hW, hUW⟩, huniq⟩
    refine ⟨ofSubmodule K n W, ⟨(mem_encode K n D _).2 ⟨W, hW, rfl⟩,
      (ofSubmodule_subset_iff K n U W).2 hUW⟩, ?_⟩
    rintro s ⟨hs, hUs⟩
    obtain ⟨W', hW', rfl⟩ := (mem_encode K n D s).1 hs
    exact congrArg (ofSubmodule K n)
      (huniq W' ⟨hW', (ofSubmodule_subset_iff K n U W').1 hUs⟩)

theorem incidence_encode_iff (D : Finset (Submodule K (V K n))) :
    IncidenceClosed K n (encode K n D) ↔
      ∀ U : Submodule K (V K n), Module.finrank K U = 2 → ∃! W, W ∈ D ∧ U ≤ W := by
  constructor
  · intro h U hU
    apply (unique_containing_encode_iff K n D U).1
    apply (filter_card_eq_one_iff (encode K n D) (fun W => ofSubmodule K n U ⊆ W)).1
    exact h _ ((ofSubmodule_mem_dimCarriers K n 2 U).2 hU)
  · intro h s hs
    obtain ⟨U, hU, rfl⟩ := (mem_dimCarriers_iff_exists_submodule K n 2 s).1 hs
    apply (filter_card_eq_one_iff (encode K n D) (fun W => ofSubmodule K n U ⊆ W)).2
    exact (unique_containing_encode_iff K n D U).2 (h U hU)

theorem encode_mem_catalogue_iff (k : Nat) (D : Finset (Submodule K (V K n))) :
    encode K n D ∈ catalogue K n k ↔ actualDesign K n k D := by
  simp only [mem_catalogue, encode_subset_dim_iff, incidence_encode_iff, actualDesign]

theorem catalogue_block_closed (k : Nat) (B : Finset (Finset (V K n)))
    (hB : B ∈ catalogue K n k) : ∀ s ∈ B, CarrierClosed K n s := by
  intro s hs
  exact ((mem_dimCarriers K n k s).1 (((mem_catalogue K n k B).1 hB).2.1 hs)).1

theorem catalogue_sound (k : Nat) (B : Finset (Finset (V K n)))
    (hB : B ∈ catalogue K n k) : actualDesign K n k (decode K n B) := by
  apply (encode_mem_catalogue_iff K n k _).1
  rw [encode_decode K n B (catalogue_block_closed K n k B hB)]
  exact hB

theorem catalogue_complete (k : Nat) (D : Finset (Submodule K (V K n)))
    (hD : actualDesign K n k D) : encode K n D ∈ catalogue K n k :=
  (encode_mem_catalogue_iff K n k D).2 hD

theorem decode_injective_on_catalogue (k : Nat) (B C : Finset (Finset (V K n)))
    (hB : B ∈ catalogue K n k) (hC : C ∈ catalogue K n k)
    (h : decode K n B = decode K n C) : B = C := by
  calc
    B = encode K n (decode K n B) :=
      (encode_decode K n B (catalogue_block_closed K n k B hB)).symm
    _ = encode K n (decode K n C) := congrArg (encode K n) h
    _ = C := encode_decode K n C (catalogue_block_closed K n k C hC)

theorem actualDesign_iff_exists_catalogue (k : Nat) (D : Finset (Submodule K (V K n))) :
    actualDesign K n k D ↔ ∃ B ∈ catalogue K n k, decode K n B = D := by
  constructor
  · intro hD
    exact ⟨encode K n D, catalogue_complete K n k D hD, decode_encode K n D⟩
  · rintro ⟨B, hB, hD⟩
    exact hD ▸ catalogue_sound K n k B hB

theorem actualDesign_iff_existsUnique_catalogue (k : Nat)
    (D : Finset (Submodule K (V K n))) :
    actualDesign K n k D ↔ ∃! B, B ∈ catalogue K n k ∧ decode K n B = D := by
  constructor
  · intro hD
    refine ⟨encode K n D, ⟨catalogue_complete K n k D hD, decode_encode K n D⟩, ?_⟩
    rintro B ⟨hB, hBD⟩
    calc
      B = encode K n (decode K n B) :=
        (encode_decode K n B (catalogue_block_closed K n k B hB)).symm
      _ = encode K n D := congrArg (encode K n) hBD
  · rintro ⟨B, hB, _⟩
    exact hB.2 ▸ catalogue_sound K n k B hB.1

theorem divisible_actualDesign_iff_exists_catalogue (k : Nat) (_hdiv : k ∣ n)
    (D : Finset (Submodule K (V K n))) :
    actualDesign K n k D ↔ ∃ B ∈ catalogue K n k, decode K n B = D :=
  actualDesign_iff_exists_catalogue K n k D

end Steiner1029.Catalog

#print Steiner1029.Catalog.IncidenceClosed
#print axioms Steiner1029.Catalog.IncidenceClosed
set_option pp.explicit true in
#print Steiner1029.Catalog.instDecidablePredIncidenceClosed
#print axioms Steiner1029.Catalog.instDecidablePredIncidenceClosed
set_option pp.explicit true in
#print Steiner1029.Catalog.catalogue
#print axioms Steiner1029.Catalog.catalogue
#print Steiner1029.Catalog.actualDesign
#print axioms Steiner1029.Catalog.actualDesign
#print Steiner1029.Catalog.decodeBlock
#print axioms Steiner1029.Catalog.decodeBlock
#print Steiner1029.Catalog.encode
#print axioms Steiner1029.Catalog.encode
#print Steiner1029.Catalog.decode
#print axioms Steiner1029.Catalog.decode

#check @Steiner1029.Catalog.filter_card_eq_one_iff
#print axioms Steiner1029.Catalog.filter_card_eq_one_iff
#check @Steiner1029.Catalog.mem_catalogue
#print axioms Steiner1029.Catalog.mem_catalogue
#check @Steiner1029.Catalog.catalogue_eq_empty_of_invalid
#print axioms Steiner1029.Catalog.catalogue_eq_empty_of_invalid
#check @Steiner1029.Catalog.catalogue_zero_zero
#print axioms Steiner1029.Catalog.catalogue_zero_zero
#check @Steiner1029.Catalog.not_actualDesign_of_invalid
#print axioms Steiner1029.Catalog.not_actualDesign_of_invalid
#check @Steiner1029.Catalog.decodeBlock_of_closed
#print axioms Steiner1029.Catalog.decodeBlock_of_closed
#check @Steiner1029.Catalog.decodeBlock_ofSubmodule
#print axioms Steiner1029.Catalog.decodeBlock_ofSubmodule
#check @Steiner1029.Catalog.ofSubmodule_decodeBlock
#print axioms Steiner1029.Catalog.ofSubmodule_decodeBlock
#check @Steiner1029.Catalog.ofSubmodule_injective
#print axioms Steiner1029.Catalog.ofSubmodule_injective
#check @Steiner1029.Catalog.mem_encode
#print axioms Steiner1029.Catalog.mem_encode
#check @Steiner1029.Catalog.mem_decode
#print axioms Steiner1029.Catalog.mem_decode
#check @Steiner1029.Catalog.decode_encode
#print axioms Steiner1029.Catalog.decode_encode
#check @Steiner1029.Catalog.encode_decode
#print axioms Steiner1029.Catalog.encode_decode
#check @Steiner1029.Catalog.encode_injective
#print axioms Steiner1029.Catalog.encode_injective
#check @Steiner1029.Catalog.encode_subset_dim_iff
#print axioms Steiner1029.Catalog.encode_subset_dim_iff
#check @Steiner1029.Catalog.unique_containing_encode_iff
#print axioms Steiner1029.Catalog.unique_containing_encode_iff
#check @Steiner1029.Catalog.incidence_encode_iff
#print axioms Steiner1029.Catalog.incidence_encode_iff
#check @Steiner1029.Catalog.encode_mem_catalogue_iff
#print axioms Steiner1029.Catalog.encode_mem_catalogue_iff
#check @Steiner1029.Catalog.catalogue_block_closed
#print axioms Steiner1029.Catalog.catalogue_block_closed
#check @Steiner1029.Catalog.catalogue_sound
#print axioms Steiner1029.Catalog.catalogue_sound
#check @Steiner1029.Catalog.catalogue_complete
#print axioms Steiner1029.Catalog.catalogue_complete
#check @Steiner1029.Catalog.decode_injective_on_catalogue
#print axioms Steiner1029.Catalog.decode_injective_on_catalogue
#check @Steiner1029.Catalog.actualDesign_iff_exists_catalogue
#print axioms Steiner1029.Catalog.actualDesign_iff_exists_catalogue
#check @Steiner1029.Catalog.actualDesign_iff_existsUnique_catalogue
#print axioms Steiner1029.Catalog.actualDesign_iff_existsUnique_catalogue
#check @Steiner1029.Catalog.divisible_actualDesign_iff_exists_catalogue
#print axioms Steiner1029.Catalog.divisible_actualDesign_iff_exists_catalogue
