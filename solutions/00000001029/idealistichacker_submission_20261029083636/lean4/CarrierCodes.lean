import Mathlib.Data.Finset.Powerset
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic

namespace Steiner1029

universe u

abbrev V (K : Type u) (n : Nat) := Fin n → K

def CarrierClosed (K : Type u) [Field K] [Fintype K] [DecidableEq K]
    (n : Nat) (s : Finset (V K n)) : Prop :=
  (0 : V K n) ∈ s ∧
    (∀ x ∈ s, ∀ y ∈ s, x + y ∈ s) ∧
    (∀ a : K, ∀ x ∈ s, a • x ∈ s)

instance instDecidablePredCarrierClosed (K : Type u) [Field K] [Fintype K]
    [DecidableEq K] (n : Nat) : DecidablePred (CarrierClosed K n) :=
  fun s => by
    unfold CarrierClosed
    infer_instance

variable (K : Type u) [Field K] [Fintype K] [DecidableEq K] (n : Nat)

def allCarriers : Finset (Finset (V K n)) :=
  (Finset.univ : Finset (V K n)).powerset.filter (CarrierClosed K n)

theorem mem_allCarriers (s : Finset (V K n)) :
    s ∈ allCarriers K n ↔ CarrierClosed K n s := by
  simp [allCarriers]

def toSubmodule (s : Finset (V K n)) (hClosed : CarrierClosed K n s) :
    Submodule K (V K n) where
  carrier := {x | x ∈ s}
  zero_mem' := hClosed.1
  add_mem' := fun hx hy => hClosed.2.1 _ hx _ hy
  smul_mem' := fun a x hx => hClosed.2.2 a x hx

@[simp] theorem mem_toSubmodule (s : Finset (V K n)) (hClosed : CarrierClosed K n s)
    (x : V K n) : x ∈ toSubmodule K n s hClosed ↔ x ∈ s :=
  Iff.rfl

theorem zero_mem_toSubmodule (s : Finset (V K n)) (hClosed : CarrierClosed K n s) :
    (0 : V K n) ∈ toSubmodule K n s hClosed :=
  (toSubmodule K n s hClosed).zero_mem

theorem add_mem_toSubmodule (s : Finset (V K n)) (hClosed : CarrierClosed K n s)
    {x y : V K n} (hx : x ∈ toSubmodule K n s hClosed)
    (hy : y ∈ toSubmodule K n s hClosed) :
    x + y ∈ toSubmodule K n s hClosed :=
  (toSubmodule K n s hClosed).add_mem hx hy

theorem smul_mem_toSubmodule (s : Finset (V K n)) (hClosed : CarrierClosed K n s)
    (a : K) {x : V K n} (hx : x ∈ toSubmodule K n s hClosed) :
    a • x ∈ toSubmodule K n s hClosed :=
  (toSubmodule K n s hClosed).smul_mem a hx

-- Proof-only encoding; no executable enumeration depends on this definition.
noncomputable def ofSubmodule (U : Submodule K (V K n)) : Finset (V K n) := by
  classical
  exact Finset.univ.filter (fun x => x ∈ U)

omit [DecidableEq K] in
@[simp] theorem mem_ofSubmodule (U : Submodule K (V K n)) (x : V K n) :
    x ∈ ofSubmodule K n U ↔ x ∈ U := by
  classical
  simp [ofSubmodule]

theorem ofSubmodule_closed (U : Submodule K (V K n)) :
    CarrierClosed K n (ofSubmodule K n U) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_ofSubmodule K n U 0).2 U.zero_mem
  · intro x hx y hy
    exact (mem_ofSubmodule K n U (x + y)).2
      (U.add_mem ((mem_ofSubmodule K n U x).1 hx) ((mem_ofSubmodule K n U y).1 hy))
  · intro a x hx
    exact (mem_ofSubmodule K n U (a • x)).2
      (U.smul_mem a ((mem_ofSubmodule K n U x).1 hx))

theorem ofSubmodule_mem_allCarriers (U : Submodule K (V K n)) :
    ofSubmodule K n U ∈ allCarriers K n :=
  (mem_allCarriers K n _).2 (ofSubmodule_closed K n U)

@[simp] theorem toSubmodule_ofSubmodule (U : Submodule K (V K n)) :
    toSubmodule K n (ofSubmodule K n U) (ofSubmodule_closed K n U) = U := by
  ext x
  exact mem_ofSubmodule K n U x

@[simp] theorem ofSubmodule_toSubmodule (s : Finset (V K n))
    (hClosed : CarrierClosed K n s) :
    ofSubmodule K n (toSubmodule K n s hClosed) = s := by
  ext x
  exact mem_ofSubmodule K n (toSubmodule K n s hClosed) x

theorem existsUnique_carrier (U : Submodule K (V K n)) :
    ∃! s : Finset (V K n), ∃ hClosed : CarrierClosed K n s,
      toSubmodule K n s hClosed = U := by
  refine ⟨ofSubmodule K n U, ⟨ofSubmodule_closed K n U, toSubmodule_ofSubmodule K n U⟩, ?_⟩
  intro s hs
  obtain ⟨hClosed, hU⟩ := hs
  calc
    s = ofSubmodule K n (toSubmodule K n s hClosed) :=
      (ofSubmodule_toSubmodule K n s hClosed).symm
    _ = ofSubmodule K n U := congrArg (ofSubmodule K n) hU

theorem toSubmodule_eq_iff (s t : Finset (V K n))
    (hs : CarrierClosed K n s) (ht : CarrierClosed K n t) :
    toSubmodule K n s hs = toSubmodule K n t ht ↔ s = t := by
  constructor
  · intro h
    calc
      s = ofSubmodule K n (toSubmodule K n s hs) :=
        (ofSubmodule_toSubmodule K n s hs).symm
      _ = ofSubmodule K n (toSubmodule K n t ht) := congrArg (ofSubmodule K n) h
      _ = t := ofSubmodule_toSubmodule K n t ht
  · intro h
    subst t
    rfl

theorem subset_iff_toSubmodule_le (s t : Finset (V K n))
    (hs : CarrierClosed K n s) (ht : CarrierClosed K n t) :
    s ⊆ t ↔ toSubmodule K n s hs ≤ toSubmodule K n t ht :=
  Iff.rfl

omit [DecidableEq K] in
theorem ofSubmodule_subset_iff (U W : Submodule K (V K n)) :
    ofSubmodule K n U ⊆ ofSubmodule K n W ↔ U ≤ W := by
  constructor
  · intro h x hx
    exact (mem_ofSubmodule K n W x).1 (h ((mem_ofSubmodule K n U x).2 hx))
  · intro h x hx
    exact (mem_ofSubmodule K n W x).2 (h ((mem_ofSubmodule K n U x).1 hx))

def carrierEquiv (s : Finset (V K n)) (hClosed : CarrierClosed K n s) :
    s ≃ toSubmodule K n s hClosed where
  toFun := fun x => ⟨x.1, x.2⟩
  invFun := fun x => ⟨x.1, x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance instFintypeToSubmodule (s : Finset (V K n)) (hClosed : CarrierClosed K n s) :
    Fintype (toSubmodule K n s hClosed) :=
  Fintype.ofEquiv s (carrierEquiv K n s hClosed)

theorem card_eq_fintype_card_toSubmodule (s : Finset (V K n))
    (hClosed : CarrierClosed K n s) :
    s.card = Fintype.card (toSubmodule K n s hClosed) :=
  (Fintype.card_coe s).symm.trans (Fintype.card_congr (carrierEquiv K n s hClosed))

theorem card_eq_natCard_toSubmodule (s : Finset (V K n))
    (hClosed : CarrierClosed K n s) :
    s.card = Nat.card (toSubmodule K n s hClosed) :=
  (card_eq_fintype_card_toSubmodule K n s hClosed).trans Fintype.card_eq_nat_card

theorem card_eq_pow_finrank (s : Finset (V K n)) (hClosed : CarrierClosed K n s) :
    s.card = Fintype.card K ^ Module.finrank K (toSubmodule K n s hClosed) :=
  (card_eq_fintype_card_toSubmodule K n s hClosed).trans
    (Module.card_eq_pow_finrank (K := K) (V := toSubmodule K n s hClosed))

omit [DecidableEq K] in
theorem field_card_two_le : 2 ≤ Fintype.card K :=
  Fintype.one_lt_card

theorem card_eq_pow_iff_finrank (s : Finset (V K n))
    (hClosed : CarrierClosed K n s) (d : Nat) :
    s.card = Fintype.card K ^ d ↔ Module.finrank K (toSubmodule K n s hClosed) = d := by
  rw [card_eq_pow_finrank K n s hClosed]
  exact (Nat.pow_right_injective (field_card_two_le K)).eq_iff

theorem ofSubmodule_card_eq_natCard (U : Submodule K (V K n)) :
    (ofSubmodule K n U).card = Nat.card U := by
  have h := card_eq_natCard_toSubmodule K n (ofSubmodule K n U) (ofSubmodule_closed K n U)
  simpa only [toSubmodule_ofSubmodule] using h

theorem ofSubmodule_card_eq_pow_finrank (U : Submodule K (V K n)) :
    (ofSubmodule K n U).card = Fintype.card K ^ Module.finrank K U := by
  have h := card_eq_pow_finrank K n (ofSubmodule K n U) (ofSubmodule_closed K n U)
  have hdim := congrArg (fun W : Submodule K (V K n) => Module.finrank K W)
    (toSubmodule_ofSubmodule K n U)
  exact h.trans (congrArg (fun r : Nat => Fintype.card K ^ r) hdim)

def dimCarriers (d : Nat) : Finset (Finset (V K n)) :=
  (allCarriers K n).filter (fun s => s.card = Fintype.card K ^ d)

theorem mem_dimCarriers (d : Nat) (s : Finset (V K n)) :
    s ∈ dimCarriers K n d ↔ CarrierClosed K n s ∧ s.card = Fintype.card K ^ d := by
  simp [dimCarriers, mem_allCarriers]

theorem mem_dimCarriers_iff_finrank (d : Nat) (s : Finset (V K n))
    (hClosed : CarrierClosed K n s) :
    s ∈ dimCarriers K n d ↔ Module.finrank K (toSubmodule K n s hClosed) = d := by
  rw [mem_dimCarriers]
  exact ⟨fun h => (card_eq_pow_iff_finrank K n s hClosed d).1 h.2,
    fun h => ⟨hClosed, (card_eq_pow_iff_finrank K n s hClosed d).2 h⟩⟩

theorem ofSubmodule_mem_dimCarriers (d : Nat) (U : Submodule K (V K n)) :
    ofSubmodule K n U ∈ dimCarriers K n d ↔ Module.finrank K U = d := by
  have h := mem_dimCarriers_iff_finrank K n d (ofSubmodule K n U) (ofSubmodule_closed K n U)
  have hdim := congrArg (fun W : Submodule K (V K n) => Module.finrank K W)
    (toSubmodule_ofSubmodule K n U)
  exact h.trans ⟨fun heq => hdim.symm.trans heq, fun heq => hdim.trans heq⟩

theorem mem_dimCarriers_iff_exists_submodule (d : Nat) (s : Finset (V K n)) :
    s ∈ dimCarriers K n d ↔ ∃ U : Submodule K (V K n),
      Module.finrank K U = d ∧ ofSubmodule K n U = s := by
  constructor
  · intro hs
    have hClosed := (mem_dimCarriers K n d s).1 hs |>.1
    exact ⟨toSubmodule K n s hClosed,
      (mem_dimCarriers_iff_finrank K n d s hClosed).1 hs,
      ofSubmodule_toSubmodule K n s hClosed⟩
  · rintro ⟨U, hdim, rfl⟩
    exact (ofSubmodule_mem_dimCarriers K n d U).2 hdim

end Steiner1029

-- Actual elaborated signatures and transitive axioms are emitted on every run.
#print Steiner1029.V
#print axioms Steiner1029.V
#print Steiner1029.CarrierClosed
#print axioms Steiner1029.CarrierClosed
set_option pp.explicit true in
#print Steiner1029.instDecidablePredCarrierClosed
#print axioms Steiner1029.instDecidablePredCarrierClosed
set_option pp.explicit true in
#print Steiner1029.allCarriers
#print axioms Steiner1029.allCarriers
#print Steiner1029.toSubmodule
#print axioms Steiner1029.toSubmodule
#print Steiner1029.ofSubmodule
#print axioms Steiner1029.ofSubmodule
#print Steiner1029.carrierEquiv
#print axioms Steiner1029.carrierEquiv
#print Steiner1029.instFintypeToSubmodule
#print axioms Steiner1029.instFintypeToSubmodule
set_option pp.explicit true in
#print Steiner1029.dimCarriers
#print axioms Steiner1029.dimCarriers

#check @Steiner1029.mem_allCarriers
#print axioms Steiner1029.mem_allCarriers
#check @Steiner1029.mem_toSubmodule
#print axioms Steiner1029.mem_toSubmodule
#check @Steiner1029.zero_mem_toSubmodule
#print axioms Steiner1029.zero_mem_toSubmodule
#check @Steiner1029.add_mem_toSubmodule
#print axioms Steiner1029.add_mem_toSubmodule
#check @Steiner1029.smul_mem_toSubmodule
#print axioms Steiner1029.smul_mem_toSubmodule
#check @Steiner1029.mem_ofSubmodule
#print axioms Steiner1029.mem_ofSubmodule
#check @Steiner1029.ofSubmodule_closed
#print axioms Steiner1029.ofSubmodule_closed
#check @Steiner1029.ofSubmodule_mem_allCarriers
#print axioms Steiner1029.ofSubmodule_mem_allCarriers
#check @Steiner1029.toSubmodule_ofSubmodule
#print axioms Steiner1029.toSubmodule_ofSubmodule
#check @Steiner1029.ofSubmodule_toSubmodule
#print axioms Steiner1029.ofSubmodule_toSubmodule
#check @Steiner1029.existsUnique_carrier
#print axioms Steiner1029.existsUnique_carrier
#check @Steiner1029.toSubmodule_eq_iff
#print axioms Steiner1029.toSubmodule_eq_iff
#check @Steiner1029.subset_iff_toSubmodule_le
#print axioms Steiner1029.subset_iff_toSubmodule_le
#check @Steiner1029.ofSubmodule_subset_iff
#print axioms Steiner1029.ofSubmodule_subset_iff
#check @Steiner1029.card_eq_fintype_card_toSubmodule
#print axioms Steiner1029.card_eq_fintype_card_toSubmodule
#check @Steiner1029.card_eq_natCard_toSubmodule
#print axioms Steiner1029.card_eq_natCard_toSubmodule
#check @Steiner1029.card_eq_pow_finrank
#print axioms Steiner1029.card_eq_pow_finrank
#check @Steiner1029.field_card_two_le
#print axioms Steiner1029.field_card_two_le
#check @Steiner1029.card_eq_pow_iff_finrank
#print axioms Steiner1029.card_eq_pow_iff_finrank
#check @Steiner1029.ofSubmodule_card_eq_natCard
#print axioms Steiner1029.ofSubmodule_card_eq_natCard
#check @Steiner1029.ofSubmodule_card_eq_pow_finrank
#print axioms Steiner1029.ofSubmodule_card_eq_pow_finrank
#check @Steiner1029.mem_dimCarriers
#print axioms Steiner1029.mem_dimCarriers
#check @Steiner1029.mem_dimCarriers_iff_finrank
#print axioms Steiner1029.mem_dimCarriers_iff_finrank
#check @Steiner1029.ofSubmodule_mem_dimCarriers
#print axioms Steiner1029.ofSubmodule_mem_dimCarriers
#check @Steiner1029.mem_dimCarriers_iff_exists_submodule
#print axioms Steiner1029.mem_dimCarriers_iff_exists_submodule
