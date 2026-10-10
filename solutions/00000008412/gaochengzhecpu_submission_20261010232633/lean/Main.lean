import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Conjecture8412

abbrev G := ZMod 3 × ZMod 3 × ZMod 3

def D : Finset G :=
  {(0, 0, 1), (0, 1, 0), (0, 1, 1), (0, 1, 2),
   (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1),
   (1, 2, 0), (1, 2, 2), (2, 0, 1), (2, 1, 2), (2, 2, 1)}

def differenceCount (S : Finset G) (g : G) : ℕ :=
  ((S.product S).filter (fun p => p.1 - p.2 = g)).card

/-- The standard ordered-difference definition, using the actual ambient group. -/
def IsDifferenceSet (S : Finset G) (v k lam : ℕ) : Prop :=
  Fintype.card G = v ∧ S.card = k ∧
    ∀ g : G, g ≠ 0 → differenceCount S g = lam

theorem difference_set : IsDifferenceSet D 27 13 6 := by
  unfold IsDifferenceSet
  decide +kernel

/-- The coordinate cycle is an actual additive group automorphism. -/
def cycle : G ≃+ G where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun x := (x.2.2, x.1, x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem cycle_cubed (x : G) : cycle (cycle (cycle x)) = x := rfl

theorem fixes_difference_set : D.image cycle = D := by decide +kernel

def translate (a : G) (S : Finset G) : Finset G := S.image (a + ·)

/-- Multipliers allow a translate; setwise fixing is sufficient but not required. -/
def IsMultiplier (S : Finset G) (σ : G ≃+ G) : Prop :=
  ∃ a : G, S.image σ = translate a S

/-- Every numerical multiplier is integer scalar multiplication on the group. -/
def IsNumerical (σ : G ≃+ G) : Prop :=
  ∃ n : ℤ, ∀ x : G, σ x = n • x

theorem cycle_is_multiplier : IsMultiplier D cycle := by
  refine ⟨0, ?_⟩
  simpa [translate] using fixes_difference_set

theorem cycle_not_numerical : ¬ IsNumerical cycle := by
  rintro ⟨n, hn⟩
  have h := congrArg (fun x : G => x.2.2) (hn (1, 0, 0))
  simp [cycle] at h

theorem group_order : Nat.card G = 27 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- No subgroup quotient of this group can even have even order. -/
theorem no_even_section (S : AddSubgroup G) (K : AddSubgroup S) :
    ¬ 2 ∣ Nat.card (S ⧸ K) := by
  intro h
  have hd := h.trans (K.card_quotient_dvd_card.trans S.card_addSubgroup_dvd_card)
  rw [group_order] at hd
  norm_num at hd

theorem no_index_two_subgroup (S : AddSubgroup G) : S.index ≠ 2 := by
  intro h
  have hd := S.index_dvd_card
  rw [h, group_order] at hd
  norm_num at hd

theorem not_exception_orders : Nat.card G ≠ 16 ∧ Nat.card G ≠ 32 := by
  rw [group_order]
  decide

theorem no_exception_section (S : AddSubgroup G) (K : AddSubgroup S) :
    Nat.card (S ⧸ K) ≠ 16 ∧ Nat.card (S ⧸ K) ≠ 32 := by
  constructor
  · intro h
    have hd := no_even_section S K
    rw [h] at hd
    norm_num at hd
  · intro h
    have hd := no_even_section S K
    rw [h] at hd
    norm_num at hd

theorem counterexample :
    IsDifferenceSet D 27 13 6 ∧
    IsMultiplier D cycle ∧ ¬ IsNumerical cycle ∧
    Nat.card G ≠ 16 ∧ Nat.card G ≠ 32 ∧
    (∀ S : AddSubgroup G, S.index ≠ 2) ∧
    (∀ (S : AddSubgroup G) (K : AddSubgroup S),
      Nat.card (S ⧸ K) ≠ 16 ∧ Nat.card (S ⧸ K) ≠ 32) := by
  exact ⟨difference_set, cycle_is_multiplier, cycle_not_numerical,
    not_exception_orders.1, not_exception_orders.2,
    no_index_two_subgroup, no_exception_section⟩

end Conjecture8412

#print axioms Conjecture8412.difference_set
#print axioms Conjecture8412.cycle_not_numerical
#print axioms Conjecture8412.no_exception_section
#print axioms Conjecture8412.counterexample
