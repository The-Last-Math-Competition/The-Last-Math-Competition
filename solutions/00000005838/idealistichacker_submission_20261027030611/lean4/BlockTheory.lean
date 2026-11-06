import Mathlib.Algebra.Group.Idempotent
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

noncomputable section

namespace BlockTheory5838

def CentralIdempotent {R : Type*} [Ring R] (e : R) : Prop :=
  IsIdempotentElem e ∧ ∀ r : R, e * r = r * e

def PrimitiveCentral {R : Type*} [Ring R] (e : R) : Prop :=
  e ≠ 0 ∧ CentralIdempotent e ∧
    ∀ f g : R, CentralIdempotent f → CentralIdempotent g →
      f + g = e → f * g = 0 → f = 0 ∨ g = 0

def Block (R : Type*) [Ring R] := {e : R // PrimitiveCentral e}

theorem one_primitive_of_idempotents {R : Type*} [Ring R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    PrimitiveCentral (1 : R) := by
  refine ⟨one_ne_zero, ⟨IsIdempotentElem.one, ?_⟩, ?_⟩
  · intro r
    simp
  · intro f g hf _hg _hadd hmul
    rcases h f hf.1 with hf0 | hf1
    · exact Or.inl hf0
    · right
      simpa only [hf1, one_mul] using hmul

theorem block_count_one {R : Type*} [Ring R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Nat.card (Block R) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨1, one_primitive_of_idempotents h⟩, ?_⟩
  intro e
  apply Subtype.ext
  rcases h e.val e.property.2.1.1 with he0 | he1
  · exact False.elim (e.property.1 he0)
  · exact he1

theorem blocks_finite {R : Type*} [Ring R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : Finite (Block R) :=
  Nat.finite_of_card_ne_zero (by rw [block_count_one h]; decide)

theorem block_subset_finite {R : Type*} [Ring R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (P : Block R → Prop) : Finite {b : Block R // P b} := by
  let := blocks_finite h
  infer_instance

theorem no_half_count {R : Type*} [Ring R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (P : Block R → Prop) :
    2 * Nat.card {b : Block R // P b} ≠ Nat.card (Block R) := by
  rw [block_count_one h]
  omega

theorem no_half_rational {R : Type*} [Ring R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (P : Block R → Prop) :
    (Nat.card {b : Block R // P b} : ℚ) ≠ (Nat.card (Block R) : ℚ) / 2 := by
  intro he
  have hmul : (2 : ℚ) * (Nat.card {b : Block R // P b} : ℚ) =
      (Nat.card (Block R) : ℚ) := by linarith
  have hn : 2 * Nat.card {b : Block R // P b} = Nat.card (Block R) := by
    exact_mod_cast hmul
  exact no_half_count h P hn

theorem idempotents_of_ringEquiv {R S : Type*} [Ring R] [Ring S]
    (f : R ≃+* S) (h : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) :
    ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  intro e he
  have hi : IsIdempotentElem (f e) := by
    rw [IsIdempotentElem, ← map_mul, he.eq]
  rcases h (f e) hi with h0 | h1
  · left
    apply f.injective
    simpa only [map_zero] using h0
  · right
    apply f.injective
    simpa only [map_one] using h1

end BlockTheory5838
