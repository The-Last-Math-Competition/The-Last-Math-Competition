import Conjecture2899.Geometry
import Conjecture2899.Squares
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Conjecture2899

noncomputable def slice (F : Type*) [Field F] [Fintype F] (x : F) : Finset F := by
  classical
  exact Finset.univ.filter (fun y => x = 0 ∨ ∃ z : F, y + x^2 = z^2)

noncomputable def familyEquiv (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    ↥(family F n) ≃ (Σ x : F, ↥(slice F x)) × (Fin n → F) where
  toFun w := (⟨w.1 0, ⟨w.1 1, by
    classical
    simpa [slice] using (mem_family w.1).1 w.2⟩⟩, Fin.tail (Fin.tail w.1))
  invFun w := ⟨Fin.cons w.1.1 (Fin.cons w.1.2.1 w.2), by
    classical
    apply (mem_family _).2
    have hh := w.1.2.2
    change _ ∈ Finset.univ.filter _ at hh
    exact (Finset.mem_filter.mp hh).2⟩
  left_inv w := by
    apply Subtype.ext
    change Fin.cons (w.1 0) (Fin.cons ((Fin.tail w.1) 0) (Fin.tail (Fin.tail w.1))) = w.1
    rw [Fin.cons_self_tail, Fin.cons_self_tail]
  right_inv w := by
    rcases w with ⟨⟨x, y, hy⟩, z⟩
    rfl

open Classical in
theorem slice_card {F : Type*} [Field F] [Fintype F] (x : F) :
    (slice F x).card = if x = 0 then Fintype.card F else
      (Finset.univ.image (fun z : F => z^2)).card := by
  classical
  by_cases hx : x = 0
  · simp [slice, hx]
  · simp only [hx, if_false]
    apply Finset.card_bij (fun y _ => y + x^2)
    · intro y hy
      simp only [slice, Finset.mem_filter, Finset.mem_univ, true_and, hx, false_or] at hy
      obtain ⟨z, hz⟩ := hy
      exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, hz.symm⟩
    · intro a _ b _ h
      exact add_right_cancel h
    · intro z hz
      obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hz
      refine ⟨z-x^2, ?_, by ring⟩
      simp only [slice, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨w, by rw [sub_add_cancel, hw]⟩

open Classical in
theorem family_card_product {F : Type*} [Field F] [Fintype F] (n : ℕ) :
    (family F n).card =
      (Fintype.card F + (Fintype.card F - 1) *
        (Finset.univ.image (fun z : F => z^2)).card) * Fintype.card F ^ n := by
  classical
  have h := Fintype.card_congr (familyEquiv F n)
  simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_sigma,
    Fintype.card_fun, Fintype.card_fin] at h
  rw [h]
  congr 1
  simp_rw [slice_card]
  rw [Finset.sum_ite]
  have hz : (Finset.univ.filter (fun x : F => x = 0)) = {0} := by ext; simp
  have hn : (Finset.univ.filter (fun x : F => ¬x = 0)) = Finset.univ.erase 0 := by
    ext; simp
  rw [hz, hn]
  simp

open Classical in
theorem family_card_identity {F : Type*} [Field F] [Fintype F]
    (htwo : (2 : F) ≠ 0) (n : ℕ) :
    2 * (family F n).card + Fintype.card F ^ n =
      (Fintype.card F ^ 2 + 2 * Fintype.card F) * Fintype.card F ^ n := by
  classical
  have hs := finite_field_square_count htwo
  have hq : 0 < Fintype.card F := Fintype.card_pos
  rw [family_card_product]
  have hq1 : Fintype.card F - 1 + 1 = Fintype.card F := Nat.sub_add_cancel hq
  have hp : 2 * (Fintype.card F + (Fintype.card F - 1) *
      (Finset.univ.image (fun z : F => z^2)).card) + 1 =
      Fintype.card F ^ 2 + 2 * Fintype.card F := by
    nlinarith [congrArg (fun k : ℕ => (Fintype.card F - 1) * k) hs]
  calc
    _ = (2 * (Fintype.card F + (Fintype.card F - 1) *
      (Finset.univ.image (fun z : F => z^2)).card) + 1) * Fintype.card F ^ n := by ring
    _ = _ := by rw [hp]

theorem family_card_real {F : Type*} [Field F] [Fintype F]
    (htwo : (2 : F) ≠ 0) (n : ℕ) :
    ((family F n).card : ℝ) =
      (((Fintype.card F : ℝ)^2 + 2 * Fintype.card F - 1) / 2) *
        (Fintype.card F : ℝ)^n := by
  have h := family_card_identity htwo n
  have hr : 2 * ((family F n).card : ℝ) + (Fintype.card F : ℝ)^n =
      ((Fintype.card F : ℝ)^2 + 2 * Fintype.card F) * (Fintype.card F : ℝ)^n := by
    exact_mod_cast h
  linarith

end Conjecture2899
