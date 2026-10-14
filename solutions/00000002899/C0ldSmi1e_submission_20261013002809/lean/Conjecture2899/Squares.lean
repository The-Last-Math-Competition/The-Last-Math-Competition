import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

open scoped BigOperators

open Classical in
theorem finite_field_square_count {F : Type*} [Field F] [Fintype F]
    (h2 : (2 : F) ≠ 0) :
    2 * (Finset.univ.image (fun z : F => z ^ 2)).card = Fintype.card F + 1 := by
  classical
  let squares : Finset F := Finset.univ.image (fun z : F => z ^ 2)
  let fiber := fun y : F => Finset.univ.filter (fun z : F => z ^ 2 = y)
  have hzmem : (0 : F) ∈ squares := by
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp⟩
  have hfzero : (fiber 0).card = 1 := by
    have heq : fiber 0 = {0} := by
      ext z
      simp [fiber]
    simp [heq]
  have hftwo : ∀ y ∈ squares.erase 0, (fiber y).card = 2 := by
    intro y hy
    obtain ⟨hy0, hys⟩ := Finset.mem_erase.mp hy
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hys
    have hz0 : z ≠ 0 := by
      intro h
      apply hy0
      simpa [h] using hz.symm
    have hzne : z ≠ -z := by
      intro h
      have hprod : (2 : F) * z = 0 := by
        rw [two_mul]
        exact add_eq_zero_iff_eq_neg.mpr h
      exact hz0 ((mul_eq_zero.mp hprod).resolve_left h2)
    have heq : fiber y = {z, -z} := by
      ext w
      simp [fiber, ← hz, sq_eq_sq_iff_eq_or_eq_neg]
    rw [heq]
    simp [hzne]
  have hcount : Fintype.card F = ∑ y ∈ squares, (fiber y).card := by
    exact Finset.card_eq_sum_card_image (fun z : F => z ^ 2) Finset.univ
  have hsum : ∑ y ∈ squares.erase 0, (fiber y).card = (squares.erase 0).card * 2 :=
    Finset.sum_const_nat hftwo
  have herase := Finset.sum_erase_add squares (fun y => (fiber y).card) hzmem
  change (∑ y ∈ squares.erase 0, (fiber y).card) + (fiber 0).card =
    ∑ y ∈ squares, (fiber y).card at herase
  rw [hsum, hfzero] at herase
  have hcard := Finset.card_erase_add_one hzmem
  change 2 * squares.card = Fintype.card F + 1
  omega

