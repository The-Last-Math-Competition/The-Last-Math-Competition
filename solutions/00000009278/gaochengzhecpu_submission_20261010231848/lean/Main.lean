import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Conjecture9278

open scoped BigOperators
abbrev G := ZMod 4

def supp (f : G → ℂ) : Finset G := by
  classical
  exact Finset.univ.filter (fun x => f x ≠ 0)

def supportSize (f : G → ℂ) : ℕ := (supp f).card

theorem support_pos {f : G → ℂ} (hf : f ≠ 0) : 1 ≤ supportSize f := by
  classical
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  exact Finset.card_pos.mpr ⟨x, by simpa [supp] using hx⟩

theorem support_full {f : G → ℂ} (hf : ∀ x, f x ≠ 0) : supportSize f = 4 := by
  classical
  simp [supportSize, supp, hf]

theorem character_ne_zero (x : G) : ZMod.stdAddChar x ≠ 0 := by
  intro hx
  have h := (ZMod.stdAddChar (N := 4)).map_add_eq_mul x (-x)
  simp [hx] at h

theorem singleton_support_transform {f : G → ℂ} (hs : supportSize f = 1) :
    ∀ k : G, ZMod.dft f k ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hs
  have hfj : f j ≠ 0 := by
    have : j ∈ supp f := by rw [hj]; exact Finset.mem_singleton_self j
    simpa [supp] using this
  have hz : ∀ x : G, x ≠ j → f x = 0 := by
    intro x hx
    by_contra hfx
    have hm : x ∈ supp f := by simp [supp, hfx]
    rw [hj] at hm
    exact hx (Finset.mem_singleton.mp hm)
  intro k
  have heq : ZMod.dft f k = ZMod.stdAddChar (-(j * k)) * f j := by
    rw [ZMod.dft_apply]
    simp only [smul_eq_mul]
    apply Finset.sum_eq_single j
    · intro x _ hx
      simp [hz x hx]
    · intro hjn
      exact False.elim (hjn (Finset.mem_univ j))
  rw [heq]
  exact mul_ne_zero (character_ne_zero _) hfj

/-- The sharp support-product lower bound for every nonzero complex function on Z/4Z. -/
theorem support_product_bound (f : G → ℂ) (hf : f ≠ 0) :
    4 ≤ supportSize f * supportSize (ZMod.dft f) := by
  have hF : ZMod.dft f ≠ 0 := by
    intro h
    apply hf
    exact ZMod.dft.injective (h.trans (map_zero ZMod.dft).symm)
  have hp := support_pos hf
  have hq := support_pos hF
  by_cases h1 : supportSize f = 1
  · have h2 := support_full (singleton_support_transform h1)
    rw [h1, h2]
  by_cases h2 : supportSize (ZMod.dft f) = 1
  · have hall := singleton_support_transform h2
    have hfAll : ∀ x : G, f x ≠ 0 := by
      intro x hx
      have h := hall (-x)
      rw [ZMod.dft_dft] at h
      simp [hx] at h
    rw [support_full hfAll, h2]
  have hp2 : 2 ≤ supportSize f := by omega
  have hq2 : 2 ≤ supportSize (ZMod.dft f) := by omega
  exact Nat.mul_le_mul hp2 hq2

def H : Finset G := {0, 2}

def subgroup : AddSubgroup G where
  carrier := {x | x ∈ H}
  zero_mem' := by decide
  add_mem' := by decide +kernel
  neg_mem' := by decide +kernel

def witness (x : G) : ℂ := if x ∈ H then 1 else 0

theorem witness_support : supp witness = H := by
  classical
  ext x
  simp [supp, witness]

theorem character_two : ZMod.stdAddChar (2 : G) = -1 := by
  have hs : ZMod.stdAddChar (2 : G) * ZMod.stdAddChar (2 : G) = 1 := by
    rw [← AddChar.map_add_eq_mul, show (2 : G) + 2 = 0 by decide]
    exact AddChar.map_zero_eq_one _
  rcases mul_self_eq_one_iff.mp hs with h | h
  · have heq : (2 : G) = 0 := ZMod.injective_stdAddChar
      (h.trans (AddChar.map_zero_eq_one _).symm)
    exact False.elim ((by decide : (2 : G) ≠ 0) heq)
  · exact h

theorem fourier_witness : ∀ k : G, ZMod.dft witness k = 2 * witness k := by
  have hsum (f : G → ℂ) : (∑ x : G, f x) = f 0 + f 1 + f 2 + f 3 := by
    change (∑ x : Fin 4, f x) = _
    simp [Fin.sum_univ_succ]
    ring
  have h0 : witness 0 = 1 := by change ite _ _ _ = _; rw [if_pos (by decide)]
  have h1 : witness 1 = 0 := by change ite _ _ _ = _; rw [if_neg (by decide)]
  have h2 : witness 2 = 1 := by change ite _ _ _ = _; rw [if_pos (by decide)]
  have h3 : witness 3 = 0 := by change ite _ _ _ = _; rw [if_neg (by decide)]
  have heq (k : G) : ZMod.dft witness k = 1 + ZMod.stdAddChar (-(2 * k)) := by
    rw [ZMod.dft_apply, hsum]
    simp [h0, h1, h2, h3, smul_eq_mul]
  intro k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    have h : ∀ k : G, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide +kernel
    exact h k
  rcases hk with rfl | rfl | rfl | rfl
  · norm_num [heq, h0]
  · rw [heq, show -(2 * (1 : G)) = 2 by decide, character_two, h1]
    norm_num
  · rw [heq, show -(2 * (2 : G)) = 0 by decide, h2]
    norm_num
  · rw [heq, show -(2 * (3 : G)) = 2 by decide, character_two, h3]
    norm_num

theorem fourier_witness_support : supp (ZMod.dft witness) = H := by
  classical
  rw [← witness_support]
  ext x
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, fourier_witness]
  simp

theorem witness_nonzero : witness ≠ 0 := by
  intro h
  have hx := congrFun h 0
  norm_num [witness, H] at hx

theorem witness_product : supportSize witness * supportSize (ZMod.dft witness) = 4 := by
  rw [supportSize, supportSize, witness_support, fourier_witness_support]
  decide +kernel

def differenceCount (S : Finset G) (g : G) : ℕ :=
  ((S.product S).filter (fun p => p.1 - p.2 = g)).card

def IsDifferenceSet (S : Finset G) : Prop :=
  ∃ lam : ℕ, ∀ g : G, g ≠ 0 → differenceCount S g = lam

theorem subgroup_not_difference_set : ¬ IsDifferenceSet H := by
  rintro ⟨lam, hlam⟩
  have h1 := hlam 1 (by decide)
  have h2 := hlam 2 (by decide)
  have c1 : differenceCount H 1 = 0 := by decide +kernel
  have c2 : differenceCount H 2 = 2 := by decide +kernel
  rw [c1] at h1
  rw [c2] at h2
  omega

theorem counterexample :
    witness ≠ 0 ∧
    (∀ f : G → ℂ, f ≠ 0 → supportSize witness * supportSize (ZMod.dft witness) ≤
      supportSize f * supportSize (ZMod.dft f)) ∧
    ¬ IsDifferenceSet (supp witness) ∧ ¬ IsDifferenceSet (supp (ZMod.dft witness)) := by
  refine ⟨witness_nonzero, ?_, ?_, ?_⟩
  · intro f hf
    rw [witness_product]
    exact support_product_bound f hf
  · rw [witness_support]
    exact subgroup_not_difference_set
  · rw [fourier_witness_support]
    exact subgroup_not_difference_set

end Conjecture9278

#print axioms Conjecture9278.support_product_bound
#print axioms Conjecture9278.fourier_witness
#print axioms Conjecture9278.subgroup_not_difference_set
#print axioms Conjecture9278.counterexample
