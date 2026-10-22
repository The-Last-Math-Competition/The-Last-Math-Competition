import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped Matrix.L2OpNorm
open Matrix

noncomputable section
namespace Conjecture998
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

abbrev Obs := Matrix (Fin 8) (Fin 8) ℂ

local instance : CStarAlgebra Obs where
  norm_mul_self_le := CStarRing.norm_mul_self_le

def transposeStarEquiv : Obs ≃⋆ₐ[ℂ] Obsᵐᵒᵖ :=
  { Matrix.transposeAlgEquiv (Fin 8) ℂ ℂ with
    map_smul' := by intro c A; rfl
    map_star' := by intro A; rfl }

theorem transpose_norm (A : Obs) : ‖A.transpose‖ = ‖A‖ := by
  exact StarAlgEquiv.norm_map transposeStarEquiv A

def transposeMap : Obs →L[ℂ] Obs :=
  (Matrix.transposeLinearEquiv (Fin 8) (Fin 8) ℂ ℂ).toLinearMap.toContinuousLinearMap

theorem transposeMap_apply (A : Obs) : transposeMap A = A.transpose := rfl

theorem transposeMap_norm : ‖transposeMap‖ = 1 := by
  apply le_antisymm
  · apply transposeMap.opNorm_le_bound (by norm_num)
    intro A
    simp only [transposeMap_apply, transpose_norm, one_mul]
    exact le_rfl
  · have h := transposeMap.le_opNorm (1 : Obs)
    simpa [transposeMap_apply] using h

def amplify (k : ℕ) (T : Obs →L[ℂ] Obs)
    (X : Matrix (Fin k × Fin 8) (Fin k × Fin 8) ℂ) :
    Matrix (Fin k × Fin 8) (Fin k × Fin 8) ℂ :=
  fun a b => T (fun i j => X (a.1,i) (b.1,j)) a.2 b.2

def blockUnit (k : ℕ) (i j : Fin 8) :
    Matrix (Fin k × Fin 8) (Fin k × Fin 8) ℂ :=
  fun a b => if a.1 = b.1 ∧ a.2 = i ∧ b.2 = j then 1 else 0

theorem blockUnit_star (k : ℕ) (i j : Fin 8) :
    (blockUnit k i j)ᴴ = blockUnit k j i := by
  ext a b
  simp only [Matrix.conjTranspose_apply, blockUnit, apply_ite, star_one, star_zero]
  split_ifs <;> simp_all

theorem blockUnit_mul (k : ℕ) (i j l : Fin 8) :
    blockUnit k i j * blockUnit k j l = blockUnit k i l := by
  ext a b
  simp only [Matrix.mul_apply, blockUnit, Fintype.sum_prod_type]
  by_cases h₁ : a.2 = i <;> by_cases h₂ : b.2 = l
  all_goals simp [h₁, h₂, ite_and, ite_mul, mul_ite, Finset.sum_ite_irrel, and_assoc]

theorem blockUnit_norm_le (k : ℕ) (i j : Fin 8) : ‖blockUnit k i j‖ ≤ 1 := by
  have hP := Matrix.l2_opNorm_conjTranspose_mul_self (blockUnit k j j)
  rw [blockUnit_star, blockUnit_mul] at hP
  have hP0 := norm_nonneg (blockUnit k j j)
  have hP1 : ‖blockUnit k j j‖ ≤ 1 := by nlinarith
  have hB := Matrix.l2_opNorm_conjTranspose_mul_self (blockUnit k i j)
  rw [blockUnit_star, blockUnit_mul] at hB
  have hB0 := norm_nonneg (blockUnit k i j)
  nlinarith

theorem blockUnit_mul_left (k : ℕ) (i j : Fin 8)
    (X : Matrix (Fin k × Fin 8) (Fin k × Fin 8) ℂ) (a b) :
    (blockUnit k i j * X) a b = if a.2 = i then X (a.1,j) b else 0 := by
  simp only [Matrix.mul_apply, blockUnit, Fintype.sum_prod_type]
  by_cases h : a.2 = i <;> simp [h, ite_and, ite_mul, Finset.sum_ite_irrel]

theorem blockUnit_sandwich (k : ℕ) (i j : Fin 8)
    (X : Matrix (Fin k × Fin 8) (Fin k × Fin 8) ℂ) (a b) :
    (blockUnit k i j * X * blockUnit k i j) a b =
      if a.2 = i ∧ b.2 = j then X (a.1,j) (b.1,i) else 0 := by
  simp only [Matrix.mul_apply, blockUnit_mul_left, blockUnit, Fintype.sum_prod_type]
  by_cases h : a.2 = i <;> by_cases h' : b.2 = j
  all_goals simp [h, h', ite_and, ite_mul, mul_ite, Finset.sum_ite_irrel, and_assoc]

theorem amplify_transpose_sum (k : ℕ)
    (X : Matrix (Fin k × Fin 8) (Fin k × Fin 8) ℂ) :
    amplify k transposeMap X =
      ∑ i : Fin 8, ∑ j : Fin 8, blockUnit k i j * X * blockUnit k i j := by
  ext a b
  simp [amplify, transposeMap_apply, Matrix.transpose_apply, blockUnit_sandwich,
    Matrix.sum_apply, Finset.sum_ite_irrel, ite_and]

theorem amplify_transpose_bound (k : ℕ)
    (X : Matrix (Fin k × Fin 8) (Fin k × Fin 8) ℂ) :
    ‖amplify k transposeMap X‖ ≤ 64 * ‖X‖ := by
  rw [amplify_transpose_sum]
  calc
    _ ≤ ∑ i : Fin 8, ∑ j : Fin 8, ‖blockUnit k i j * X * blockUnit k i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin 8, ∑ _j : Fin 8, ‖X‖ := by
      gcongr with i _ j _
      calc
        _ ≤ ‖blockUnit k i j‖ * ‖X‖ * ‖blockUnit k i j‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ 1 * ‖X‖ * 1 := by
          gcongr <;> exact blockUnit_norm_le k i j
        _ = ‖X‖ := by ring
    _ = 64 * ‖X‖ := by simp; ring

abbrev Pair := Fin 8 × Fin 8

def swapMatrix : Matrix Pair Pair ℂ :=
  fun a b => if a.1 = b.2 ∧ a.2 = b.1 then 1 else 0

theorem swap_star : swapMatrixᴴ = swapMatrix := by
  ext a b
  simp only [Matrix.conjTranspose_apply, swapMatrix, apply_ite, star_one, star_zero]
  split_ifs <;> simp_all

theorem swap_square : swapMatrix * swapMatrix = 1 := by
  ext a b
  simp only [Matrix.mul_apply, swapMatrix, Fintype.sum_prod_type, Matrix.one_apply]
  simp [ite_and, ite_mul, mul_ite, Prod.ext_iff, and_comm]

theorem swap_norm : ‖swapMatrix‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self swapMatrix
  rw [swap_star, swap_square, CStarRing.norm_one] at h
  have h0 := norm_nonneg swapMatrix
  nlinarith

def omega : EuclideanSpace ℂ Pair :=
  (EuclideanSpace.equiv Pair ℂ).symm (fun a => if a.1 = a.2 then 1 else 0)

theorem omega_nonzero : omega ≠ 0 := by
  intro h
  have h' := congrArg (fun v : EuclideanSpace ℂ Pair => v (0,0)) h
  norm_num [omega] at h'

theorem amplified_swap_eigen :
    (EuclideanSpace.equiv Pair ℂ).symm ((amplify 8 transposeMap swapMatrix) *ᵥ omega) =
      (8 : ℂ) • omega := by
  ext a
  simp [amplify, transposeMap_apply, swapMatrix, omega, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, ite_and, ite_mul, mul_ite, Finset.sum_ite_irrel]

theorem amplification_norm_lower : 8 ≤ ‖amplify 8 transposeMap swapMatrix‖ := by
  have h := Matrix.l2_opNorm_mulVec (amplify 8 transposeMap swapMatrix) omega
  rw [amplified_swap_eigen, norm_smul] at h
  have hn : ‖omega‖ > 0 := norm_pos_iff.mpr omega_nonzero
  norm_num at h
  nlinarith

def amplificationRatios (T : Obs →L[ℂ] Obs) : Set ℝ :=
  {r | ∃ k : ℕ, ∃ X : Matrix (Fin k × Fin 8) (Fin k × Fin 8) ℂ,
    r = ‖amplify k T X‖ / ‖X‖}

def CompletelyBounded (T : Obs →L[ℂ] Obs) : Prop := BddAbove (amplificationRatios T)

def cbNorm (T : Obs →L[ℂ] Obs) : ℝ := sSup (amplificationRatios T)

theorem transpose_completelyBounded : CompletelyBounded transposeMap := by
  refine ⟨64, ?_⟩
  rintro r ⟨k,X,rfl⟩
  by_cases hx : ‖X‖ = 0
  · simp [hx]
  · apply (div_le_iff₀ (lt_of_le_of_ne (norm_nonneg X) (Ne.symm hx))).mpr
    exact amplify_transpose_bound k X

theorem transpose_cbNorm_lower : 8 ≤ cbNorm transposeMap := by
  have hmem : ‖amplify 8 transposeMap swapMatrix‖ ∈ amplificationRatios transposeMap := by
    refine ⟨8, swapMatrix, ?_⟩
    simp [swap_norm]
  exact amplification_norm_lower.trans (le_csSup transpose_completelyBounded hmem)

theorem transpose_cbNorm_upper : cbNorm transposeMap ≤ 64 := by
  apply csSup_le
  · exact ⟨0, 0, 0, by simp [amplify]⟩
  · rintro r ⟨k,X,rfl⟩
    by_cases hx : ‖X‖ = 0
    · simp [hx]
    · exact (div_le_iff₀ (lt_of_le_of_ne (norm_nonneg X) (Ne.symm hx))).mpr
        (amplify_transpose_bound k X)

def cbRatios : Set ℝ :=
  {r | ∃ T : Obs →L[ℂ] Obs, CompletelyBounded T ∧ T ≠ 0 ∧ r = cbNorm T / ‖T‖}

theorem counterexample : ∃ r ∈ cbRatios, Real.sqrt 2 < r := by
  refine ⟨cbNorm transposeMap, ?_, ?_⟩
  · refine ⟨transposeMap, transpose_completelyBounded, ?_, ?_⟩
    · intro h
      have h' := transposeMap_norm
      simp [h] at h'
    · simp [transposeMap_norm]
  · have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    have hl := transpose_cbNorm_lower
    nlinarith

theorem not_upperBound : ¬(Real.sqrt 2 ∈ upperBounds cbRatios) := by
  intro h
  obtain ⟨r,hr,hs⟩ := counterexample
  exact (not_le_of_gt hs) (h hr)

theorem not_claimed_supremum : ¬IsLUB cbRatios (Real.sqrt 2) := by
  intro h
  exact not_upperBound h.1

#print axioms transposeMap_norm
#print axioms amplify_transpose_bound
#print axioms transpose_cbNorm_lower
#print axioms not_claimed_supremum

end Conjecture998
