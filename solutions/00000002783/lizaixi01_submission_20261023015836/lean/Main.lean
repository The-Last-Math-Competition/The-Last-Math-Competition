import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace TLMC2783
set_option linter.unusedSimpArgs false
abbrev E := EuclideanSpace ℝ (Fin 2)
abbrev S := Fin 2 → ℝ
abbrev L1 := PiLp 1 (fun _ : Fin 2 => ℝ)

def e0 : S := ![1,0]
def e1 : S := ![0,1]
lemma snorm (x : S) : ‖x‖ = max |x 0| |x 1| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_trans (abs_nonneg _) (le_max_left _ _))).mpr
    intro i; fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x 0)
      (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x 1)
lemma basis_norms : ‖e0‖=1 ∧ ‖e1‖=1 ∧ ‖e0+e1‖=1 ∧ ‖e0-e1‖=1 := by
  norm_num [snorm,e0,e1]
noncomputable def coord : E ≃L[ℝ] S := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
noncomputable def distortion (T : E ≃L[ℝ] S) : ℝ :=
  ‖T.toContinuousLinearMap‖ * ‖T.symm.toContinuousLinearMap‖

lemma every_distortion_lower (T : E ≃L[ℝ] S) : Real.sqrt 2 ≤ distortion T := by
  let u : E := T.symm e0
  let v : E := T.symm e1
  let m : ℝ := ‖T.toContinuousLinearMap‖
  let M : ℝ := ‖T.symm.toContinuousLinearMap‖
  have hm : 0 ≤ m := norm_nonneg _
  have hM : 0 ≤ M := norm_nonneg _
  have hu : 1 ≤ m * ‖u‖ := by
    have h := T.toContinuousLinearMap.le_opNorm u
    simpa [u,m,basis_norms.1] using h
  have hv : 1 ≤ m * ‖v‖ := by
    have h := T.toContinuousLinearMap.le_opNorm v
    simpa [v,m,basis_norms.2.1] using h
  have hp : ‖u+v‖ ≤ M := by
    have h := T.symm.toContinuousLinearMap.le_opNorm (e0+e1)
    simpa [u,v,M,map_add,basis_norms.2.2.1] using h
  have hd : ‖u-v‖ ≤ M := by
    have h := T.symm.toContinuousLinearMap.le_opNorm (e0-e1)
    simpa [u,v,M,map_sub,basis_norms.2.2.2] using h
  have hpar := parallelogram_law_with_norm ℝ u v
  have hp2 : ‖u+v‖^2 ≤ M^2 := sq_le_sq₀ (norm_nonneg _) hM |>.mpr hp
  have hd2 : ‖u-v‖^2 ≤ M^2 := sq_le_sq₀ (norm_nonneg _) hM |>.mpr hd
  have hsum : ‖u‖^2+‖v‖^2 ≤ M^2 := by nlinarith
  have hu2 : 1 ≤ (m*‖u‖)^2 := by nlinarith
  have hv2 : 1 ≤ (m*‖v‖)^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg m)
  have hprod : 2 ≤ (m*M)^2 := by nlinarith
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hnonneg := mul_nonneg hm hM
  change Real.sqrt 2 ≤ m*M
  nlinarith [Real.sqrt_nonneg (2:ℝ)]
lemma coord_norm_le_one : ‖coord.toContinuousLinearMap‖ ≤ 1 := by
  apply coord.toContinuousLinearMap.opNorm_le_bound (by norm_num)
  intro x
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le x i
lemma coord_symm_norm_le : ‖coord.symm.toContinuousLinearMap‖ ≤ Real.sqrt 2 := by
  apply coord.symm.toContinuousLinearMap.opNorm_le_bound (Real.sqrt_nonneg _)
  intro y
  change ‖coord.symm y‖ ≤ Real.sqrt 2 * ‖y‖
  have hsq : ‖coord.symm y‖^2=|y 0|^2+|y 1|^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [coord,Fin.sum_univ_two,Real.norm_eq_abs]
  have h0 : |y 0| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm y 0
  have h1 : |y 1| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm y 1
  have hh0 := (sq_le_sq₀ (abs_nonneg (y 0)) (norm_nonneg y)).mpr h0
  have hh1 := (sq_le_sq₀ (abs_nonneg (y 1)) (norm_nonneg y)).mpr h1
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by norm_num)]
  nlinarith
lemma coord_distortion : distortion coord = Real.sqrt 2 := by
  apply le_antisymm
  · exact (mul_le_mul coord_norm_le_one coord_symm_norm_le (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · exact every_distortion_lower _

noncomputable def distances : Set ℝ := Set.range distortion
noncomputable def bmDistance : ℝ := sInf distances
lemma distortion_isLeast : IsLeast distances (Real.sqrt 2) := by
  refine ⟨?_,?_⟩
  · exact ⟨coord,coord_distortion⟩
  · rintro r ⟨T,rfl⟩; exact every_distortion_lower T
lemma bmDistance_eq : bmDistance=Real.sqrt 2 := distortion_isLeast.csInf_eq
lemma sqrt_two_gt_one : (1:ℝ)<Real.sqrt 2 := by
  have h := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  nlinarith [Real.sqrt_nonneg (2:ℝ)]

lemma not_isometric_sup : ¬ Nonempty (E ≃ₗᵢ[ℝ] S) := by
  rintro ⟨T⟩
  let u := T.symm e0
  let v := T.symm e1
  have h := parallelogram_law_with_norm ℝ u v
  have hu : ‖u‖=1 := by simp [u,basis_norms.1]
  have hv : ‖v‖=1 := by simp [v,basis_norms.2.1]
  have hp : ‖u+v‖=1 := by
    change ‖T.symm e0 + T.symm e1‖=1
    rw [← map_add,T.symm.norm_map]
    exact basis_norms.2.2.1
  have hd : ‖u-v‖=1 := by
    change ‖T.symm e0 - T.symm e1‖=1
    rw [← map_sub,T.symm.norm_map]
    exact basis_norms.2.2.2
  nlinarith

def a0 : L1 := WithLp.toLp 1 e0
def a1 : L1 := WithLp.toLp 1 e1
lemma l1_basis_norms : ‖a0‖=1 ∧ ‖a1‖=1 ∧ ‖a0+a1‖=2 ∧ ‖a0-a1‖=2 := by
  norm_num [PiLp.norm_eq_of_L1,Fin.sum_univ_two,a0,a1,e0,e1]
lemma not_isometric_l1 : ¬ Nonempty (E ≃ₗᵢ[ℝ] L1) := by
  rintro ⟨T⟩
  let u := T.symm a0
  let v := T.symm a1
  have h := parallelogram_law_with_norm ℝ u v
  have hu : ‖u‖=1 := by simp [u,l1_basis_norms.1]
  have hv : ‖v‖=1 := by simp [v,l1_basis_norms.2.1]
  have hp : ‖u+v‖=2 := by
    change ‖T.symm a0 + T.symm a1‖=2
    rw [← map_add,T.symm.norm_map]
    exact l1_basis_norms.2.2.1
  have hd : ‖u-v‖=2 := by
    change ‖T.symm a0 - T.symm a1‖=2
    rw [← map_sub,T.symm.norm_map]
    exact l1_basis_norms.2.2.2
  nlinarith
def NamedPair : Prop :=
  (Nonempty (E ≃ₗᵢ[ℝ] L1) ∧ Nonempty (S ≃ₗᵢ[ℝ] S)) ∨
  (Nonempty (E ≃ₗᵢ[ℝ] S) ∧ Nonempty (S ≃ₗᵢ[ℝ] L1))
lemma not_named_pair : ¬ NamedPair := by
  rintro (⟨h,_⟩ | ⟨h,_⟩)
  · exact not_isometric_l1 h
  · exact not_isometric_sup h
theorem no_unique_equality_classification : ¬ (bmDistance=Real.sqrt 2 → NamedPair) := by
  intro h
  exact not_named_pair (h bmDistance_eq)
/-- A genuine equality pair outside both orders of the named isometry classes. -/
theorem counterexample : Module.finrank ℝ E=2 ∧ Module.finrank ℝ S=2 ∧
    bmDistance=Real.sqrt 2 ∧ ¬Nonempty (E ≃ₗᵢ[ℝ] L1) ∧ ¬Nonempty (E ≃ₗᵢ[ℝ] S) := by
  exact ⟨by simp,by simp,bmDistance_eq,not_isometric_l1,not_isometric_sup⟩
end TLMC2783
