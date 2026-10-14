import Mathlib.Analysis.NormedSpace.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Tactic

noncomputable section
open scoped TensorProduct BigOperators
namespace Conjecture7302

abbrev Factor := EuclideanSpace ℝ (Fin 2)
abbrev Tensor := PiTensorProduct ℝ (fun _ : Fin 3 => Factor)

theorem factor_expansion (v : Factor) :
    v = ∑ j : Fin 2, v j • EuclideanSpace.single j (1 : ℝ) := by
  ext k
  fin_cases k <;> simp [EuclideanSpace.single_apply]

theorem multilinear_expansion (f : MultilinearMap ℝ (fun _ : Fin 3 => Factor) ℝ)
    (m : Fin 3 → Factor) :
    f m = ∑ a : Fin 3 → Fin 2,
      (∏ i : Fin 3, m i (a i)) • f (fun i => EuclideanSpace.single (a i) (1 : ℝ)) := by
  conv_lhs => rw [show m = (fun i => ∑ j : Fin 2,
    (m i) j • EuclideanSpace.single j (1 : ℝ)) from funext fun i => factor_expansion (m i)]
  rw [f.map_sum]
  simp_rw [f.map_smul_univ]

theorem multilinear_continuous (f : MultilinearMap ℝ (fun _ : Fin 3 => Factor) ℝ) :
    Continuous f := by
  have h : (fun m => f m) = (fun m : Fin 3 → Factor =>
      ∑ a : Fin 3 → Fin 2, (∏ i : Fin 3, m i (a i)) •
        f (fun i => EuclideanSpace.single (a i) (1 : ℝ))) := funext (multilinear_expansion f)
  rw [show (f : (Fin 3 → Factor) → ℝ) = _ from h]
  fun_prop

theorem projective_definite (x : Tensor)
    (h : PiTensorProduct.projectiveSeminorm x = 0) : x = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff ℝ x).mp
  intro φ
  let f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Factor) ℝ :=
    ⟨PiTensorProduct.lift.symm φ, multilinear_continuous (PiTensorProduct.lift.symm φ)⟩
  have hb := PiTensorProduct.norm_eval_le_projectiveSeminorm x ℝ f
  have hf : PiTensorProduct.lift f.toMultilinearMap = φ :=
    PiTensorProduct.lift.apply_symm_apply φ
  rw [hf, h, zero_mul] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

/-- The projective decomposition seminorm is a genuine norm on these tensors. -/
def nuclearAddGroupNorm : AddGroupNorm Tensor where
  __ := (PiTensorProduct.projectiveSeminorm : Seminorm ℝ Tensor).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' := projective_definite

instance tensorNormedAddCommGroup : NormedAddCommGroup Tensor :=
  nuclearAddGroupNorm.toNormedAddCommGroup

instance tensorNormedSpace : NormedSpace ℝ Tensor where
  norm_smul_le a x := by
    change PiTensorProduct.projectiveSeminorm (a • x) ≤
      ‖a‖ * PiTensorProduct.projectiveSeminorm x
    exact le_of_eq ((PiTensorProduct.projectiveSeminorm : Seminorm ℝ Tensor).smul' a x)

/-- The installed norm is precisely Mathlib's finite-decomposition projective norm. -/
theorem norm_eq_projective (x : Tensor) : ‖x‖ = PiTensorProduct.projectiveSeminorm x := rfl

/-- A concrete nonzero order-three pure tensor. -/
def witness : Tensor :=
  PiTensorProduct.tprod ℝ (fun _ : Fin 3 => EuclideanSpace.single (0 : Fin 2) (1 : ℝ))

private def coordinateProduct : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Factor) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 3) ℝ).compContinuousLinearMap
    (fun _ => EuclideanSpace.proj (0 : Fin 2))

theorem witness_ne_zero : witness ≠ 0 := by
  intro h
  have he := congrArg (PiTensorProduct.lift coordinateProduct.toMultilinearMap) h
  norm_num [witness, coordinateProduct, EuclideanSpace.single_apply] at he

instance tensorNontrivial : Nontrivial Tensor := ⟨⟨witness, 0, witness_ne_zero⟩⟩

end Conjecture7302
