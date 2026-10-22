import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace TLMC644
open Matrix
set_option maxRecDepth 2000
set_option linter.unusedSectionVars false

/-- The actual Artin three-strand presentation, with its single braid relator. -/
def braidRelator : FreeGroup (Fin 2) :=
  (FreeGroup.of 0*FreeGroup.of 1*FreeGroup.of 0)*
    (FreeGroup.of 1*FreeGroup.of 0*FreeGroup.of 1)⁻¹
abbrev Braid3 := PresentedGroup ({braidRelator} : Set (FreeGroup (Fin 2)))
def sigma (i : Fin 2) : Braid3 := PresentedGroup.of i

/-- Standard reduced generator matrices, Morier-Genoud--Ovsienko--Veselov (1.1). -/
def reducedA (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![-t,1;0,1]
def reducedB (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;t,-t]
/-- Standard unreduced generator blocks, Kassel--Turaev Section3.1.1. -/
def unreducedA (t : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![1-t,t,0;1,0,0;0,0,1]
def unreducedB (t : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![1,0,0;0,1-t,t;0,1,0]

lemma reducedA_det (t : ℂ) : (reducedA t).det = -t := by simp [reducedA,Matrix.det_fin_two]
lemma reducedB_det (t : ℂ) : (reducedB t).det = -t := by simp [reducedB,Matrix.det_fin_two]
lemma unreducedA_det (t : ℂ) : (unreducedA t).det = -t := by simp [unreducedA,Matrix.det_fin_three]
lemma unreducedB_det (t : ℂ) : (unreducedB t).det = -t := by simp [unreducedB,Matrix.det_fin_three]

lemma reduced_braid (t : ℂ) : reducedA t*reducedB t*reducedA t = reducedB t*reducedA t*reducedB t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reducedA,reducedB,Matrix.mul_apply,Fin.sum_univ_succ]
lemma unreduced_braid (t : ℂ) : unreducedA t*unreducedB t*unreducedA t = unreducedB t*unreducedA t*unreducedB t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unreducedA,unreducedB,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

noncomputable def redAU (t : ℂ) (ht : t≠0) : GeneralLinearGroup (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero (reducedA t) (by rw [reducedA_det]; exact neg_ne_zero.mpr ht)
noncomputable def redBU (t : ℂ) (ht : t≠0) : GeneralLinearGroup (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero (reducedB t) (by rw [reducedB_det]; exact neg_ne_zero.mpr ht)
noncomputable def unredAU (t : ℂ) (ht : t≠0) : GeneralLinearGroup (Fin 3) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero (unreducedA t) (by rw [unreducedA_det]; exact neg_ne_zero.mpr ht)
noncomputable def unredBU (t : ℂ) (ht : t≠0) : GeneralLinearGroup (Fin 3) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero (unreducedB t) (by rw [unreducedB_det]; exact neg_ne_zero.mpr ht)

noncomputable def redGenerators (t : ℂ) (ht : t≠0) (i : Fin 2) : GeneralLinearGroup (Fin 2) ℂ :=
  if i=0 then redAU t ht else redBU t ht
noncomputable def unredGenerators (t : ℂ) (ht : t≠0) (i : Fin 2) : GeneralLinearGroup (Fin 3) ℂ :=
  if i=0 then unredAU t ht else unredBU t ht

lemma red_relation (t : ℂ) (ht : t≠0) :
    ∀ r ∈ ({braidRelator} : Set (FreeGroup (Fin 2))), FreeGroup.lift (redGenerators t ht) r=1 := by
  have h : redAU t ht*redBU t ht*redAU t ht = redBU t ht*redAU t ht*redBU t ht := by
    apply Units.ext
    simpa [GeneralLinearGroup.coe_mul,redAU,redBU] using reduced_braid t
  rintro r hr
  rw [Set.mem_singleton_iff] at hr
  subst r
  simp [braidRelator,redGenerators,h]
lemma unred_relation (t : ℂ) (ht : t≠0) :
    ∀ r ∈ ({braidRelator} : Set (FreeGroup (Fin 2))), FreeGroup.lift (unredGenerators t ht) r=1 := by
  have h : unredAU t ht*unredBU t ht*unredAU t ht = unredBU t ht*unredAU t ht*unredBU t ht := by
    apply Units.ext
    simpa [GeneralLinearGroup.coe_mul,unredAU,unredBU] using unreduced_braid t
  rintro r hr
  rw [Set.mem_singleton_iff] at hr
  subst r
  simp [braidRelator,unredGenerators,h]

/-- Actual group homomorphisms obtained by checking the Artin relation. -/
noncomputable def reducedBurau (t : ℂ) (ht : t≠0) : Braid3 →* GeneralLinearGroup (Fin 2) ℂ :=
  PresentedGroup.toGroup (red_relation t ht)
noncomputable def unreducedBurau (t : ℂ) (ht : t≠0) : Braid3 →* GeneralLinearGroup (Fin 3) ℂ :=
  PresentedGroup.toGroup (unred_relation t ht)

lemma reduced_sigma_one (t : ℂ) (ht : t≠0) :
    ((reducedBurau t ht (sigma 0) : GeneralLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)=reducedA t := by
  simp [reducedBurau,sigma,redGenerators,redAU]
lemma unreduced_sigma_one (t : ℂ) (ht : t≠0) :
    ((unreducedBurau t ht (sigma 0) : GeneralLinearGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)=unreducedA t := by
  simp [unreducedBurau,sigma,unredGenerators,unredAU]

noncomputable def parameter : ℂ := 3/4
lemma parameter_legal : parameter.im=0 ∧ parameter≠0 ∧ 0<parameter.re ∧ parameter.re<1 := by
  norm_num [parameter]

def rv : Fin 2 → ℂ := ![1,0]
def uv : Fin 3 → ℂ := ![-3,4,0]
lemma rv_nonzero : rv≠0 := by
  intro h
  have hh := congrFun h 0
  norm_num [rv] at hh
lemma uv_nonzero : uv≠0 := by
  intro h
  have hh := congrFun h 0
  norm_num [uv] at hh

lemma reduced_vector : reducedA parameter *ᵥ rv = (-parameter) • rv := by
  ext i
  fin_cases i <;> norm_num [reducedA,parameter,rv,Matrix.mulVec, dotProduct,Fin.sum_univ_succ]
lemma unreduced_vector : unreducedA parameter *ᵥ uv = (-parameter) • uv := by
  ext i
  fin_cases i <;> norm_num [unreducedA,parameter,uv,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

lemma reduced_eigenvalue : Module.End.HasEigenvalue (Matrix.mulVecLin (reducedA parameter)) (-parameter) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x:=rv)
  rw [Module.End.hasEigenvector_iff,Module.End.mem_eigenspace_iff]
  exact ⟨reduced_vector,rv_nonzero⟩
lemma unreduced_eigenvalue : Module.End.HasEigenvalue (Matrix.mulVecLin (unreducedA parameter)) (-parameter) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x:=uv)
  rw [Module.End.hasEigenvector_iff,Module.End.mem_eigenspace_iff]
  exact ⟨unreduced_vector,uv_nonzero⟩

section BasisChange
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma conjugate_eigenvalue (M : Matrix n n ℂ) (μ : ℂ) (h : Module.End.HasEigenvalue (Matrix.mulVecLin M) μ)
    (P : GeneralLinearGroup n ℂ) :
    Module.End.HasEigenvalue (Matrix.mulVecLin (((P⁻¹ : GeneralLinearGroup n ℂ) : Matrix n n ℂ)*M*(P : Matrix n n ℂ))) μ := by
  obtain ⟨v,hv⟩ := h.exists_hasEigenvector
  obtain ⟨he,hne⟩ := (Module.End.hasEigenvector_iff.mp hv)
  have he' : M *ᵥ v=μ • v := (Module.End.mem_eigenspace_iff.mp he)
  let w := ((P⁻¹ : GeneralLinearGroup n ℂ) : Matrix n n ℂ) *ᵥ v
  have hcancel : (P : Matrix n n ℂ)*ᵥ w=v := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec,←GeneralLinearGroup.coe_mul]
    simp
  have hw : w≠0 := by
    intro hz
    rw [hz,Matrix.mulVec_zero] at hcancel
    exact hne hcancel.symm
  apply Module.End.hasEigenvalue_of_hasEigenvector (x:=w)
  rw [Module.End.hasEigenvector_iff,Module.End.mem_eigenspace_iff]
  refine ⟨?_,hw⟩
  change (((P⁻¹ : GeneralLinearGroup n ℂ) : Matrix n n ℂ)*M*(P : Matrix n n ℂ))*ᵥ w=μ • w
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hcancel,he',Matrix.mulVec_smul]

end BasisChange

/-- The precise spectral lower bound explicitly required by the source. -/
def SpectralBound {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) : Prop :=
  ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.mulVecLin M) μ → (-1/2 : ℝ)≤μ.re

lemma negative_real_part : (-parameter).re < (-1/2 : ℝ) := by norm_num [parameter]

theorem no_reduced_bound_in_any_basis (P : GeneralLinearGroup (Fin 2) ℂ) :
    ¬SpectralBound (((P⁻¹ : GeneralLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)*
      (reducedBurau parameter parameter_legal.2.1 (sigma 0) : Matrix (Fin 2) (Fin 2) ℂ)*
      (P : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [reduced_sigma_one]
  intro h
  have hh := h (-parameter) (conjugate_eigenvalue _ _ reduced_eigenvalue P)
  exact (not_le_of_gt negative_real_part) hh

theorem no_unreduced_bound_in_any_basis (P : GeneralLinearGroup (Fin 3) ℂ) :
    ¬SpectralBound (((P⁻¹ : GeneralLinearGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)*
      (unreducedBurau parameter parameter_legal.2.1 (sigma 0) : Matrix (Fin 3) (Fin 3) ℂ)*
      (P : Matrix (Fin 3) (Fin 3) ℂ)) := by
  rw [unreduced_sigma_one]
  intro h
  have hh := h (-parameter) (conjugate_eigenvalue _ _ unreduced_eigenvalue P)
  exact (not_le_of_gt negative_real_part) hh

/-- The source's universal real-specialization spectral condition fails. -/
theorem not_all_real_reduced_specializations :
    ¬∀ (t : ℂ) (ht : t≠0), t.im=0 → ∀ b : Braid3,
      SpectralBound (reducedBurau t ht b : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have hh := h parameter parameter_legal.2.1 parameter_legal.1 (sigma 0)
  have hn := no_reduced_bound_in_any_basis (1 : GeneralLinearGroup (Fin 2) ℂ)
  simp only [inv_one,GeneralLinearGroup.coe_one,Matrix.one_mul,Matrix.mul_one] at hn
  exact hn hh

theorem not_all_real_unreduced_specializations :
    ¬∀ (t : ℂ) (ht : t≠0), t.im=0 → ∀ b : Braid3,
      SpectralBound (unreducedBurau t ht b : Matrix (Fin 3) (Fin 3) ℂ) := by
  intro h
  have hh := h parameter parameter_legal.2.1 parameter_legal.1 (sigma 0)
  have hn := no_unreduced_bound_in_any_basis (1 : GeneralLinearGroup (Fin 3) ℂ)
  simp only [inv_one,GeneralLinearGroup.coe_one,Matrix.one_mul,Matrix.mul_one] at hn
  exact hn hh

end TLMC644
