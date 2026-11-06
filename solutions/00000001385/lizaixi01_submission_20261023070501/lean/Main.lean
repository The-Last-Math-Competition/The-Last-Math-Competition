import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic.NormNum

/-! The actual identity probability-circle system. Dimension here is Hilbert
dimension, not Hamel dimension; thresholds are real numbers, not just sampled
spectral points. Both real-eigenvalue and modulus cutoffs are constructed. -/
namespace TLMC1385
noncomputable section
open MeasureTheory Cardinal
open scoped ENNReal

instance period_positive : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
abbrev X := AddCircle (1 : ℝ)
noncomputable def μ : Measure X := AddCircle.haarAddCircle
abbrev E := Lp ℂ 2 μ

theorem probability_circle : IsProbabilityMeasure μ := by unfold μ; infer_instance

def T : X → X := id
theorem T_preserves : MeasurePreserving T μ μ := MeasurePreserving.id μ
theorem T_involutive : Function.Involutive T := fun _ => rfl

noncomputable def U : E →ₗ[ℂ] E := Lp.compMeasurePreservingₗ ℂ T T_preserves

theorem U_apply (f : E) : U f=f := by
  exact Lp.compMeasurePreserving_id_apply f

theorem U_identity : U=LinearMap.id := by
  apply LinearMap.ext
  exact U_apply

noncomputable def fourier : HilbertBasis ℤ ℂ E := fourierBasis

theorem true_eigenspace : Module.End.eigenspace U (1 : ℂ)=⊤ := by
  rw [U_identity]
  ext f
  simp

theorem one_eigenvalue : Module.End.HasEigenvalue U (1 : ℂ) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x:=fourier 0)
  exact ⟨by simp [U_apply],fourier.orthonormal.ne_zero 0⟩

theorem only_eigenvalue {z : ℂ} (hz : Module.End.HasEigenvalue U z) : z=1 := by
  obtain ⟨f,hf,hne⟩ := hz.exists_hasEigenvector
  have he : (1-z) • f=0 := by
    have h := hf
    rw [Module.End.mem_eigenspace_iff,U_apply] at h
    simpa [sub_smul] using sub_eq_zero.mpr h
  rcases smul_eq_zero.mp he with h|h
  · exact (sub_eq_zero.mp h).symm
  · exact False.elim (hne h)

def realCutoff (a : ℝ) : Submodule ℂ E :=
  (⨆ r : {r : ℝ // r≤a}, Module.End.eigenspace U (r.val : ℂ)).topologicalClosure

def modulusCutoff (a : ℝ) : Submodule ℂ E :=
  (⨆ z : {z : ℂ // ‖z‖≤a}, Module.End.eigenspace U z.val).topologicalClosure

theorem realCutoff_top {a : ℝ} (ha : 1≤a) : realCutoff a=⊤ := by
  apply top_unique
  calc
    ⊤ = Module.End.eigenspace U (1 : ℂ) := true_eigenspace.symm
    _ ≤ ⨆ r : {r : ℝ // r≤a}, Module.End.eigenspace U (r.val : ℂ) :=
      le_iSup (fun r : {r : ℝ // r≤a} => Module.End.eigenspace U (r.val : ℂ)) ⟨1,ha⟩
    _ ≤ realCutoff a := Submodule.le_topologicalClosure _

theorem modulusCutoff_top {a : ℝ} (ha : 1≤a) : modulusCutoff a=⊤ := by
  apply top_unique
  calc
    ⊤ = Module.End.eigenspace U (1 : ℂ) := true_eigenspace.symm
    _ ≤ ⨆ z : {z : ℂ // ‖z‖≤a}, Module.End.eigenspace U z.val :=
      le_iSup (fun z : {z : ℂ // ‖z‖≤a} => Module.End.eigenspace U z.val) ⟨1,by simpa using ha⟩
    _ ≤ modulusCutoff a := Submodule.le_topologicalClosure _

/- Hilbert basis cardinality is proved for every actual basis, so no chosen
Fourier enumeration is silently declared to be the dimension. -/
theorem all_basis_cardinality {ι : Type} (b : HilbertBasis ι ℂ E) :
    Cardinal.mk ι=ℵ₀ := by
  classical
  have hc (n : ℤ) : (Function.support (fun i : ι => b.repr (fourier n) i)).Countable := by
    have hs := ((lp.memℓp (b.repr (fourier n))).summable (by norm_num : 0<(2 : ℝ≥0∞).toReal)).countable_support
    simpa [Function.support] using hs
  have hcover : (Set.univ : Set ι)=⋃ n : ℤ, Function.support (fun i => b.repr (fourier n) i) := by
    ext i
    simp only [Set.mem_univ,Set.mem_iUnion,Function.mem_support,true_iff]
    by_contra h
    push Not at h
    have hz : fourier.repr (b i)=0 := by
      ext n
      rw [HilbertBasis.repr_apply_apply]
      have hn : inner ℂ (b i) (fourier n)=0 := by
        simpa only [HilbertBasis.repr_apply_apply] using h n
      change inner ℂ (fourier n) (b i)=0
      have hconj := inner_conj_symm (𝕜:=ℂ) (fourier n) (b i)
      rw [hn,map_zero] at hconj
      exact hconj.symm
    have hz' : b i=0 := fourier.repr.injective (by simpa using hz)
    exact b.orthonormal.ne_zero i hz'
  have : Countable ι := Set.countable_univ_iff.mp (hcover ▸ Set.countable_iUnion hc)
  have hi : Infinite ι := by
    by_contra h
    have : Finite ι := not_infinite_iff_finite.mp h
    let : Fintype ι := Fintype.ofFinite ι
    have : FiniteDimensional ℂ E := b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
    have hc' := fourier.orthonormal.linearIndependent.lt_aleph0_of_finiteDimensional
    simp only [Cardinal.mk_int,lt_self_iff_false] at hc'
  exact Cardinal.mk_eq_aleph0 ι

noncomputable def topIsometry : (⊤ : Submodule ℂ E) ≃ₗᵢ[ℂ] E where
  toLinearEquiv := Submodule.topEquiv
  norm_map' _ := rfl

noncomputable def topBasis : HilbertBasis ℤ ℂ (⊤ : Submodule ℂ E) :=
  HilbertBasis.ofRepr (topIsometry.trans fourier.repr)

theorem top_basis_cardinality {ι : Type} (b : HilbertBasis ι ℂ (⊤ : Submodule ℂ E)) :
    Cardinal.mk ι=ℵ₀ :=
  all_basis_cardinality (HilbertBasis.ofRepr (topIsometry.symm.trans b.repr))

/- Basis-cardinality definition: the set is nonempty and a singleton on every
cutoff used below. Thus its infimum uses no empty-set fallback. -/
noncomputable def hilbertDim (S : Submodule ℂ E) : Cardinal :=
  sInf {c | ∃ (ι : Type), Nonempty (HilbertBasis ι ℂ S) ∧ Cardinal.mk ι=c}

theorem top_hilbertDim : hilbertDim (⊤ : Submodule ℂ E)=ℵ₀ := by
  have hset : {c : Cardinal | ∃ (ι : Type), Nonempty (HilbertBasis ι ℂ (⊤ : Submodule ℂ E)) ∧ Cardinal.mk ι=c}={ℵ₀} := by
    ext c
    constructor
    · rintro ⟨ι,⟨b⟩,rfl⟩
      exact top_basis_cardinality b
    · intro hc
      have h : c=ℵ₀ := hc
      subst c
      exact ⟨ℤ,⟨topBasis⟩,Cardinal.mk_int⟩
  simp only [hilbertDim,hset,csInf_singleton]

noncomputable def Nreal (a : ℝ) : Cardinal := hilbertDim (realCutoff a)
noncomputable def Nmodulus (a : ℝ) : Cardinal := hilbertDim (modulusCutoff a)

theorem Nreal_value {a : ℝ} (ha : 1≤a) : Nreal a=ℵ₀ := by
  rw [Nreal,realCutoff_top ha,top_hilbertDim]

theorem Nmodulus_value {a : ℝ} (ha : 1≤a) : Nmodulus a=ℵ₀ := by
  rw [Nmodulus,modulusCutoff_top ha,top_hilbertDim]

def InfiniteJump (N : ℝ → Cardinal) : Prop :=
  ∀ a b : ℝ, a<b → ℵ₀≤N a → N b=2^ℵ₀

theorem real_counterexample : ¬ InfiniteJump Nreal := by
  intro h
  have hj := h 1 2 (by norm_num) (by rw [Nreal_value le_rfl])
  rw [Nreal_value (by norm_num : (1 : ℝ)≤2)] at hj
  exact (ne_of_lt (Cardinal.cantor ℵ₀)) hj

theorem modulus_counterexample : ¬ InfiniteJump Nmodulus := by
  intro h
  have hj := h 1 2 (by norm_num) (by rw [Nmodulus_value le_rfl])
  rw [Nmodulus_value (by norm_num : (1 : ℝ)≤2)] at hj
  exact (ne_of_lt (Cardinal.cantor ℵ₀)) hj

end
end TLMC1385
