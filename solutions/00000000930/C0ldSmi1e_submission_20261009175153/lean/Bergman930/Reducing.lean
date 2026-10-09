import Bergman930.Completeness
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open Set Metric MeasureTheory Filter Complex
open scoped ENNReal Topology Real
namespace Bergman930

instance : Nontrivial l2Space :=
  ⟨⟨functionEquivL2 one, functionEquivL2 0,
    fun h => one_ne_zero (functionEquivL2.injective h)⟩⟩

theorem shift_norm_le (f : A2) : ‖toL2 (shift f)‖ ≤ ‖toL2 f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(square_integrable (shift f)).coeFn_toLp,
    (square_integrable f).coeFn_toLp, ae_restrict_mem disk_measurable] with z hs hf hz
  change ‖((square_integrable (shift f)).toLp (shift f)) z‖ ≤
    ‖((square_integrable f).toLp f) z‖
  rw [hs, hf, shift_apply, norm_mul]
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  exact mul_le_of_le_one_left (norm_nonneg _) hz'.le

theorem l2Shift_norm_le (f : l2Space) : ‖l2Shift f‖ ≤ ‖f‖ := by
  obtain ⟨g, rfl⟩ := functionEquivL2.surjective f
  simpa [l2Shift, functionEquivL2] using shift_norm_le g

/-- The bounded ordinary Bergman shift on its genuine Hilbert space. -/
def bergmanShift : l2Space →L[ℂ] l2Space :=
  l2Shift.mkContinuous 1 (fun f => by simpa only [one_mul] using l2Shift_norm_le f)

/-- Every relatively closed complex subspace invariant under M_z and with
M_z-invariant orthogonal complement. The topology and orthogonal complement here
are inherited from area-L²; no pointwise function topology is used. -/
def IsReducing (M : Submodule ℂ l2Space) : Prop :=
  IsClosed (M : Set l2Space) ∧
  (∀ f ∈ M, bergmanShift f ∈ M) ∧
  (∀ f ∈ Mᗮ, bergmanShift f ∈ Mᗮ)

/-- Equivalence with the customary definition using the Hilbert-space adjoint. -/
theorem isReducing_iff_adjoint (M : Submodule ℂ l2Space) : IsReducing M ↔
    IsClosed (M : Set l2Space) ∧
    (∀ f ∈ M, bergmanShift f ∈ M) ∧
    (∀ f ∈ M, bergmanShift.adjoint f ∈ M) := by
  constructor
  · rintro ⟨hclosed, hM, horth⟩
    letI : CompleteSpace M := hclosed.completeSpace_coe
    refine ⟨hclosed, hM, ?_⟩
    intro f hf
    rw [← M.orthogonal_orthogonal]
    apply (Mᗮ.mem_orthogonal _).mpr
    intro g hg
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact M.inner_left_of_mem_orthogonal hf (horth g hg)
  · rintro ⟨hclosed, hM, hadj⟩
    refine ⟨hclosed, hM, ?_⟩
    intro f hf
    apply (M.mem_orthogonal _).mpr
    intro g hg
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact M.inner_right_of_mem_orthogonal (hadj g hg) hf

/-- All closed complex reducing subspaces of the actual Bergman shift are trivial. -/
theorem reducing_eq_bot_or_top (M : Submodule ℂ l2Space) (hM : IsReducing M) :
    M = ⊥ ∨ M = ⊤ := by
  letI : CompleteSpace M := hM.1.completeSpace_coe
  have hcomp : IsCompl M Mᗮ := Submodule.isCompl_orthogonal_of_completeSpace
  let o : Submodule ℂ l2Space ≃o Submodule ℂ A2 :=
    Submodule.orderIsoMapComap functionEquivL2.symm
  have hinv (N : Submodule ℂ l2Space) (hN : ∀ f ∈ N, bergmanShift f ∈ N) :
      Invariant (o N) := by
    intro f hf
    obtain ⟨u, hu, rfl⟩ := hf
    refine ⟨bergmanShift u, hN u hu, ?_⟩
    simp [bergmanShift, l2Shift]
  have hc := invariant_complemented_eq_bot_or_top (o M) (o Mᗮ) (o.isCompl hcomp)
    (hinv M hM.2.1) (hinv Mᗮ hM.2.2)
  rcases hc with hbot | htop
  · exact Or.inl (o.injective (by simpa using hbot))
  · exact Or.inr (o.injective (by simpa using htop))

theorem reducing_bot : IsReducing (⊥ : Submodule ℂ l2Space) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro f hf
    have hzero : f = 0 := by simpa using hf
    simp [hzero]
  · simp

theorem reducing_top : IsReducing (⊤ : Submodule ℂ l2Space) := by
  refine ⟨isClosed_univ, ?_, ?_⟩
  · simp
  · intro f hf
    have hzero : f = 0 := by simpa using hf
    simp [hzero]

/-- A subtype of all subspaces, rather than a list of selected examples. -/
def ReducingSubspace := {M : Submodule ℂ l2Space // IsReducing M}

def reducingFromBool (b : Bool) : ReducingSubspace :=
  if b then ⟨⊤, reducing_top⟩ else ⟨⊥, reducing_bot⟩

theorem reducingFromBool_bijective : Function.Bijective reducingFromBool := by
  constructor
  · intro b c h
    cases b <;> cases c <;> simp_all [reducingFromBool]
    all_goals
      have h' := congrArg (fun M : ReducingSubspace => M.1) h
      simp at h'
  · intro M
    rcases reducing_eq_bot_or_top M.1 M.2 with hbot | htop
    · refine ⟨false, ?_⟩
      apply Subtype.ext
      simpa [reducingFromBool] using hbot.symm
    · refine ⟨true, ?_⟩
      apply Subtype.ext
      simpa [reducingFromBool] using htop.symm

/-- Exact cardinality, including the zero and full spaces. -/
theorem reducing_cardinality : Cardinal.mk ReducingSubspace = 2 := by
  rw [← Cardinal.mk_congr (Equiv.ofBijective reducingFromBool reducingFromBool_bijective),
    Cardinal.mk_bool]

/-- The necessary continuum-cardinality clause in conjecture 00000000930 is false. -/
theorem not_continuum : Cardinal.mk ReducingSubspace ≠ Cardinal.continuum := by
  rw [reducing_cardinality]
  exact (Cardinal.nat_lt_continuum 2).ne

end Bergman930
