import NuclearCPAP
import QuasiTraceModel

namespace Quasitrace918

open scoped ComplexOrder
open AffineSubspace

theorem matrixCoordinate_oneQuasitrace (i : Fin 3) :
    OneQuasitrace MatrixA (matrixCoordinate i) :=
  complex_linear_trace_oneQuasitrace MatrixA (matrixCoordinate i).toLinearMap
    (matrixCoordinate_positive i) (matrixCoordinate_tracial i) (matrixCoordinate_star i)

theorem coordinate_twoQuasitrace (i : Fin 3) : TwoQuasitrace A (coordinate i) := by
  refine ⟨coordinate_oneQuasitrace i, matrixCoordinate i, matrixCoordinate_oneQuasitrace i, ?_⟩
  intro a
  exact matrixCoordinate_corner i a

theorem coordinate_mem_normalizedQuasitraces (i : Fin 3) :
    coordinate i ∈ normalizedTwoQuasitraces :=
  ⟨coordinate_twoQuasitrace i, coordinate_one i, coordinate_weak_continuous i⟩

theorem normalized_quasitrace_dimension_ge_two :
    2 ≤ Module.finrank ℝ (affineSpan ℝ normalizedTwoQuasitraces).direction :=
  affineSpan_direction_finrank_ge_two normalizedTwoQuasitraces coordinate_mem_normalizedQuasitraces

theorem normalized_quasitrace_dimension_ne_one :
    Module.finrank ℝ (affineSpan ℝ normalizedTwoQuasitraces).direction ≠ 1 :=
  affineSpan_direction_finrank_ne_one normalizedTwoQuasitraces coordinate_mem_normalizedQuasitraces

def weakTwoQuasitraces : Set TraceDual :=
  {f | TwoQuasitrace A f ∧ WeakContinuous f}

theorem coordinate_mem_weakQuasitraces (i : Fin 3) : coordinate i ∈ weakTwoQuasitraces :=
  ⟨coordinate_twoQuasitrace i, coordinate_weak_continuous i⟩

theorem unnormalized_quasitrace_dimension_ne_one :
    Module.finrank ℝ (affineSpan ℝ weakTwoQuasitraces).direction ≠ 1 :=
  affineSpan_direction_finrank_ne_one weakTwoQuasitraces coordinate_mem_weakQuasitraces

def unbundledNormalizedQuasitraces : Set (A → ℂ) :=
  {τ | TwoQuasitrace A τ ∧ τ 1 = 1 ∧ WeakContinuous τ}

theorem unbundled_iff_unique_dual (τ : A → ℂ) :
    τ ∈ unbundledNormalizedQuasitraces ↔
      ∃! f : TraceDual, f ∈ normalizedTwoQuasitraces ∧ ∀ a, f a = τ a := by
  constructor
  · intro hτ
    obtain ⟨f, hf, huniq⟩ := oneQuasitrace_unique_dual_representation τ hτ.1.1
    have heq : (f : A → ℂ) = τ := funext hf
    have hmem : f ∈ normalizedTwoQuasitraces := by
      change TwoQuasitrace A (f : A → ℂ) ∧ f 1 = 1 ∧ WeakContinuous (f : A → ℂ)
      simpa only [heq] using
        (show TwoQuasitrace A τ ∧ τ 1 = 1 ∧ WeakContinuous τ from hτ)
    refine ⟨f, ⟨hmem, hf⟩, ?_⟩
    intro g hg
    exact huniq g hg.2
  · rintro ⟨f, ⟨hf, heval⟩, _⟩
    have heq : (f : A → ℂ) = τ := funext heval
    change TwoQuasitrace A τ ∧ τ 1 = 1 ∧ WeakContinuous τ
    simpa only [heq] using (normalized_space_membership f).1 hf

noncomputable def dualToFunction : TraceDual →ₗ[ℝ] (A → ℂ) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem dualToFunction_injective : Function.Injective dualToFunction := by
  intro f g h
  ext a
  exact congrFun h a

theorem unbundled_space_eq_linear_image :
    unbundledNormalizedQuasitraces = dualToFunction '' normalizedTwoQuasitraces := by
  ext τ
  constructor
  · intro hτ
    obtain ⟨f, ⟨hf, heval⟩, _⟩ := (unbundled_iff_unique_dual τ).1 hτ
    exact ⟨f, hf, funext heval⟩
  · rintro ⟨f, hf, rfl⟩
    exact (unbundled_iff_unique_dual (dualToFunction f)).2
      ⟨f, ⟨hf, fun _ => rfl⟩, fun g hg => dualToFunction_injective (funext hg.2)⟩

theorem actual_model_hasCPAP : HasCPAP A := finite_dimensional_hasCPAP A

theorem actual_nuclear_counterexample :
    HasCPAP A ∧
      (∀ i : Fin 3, coordinate i ∈ normalizedTwoQuasitraces) ∧
      Module.finrank ℝ (affineSpan ℝ normalizedTwoQuasitraces).direction ≠ 1 :=
  ⟨actual_model_hasCPAP, coordinate_mem_normalizedQuasitraces, normalized_quasitrace_dimension_ne_one⟩

def normalizedWeakQuasitraceSpace (B : Type) [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] : Set (B →L[ℂ] ℂ) :=
  {f | TwoQuasitrace B f ∧ f 1 = 1 ∧
    Continuous (fun x : WeakSpace ℂ B => f ((toWeakSpace ℂ B).symm x))}

-- This is already a necessary restriction of the printed universal clause.
def FiniteCommutativeDimensionOneClause : Prop :=
  ∀ (B : Type) [CommCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FiniteDimensional ℂ B], HasCPAP B →
      Module.finrank ℝ (affineSpan ℝ (normalizedWeakQuasitraceSpace B)).direction = 1

theorem source_necessary_clause_false : ¬FiniteCommutativeDimensionOneClause := by
  intro h
  have hA := h A actual_model_hasCPAP
  exact normalized_quasitrace_dimension_ne_one hA

end Quasitrace918

#check Quasitrace918.matrixCoordinate_oneQuasitrace
#print axioms Quasitrace918.matrixCoordinate_oneQuasitrace
#check Quasitrace918.coordinate_twoQuasitrace
#print axioms Quasitrace918.coordinate_twoQuasitrace
#check Quasitrace918.coordinate_mem_normalizedQuasitraces
#print axioms Quasitrace918.coordinate_mem_normalizedQuasitraces
#check Quasitrace918.normalized_quasitrace_dimension_ge_two
#print axioms Quasitrace918.normalized_quasitrace_dimension_ge_two
#check Quasitrace918.normalized_quasitrace_dimension_ne_one
#print axioms Quasitrace918.normalized_quasitrace_dimension_ne_one
#check Quasitrace918.coordinate_mem_weakQuasitraces
#print axioms Quasitrace918.coordinate_mem_weakQuasitraces
#check Quasitrace918.unnormalized_quasitrace_dimension_ne_one
#print axioms Quasitrace918.unnormalized_quasitrace_dimension_ne_one
#check Quasitrace918.unbundled_iff_unique_dual
#print axioms Quasitrace918.unbundled_iff_unique_dual
#check Quasitrace918.dualToFunction_injective
#print axioms Quasitrace918.dualToFunction_injective
#check Quasitrace918.unbundled_space_eq_linear_image
#print axioms Quasitrace918.unbundled_space_eq_linear_image
#check Quasitrace918.actual_model_hasCPAP
#print axioms Quasitrace918.actual_model_hasCPAP
#check Quasitrace918.actual_nuclear_counterexample
#print axioms Quasitrace918.actual_nuclear_counterexample
#check Quasitrace918.source_necessary_clause_false
#print axioms Quasitrace918.source_necessary_clause_false
#print Quasitrace918.FiniteCommutativeDimensionOneClause
#print axioms Quasitrace918.FiniteCommutativeDimensionOneClause
