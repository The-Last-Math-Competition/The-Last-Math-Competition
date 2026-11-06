import MatrixExtensions
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Algebra.Star.Subalgebra

namespace Quasitrace918

open scoped ComplexOrder

-- The standard one-quasitrace laws, with explicit abelian-subalgebra linearity.
def OneQuasitrace (B : Type) [CStarAlgebra B] (τ : B → ℂ) : Prop :=
  (∀ x, 0 ≤ τ (star x * x)) ∧
  (∀ x, τ (star x * x) = τ (x * star x)) ∧
  (∀ x, IsSelfAdjoint x → IsSelfAdjoint (τ x)) ∧
  (∀ x y, IsSelfAdjoint x → IsSelfAdjoint y →
    τ (x + Complex.I • y) = τ x + Complex.I * τ y) ∧
  (∀ S : StarSubalgebra ℂ B, IsClosed (S : Set B) → (∀ x y : S, x * y = y * x) →
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = τ x)

def cornerOf (B : Type) [CStarAlgebra B] (a : B) : CStarMatrix (Fin 2) (Fin 2) B :=
  CStarMatrix.ofMatrix (Matrix.single (0 : Fin 2) (0 : Fin 2) a)

def TwoQuasitrace (B : Type) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (τ : B → ℂ) : Prop :=
  OneQuasitrace B τ ∧
    ∃ τ₂ : CStarMatrix (Fin 2) (Fin 2) B → ℂ,
      OneQuasitrace (CStarMatrix (Fin 2) (Fin 2) B) τ₂ ∧
        ∀ a, τ₂ (cornerOf B a) = τ a

def WeakContinuous (f : A → ℂ) : Prop :=
  Continuous (fun x : WeakSpace ℂ A => f ((toWeakSpace ℂ A).symm x))

def normalizedTwoQuasitraces : Set TraceDual :=
  {f | TwoQuasitrace A f ∧ f 1 = 1 ∧ WeakContinuous f}

theorem complex_linear_trace_oneQuasitrace (B : Type) [CStarAlgebra B]
    (f : B →ₗ[ℂ] ℂ)
    (hpos : ∀ x, 0 ≤ f (star x * x))
    (htrace : ∀ x y, f (x * y) = f (y * x))
    (hstar : ∀ x, f (star x) = star (f x)) : OneQuasitrace B f := by
  refine ⟨hpos, fun x => htrace (star x) x, ?_, ?_, ?_⟩
  · intro x hx
    change star (f x) = f x
    rw [← hstar x, hx.star_eq]
  · intro x y _ _
    simp only [map_add, map_smul, smul_eq_mul]
  · intro S _ _
    let g : S →ₗ[ℂ] ℂ :=
      { toFun := fun x => f x
        map_add' := fun x y => f.map_add (x : B) (y : B)
        map_smul' := fun c x => f.map_smul c (x : B) }
    exact ⟨g, fun _ => rfl⟩

theorem coordinate_oneQuasitrace (i : Fin 3) : OneQuasitrace A (coordinate i) :=
  complex_linear_trace_oneQuasitrace A (coordinate i).toLinearMap
    (coordinate_positive i) (coordinate_tracial i) (coordinate_star i)

-- On this commutative finite-dimensional algebra no quasitrace is discarded by
-- using the continuous complex-linear dual as the ambient affine space.
theorem oneQuasitrace_unique_dual_representation (τ : A → ℂ) (hτ : OneQuasitrace A τ) :
    ∃! f : TraceDual, ∀ a, f a = τ a := by
  obtain ⟨g, hg⟩ := hτ.2.2.2.2 (⊤ : StarSubalgebra ℂ A)
    (by simp) (fun x y => mul_comm x y)
  let inclusion : A →ₗ[ℂ] (⊤ : StarSubalgebra ℂ A) :=
    { toFun := fun a => ⟨a, by simp⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  let L : A →ₗ[ℂ] ℂ := g.comp inclusion
  let f : TraceDual := { L with cont := L.continuous_of_finiteDimensional }
  have hf : ∀ a, f a = τ a := fun a => hg (inclusion a)
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  ext a
  exact (hf' a).trans (hf a).symm

theorem oneQuasitrace_additive (τ : A → ℂ) (hτ : OneQuasitrace A τ) (a b : A) :
    τ (a + b) = τ a + τ b := by
  obtain ⟨f, hf, _⟩ := oneQuasitrace_unique_dual_representation τ hτ
  rw [← hf (a + b), ← hf a, ← hf b, map_add]

theorem oneQuasitrace_subadditive_real (τ : A → ℂ) (hτ : OneQuasitrace A τ) (a b : A) :
    (τ (a + b)).re ≤ (τ a).re + (τ b).re := by
  rw [oneQuasitrace_additive τ hτ, Complex.add_re]

theorem normalized_space_membership (f : TraceDual) :
    f ∈ normalizedTwoQuasitraces ↔ TwoQuasitrace A f ∧ f 1 = 1 ∧ WeakContinuous f :=
  Iff.rfl

end Quasitrace918

#check Quasitrace918.complex_linear_trace_oneQuasitrace
#print axioms Quasitrace918.complex_linear_trace_oneQuasitrace
#check Quasitrace918.coordinate_oneQuasitrace
#print axioms Quasitrace918.coordinate_oneQuasitrace
#check Quasitrace918.oneQuasitrace_unique_dual_representation
#print axioms Quasitrace918.oneQuasitrace_unique_dual_representation
#check Quasitrace918.oneQuasitrace_additive
#print axioms Quasitrace918.oneQuasitrace_additive
#check Quasitrace918.oneQuasitrace_subadditive_real
#print axioms Quasitrace918.oneQuasitrace_subadditive_real
#check Quasitrace918.normalized_space_membership
#print axioms Quasitrace918.normalized_space_membership
#print Quasitrace918.OneQuasitrace
#print axioms Quasitrace918.OneQuasitrace
#print Quasitrace918.TwoQuasitrace
#print axioms Quasitrace918.TwoQuasitrace
#print Quasitrace918.normalizedTwoQuasitraces
#print axioms Quasitrace918.normalizedTwoQuasitraces
