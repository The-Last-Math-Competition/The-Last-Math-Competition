import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

namespace Quasitrace918

open scoped ComplexOrder
open AffineSubspace

-- The ordinary Pi norm is the supremum norm, not EuclideanSpace's norm.
abbrev A := Fin 3 → ℂ
abbrev TraceDual := A →L[ℂ] ℂ

noncomputable def coordinate (i : Fin 3) : TraceDual := ContinuousLinearMap.proj i

def atom (j : Fin 3) : A := Pi.single j 1

@[instance_reducible]
noncomputable def algebra_is_comm_cstar : CommCStarAlgebra A := inferInstance

theorem algebra_complex_finite : FiniteDimensional ℂ A := inferInstance

instance traceDual_complex_finite : FiniteDimensional ℂ TraceDual := inferInstance

instance traceDual_real_finite : FiniteDimensional ℝ TraceDual :=
  Module.Finite.trans ℂ TraceDual

theorem coordinate_apply (i : Fin 3) (x : A) : coordinate i x = x i := rfl

theorem coordinate_one (i : Fin 3) : coordinate i 1 = 1 := rfl

theorem coordinate_add (i : Fin 3) (x y : A) :
    coordinate i (x + y) = coordinate i x + coordinate i y := rfl

theorem coordinate_smul (i : Fin 3) (c : ℂ) (x : A) :
    coordinate i (c • x) = c * coordinate i x := rfl

theorem coordinate_mul (i : Fin 3) (x y : A) :
    coordinate i (x * y) = coordinate i x * coordinate i y := rfl

theorem coordinate_star (i : Fin 3) (x : A) :
    coordinate i (star x) = star (coordinate i x) := rfl

theorem coordinate_tracial (i : Fin 3) (x y : A) :
    coordinate i (x * y) = coordinate i (y * x) := mul_comm _ _

theorem coordinate_positive (i : Fin 3) (x : A) :
    0 ≤ coordinate i (star x * x) := star_mul_self_nonneg (x i)

theorem coordinate_star_square_real (i : Fin 3) (x : A) :
    (coordinate i (star x * x)).re = Complex.normSq (x i) := by
  change (star (x i) * x i).re = _
  simp [Complex.normSq, Complex.mul_re]

theorem coordinate_star_square_imag (i : Fin 3) (x : A) :
    (coordinate i (star x * x)).im = 0 := by
  change (star (x i) * x i).im = _
  simp [Complex.mul_im]
  ring

theorem coordinate_norm_bound (i : Fin 3) (x : A) : ‖coordinate i x‖ ≤ ‖x‖ :=
  norm_le_pi_norm x i

theorem coordinate_operator_norm (i : Fin 3) : ‖coordinate i‖ ≤ 1 := by
  apply (coordinate i).opNorm_le_bound (by norm_num)
  intro x
  simpa only [one_mul] using coordinate_norm_bound i x

theorem coordinate_continuous (i : Fin 3) : Continuous (coordinate i) :=
  (coordinate i).continuous

-- WeakSpace is sigma(A,A*), not the weak-star topology on the dual.
theorem coordinate_weak_continuous (i : Fin 3) :
    Continuous (fun x : WeakSpace ℂ A => coordinate i ((toWeakSpace ℂ A).symm x)) :=
  WeakBilin.eval_continuous (topDualPairing ℂ A).flip (coordinate i)

def ordinaryTraceStates : Set TraceDual :=
  {f | (∀ x : A, 0 ≤ f (star x * x)) ∧ f 1 = 1 ∧ ∀ x y : A, f (x * y) = f (y * x)}

theorem coordinate_mem_traceStates (i : Fin 3) : coordinate i ∈ ordinaryTraceStates :=
  ⟨coordinate_positive i, coordinate_one i, coordinate_tracial i⟩

theorem coordinate_atom (i j : Fin 3) : coordinate i (atom j) = if i = j then 1 else 0 := by
  simp [coordinate_apply, atom, Pi.single_apply]

theorem coordinates_real_linearIndependent : LinearIndependent ℝ coordinate := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (fun f : TraceDual => (f (atom j)).re) hg
  simpa [sum_apply, smul_apply,
    coordinate_atom, Complex.real_smul, Finset.sum_apply] using h

theorem coordinates_real_affineIndependent : AffineIndependent ℝ coordinate :=
  coordinates_real_linearIndependent.affineIndependent

theorem coordinate_triangle_finrank :
    Module.finrank ℝ (vectorSpan ℝ (Set.range coordinate)) = 2 :=
  coordinates_real_affineIndependent.finrank_vectorSpan (by simp)

theorem coordinate_difference_mem_vectorSpan (S : Set TraceDual)
    (hS : ∀ i : Fin 3, coordinate i ∈ S) (i j : Fin 3) :
    coordinate i - coordinate j ∈ vectorSpan ℝ S :=
  vsub_mem_vectorSpan ℝ (hS i) (hS j)

theorem vectorSpan_finrank_ge_two (S : Set TraceDual)
    (hS : ∀ i : Fin 3, coordinate i ∈ S) : 2 ≤ Module.finrank ℝ (vectorSpan ℝ S) := by
  have hsub : Set.range coordinate ⊆ S := by
    rintro f ⟨i, rfl⟩
    exact hS i
  have h := Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  rw [coordinate_triangle_finrank] at h
  exact h

theorem vectorSpan_finrank_ne_one (S : Set TraceDual)
    (hS : ∀ i : Fin 3, coordinate i ∈ S) : Module.finrank ℝ (vectorSpan ℝ S) ≠ 1 := by
  have h := vectorSpan_finrank_ge_two S hS
  omega

theorem affineSpan_direction_finrank_ge_two (S : Set TraceDual)
    (hS : ∀ i : Fin 3, coordinate i ∈ S) :
    2 ≤ Module.finrank ℝ (affineSpan ℝ S).direction := by
  rw [direction_affineSpan]
  exact vectorSpan_finrank_ge_two S hS

theorem affineSpan_direction_finrank_ne_one (S : Set TraceDual)
    (hS : ∀ i : Fin 3, coordinate i ∈ S) :
    Module.finrank ℝ (affineSpan ℝ S).direction ≠ 1 := by
  rw [direction_affineSpan]
  exact vectorSpan_finrank_ne_one S hS

theorem ordinaryTraceStates_dimension_ge_two :
    2 ≤ Module.finrank ℝ (affineSpan ℝ ordinaryTraceStates).direction :=
  affineSpan_direction_finrank_ge_two ordinaryTraceStates coordinate_mem_traceStates

theorem ordinaryTraceStates_dimension_ne_one :
    Module.finrank ℝ (affineSpan ℝ ordinaryTraceStates).direction ≠ 1 :=
  affineSpan_direction_finrank_ne_one ordinaryTraceStates coordinate_mem_traceStates

end Quasitrace918

#print Quasitrace918.A
#print axioms Quasitrace918.A
#print Quasitrace918.TraceDual
#print axioms Quasitrace918.TraceDual
#print Quasitrace918.coordinate
#print axioms Quasitrace918.coordinate
#print Quasitrace918.atom
#print axioms Quasitrace918.atom
#print Quasitrace918.traceDual_complex_finite
#print axioms Quasitrace918.traceDual_complex_finite
#print Quasitrace918.traceDual_real_finite
#print axioms Quasitrace918.traceDual_real_finite
#print Quasitrace918.ordinaryTraceStates
#print axioms Quasitrace918.ordinaryTraceStates

#print Quasitrace918.algebra_is_comm_cstar
#print axioms Quasitrace918.algebra_is_comm_cstar
#check @Quasitrace918.algebra_complex_finite
#print axioms Quasitrace918.algebra_complex_finite
#check @Quasitrace918.coordinate_apply
#print axioms Quasitrace918.coordinate_apply
#check @Quasitrace918.coordinate_one
#print axioms Quasitrace918.coordinate_one
#check @Quasitrace918.coordinate_add
#print axioms Quasitrace918.coordinate_add
#check @Quasitrace918.coordinate_smul
#print axioms Quasitrace918.coordinate_smul
#check @Quasitrace918.coordinate_mul
#print axioms Quasitrace918.coordinate_mul
#check @Quasitrace918.coordinate_star
#print axioms Quasitrace918.coordinate_star
#check @Quasitrace918.coordinate_tracial
#print axioms Quasitrace918.coordinate_tracial
#check @Quasitrace918.coordinate_positive
#print axioms Quasitrace918.coordinate_positive
#check @Quasitrace918.coordinate_star_square_real
#print axioms Quasitrace918.coordinate_star_square_real
#check @Quasitrace918.coordinate_star_square_imag
#print axioms Quasitrace918.coordinate_star_square_imag
#check @Quasitrace918.coordinate_norm_bound
#print axioms Quasitrace918.coordinate_norm_bound
#check @Quasitrace918.coordinate_operator_norm
#print axioms Quasitrace918.coordinate_operator_norm
#check @Quasitrace918.coordinate_continuous
#print axioms Quasitrace918.coordinate_continuous
#check @Quasitrace918.coordinate_weak_continuous
#print axioms Quasitrace918.coordinate_weak_continuous
#check @Quasitrace918.coordinate_mem_traceStates
#print axioms Quasitrace918.coordinate_mem_traceStates
#check @Quasitrace918.coordinate_atom
#print axioms Quasitrace918.coordinate_atom
#check @Quasitrace918.coordinates_real_linearIndependent
#print axioms Quasitrace918.coordinates_real_linearIndependent
#check @Quasitrace918.coordinates_real_affineIndependent
#print axioms Quasitrace918.coordinates_real_affineIndependent
#check @Quasitrace918.coordinate_triangle_finrank
#print axioms Quasitrace918.coordinate_triangle_finrank
#check @Quasitrace918.coordinate_difference_mem_vectorSpan
#print axioms Quasitrace918.coordinate_difference_mem_vectorSpan
#check @Quasitrace918.vectorSpan_finrank_ge_two
#print axioms Quasitrace918.vectorSpan_finrank_ge_two
#check @Quasitrace918.vectorSpan_finrank_ne_one
#print axioms Quasitrace918.vectorSpan_finrank_ne_one
#check @Quasitrace918.affineSpan_direction_finrank_ge_two
#print axioms Quasitrace918.affineSpan_direction_finrank_ge_two
#check @Quasitrace918.affineSpan_direction_finrank_ne_one
#print axioms Quasitrace918.affineSpan_direction_finrank_ne_one
#check @Quasitrace918.ordinaryTraceStates_dimension_ge_two
#print axioms Quasitrace918.ordinaryTraceStates_dimension_ge_two
#check @Quasitrace918.ordinaryTraceStates_dimension_ne_one
#print axioms Quasitrace918.ordinaryTraceStates_dimension_ne_one
