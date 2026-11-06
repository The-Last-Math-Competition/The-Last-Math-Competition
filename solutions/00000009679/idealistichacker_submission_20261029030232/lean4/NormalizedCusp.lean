import AlgebraicPoint
import Mathlib.NumberTheory.ModularForms.Discriminant

open scoped MatrixGroups

namespace ModularValue9679

/-- A concrete imaginary quadratic subfield: degree two over Q and nonreal. -/
def ImaginaryQuadraticSubfield (K : IntermediateField Rat Complex) : Prop :=
  And (Module.finrank Rat K = 2) (Exists fun x : K => Not ((x : Complex).im = 0))

def OutsideImaginaryQuadratic (z : Complex) : Prop :=
  forall K : IntermediateField Rat Complex, ImaginaryQuadraticSubfield K -> Not (K.carrier z)

noncomputable def tau : UpperHalfPlane := UpperHalfPlane.mk point point_im_pos

theorem tau_coe : (tau : Complex) = point := rfl

theorem tau_algebraic : IsAlgebraic Rat (tau : Complex) := point_algebraic

theorem tau_outside_imaginary_quadratic : OutsideImaginaryQuadratic (tau : Complex) := by
  intro K hK
  exact point_not_mem_quadratic K hK.1

theorem discriminant_at_tau_nonzero : Not (CuspForm.discriminant tau = 0) := by
  exact ModularForm.discriminant_ne_zero tau

noncomputable def normalized : CuspForm 𝒮ℒ 12 :=
  (CuspForm.discriminant tau)⁻¹ • CuspForm.discriminant

theorem normalized_value : normalized tau = 1 := by
  change (CuspForm.discriminant tau)⁻¹ * CuspForm.discriminant tau = 1
  exact inv_mul_cancel₀ discriminant_at_tau_nonzero

theorem normalized_nonzero : Not (normalized = 0) := by
  intro h
  have hz : normalized tau = 0 := by rw [h]; rfl
  rw [normalized_value] at hz
  exact one_ne_zero hz

theorem normalized_value_algebraic : IsAlgebraic Rat (normalized tau) := by
  rw [normalized_value]
  exact isAlgebraic_one

theorem normalized_value_not_transcendental : Not (Transcendental Rat (normalized tau)) :=
  not_not_intro normalized_value_algebraic

/-- The necessary universal first clause, already restricted to level one. -/
def LevelOneValueAssertion : Prop :=
  forall k : Int, LE.le (2 : Int) k ->
    forall f : CuspForm 𝒮ℒ k, Not (f = 0) ->
      forall z : UpperHalfPlane, IsAlgebraic Rat (z : Complex) ->
        OutsideImaginaryQuadratic (z : Complex) -> Transcendental Rat (f z)

theorem level_one_value_assertion_false : Not LevelOneValueAssertion := by
  intro h
  exact normalized_value_not_transcendental
    (h 12 (by norm_num) normalized normalized_nonzero tau tau_algebraic
      tau_outside_imaginary_quadratic)

theorem actual_counterexample :
    Exists fun f : CuspForm 𝒮ℒ 12 => Exists fun z : UpperHalfPlane =>
      And (Not (f = 0)) (And (IsAlgebraic Rat (z : Complex))
        (And (OutsideImaginaryQuadratic (z : Complex))
          (And (f z = 1) (Not (Transcendental Rat (f z)))))) := by
  exact Exists.intro normalized (Exists.intro tau
    (And.intro normalized_nonzero (And.intro tau_algebraic
      (And.intro tau_outside_imaginary_quadratic
        (And.intro normalized_value normalized_value_not_transcendental)))))

end ModularValue9679

#check ModularValue9679.tau_coe
#print axioms ModularValue9679.tau_coe
#check ModularValue9679.tau_algebraic
#print axioms ModularValue9679.tau_algebraic
#check ModularValue9679.tau_outside_imaginary_quadratic
#print axioms ModularValue9679.tau_outside_imaginary_quadratic
#check ModularValue9679.discriminant_at_tau_nonzero
#print axioms ModularValue9679.discriminant_at_tau_nonzero
#check ModularValue9679.normalized_value
#print axioms ModularValue9679.normalized_value
#check ModularValue9679.normalized_nonzero
#print axioms ModularValue9679.normalized_nonzero
#check ModularValue9679.normalized_value_algebraic
#print axioms ModularValue9679.normalized_value_algebraic
#check ModularValue9679.normalized_value_not_transcendental
#print axioms ModularValue9679.normalized_value_not_transcendental
#check ModularValue9679.level_one_value_assertion_false
#print axioms ModularValue9679.level_one_value_assertion_false
#check ModularValue9679.actual_counterexample
#print axioms ModularValue9679.actual_counterexample
