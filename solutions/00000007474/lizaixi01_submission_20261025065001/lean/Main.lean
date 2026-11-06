import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-
Problem7474: only the affine real parameter-spectrum clause.
The spectrum is the actual set of parameters where the actual bounded operator
is not invertible. No assertion about a projectivized parameter spectrum,
genus, pencil rank or any repaired narrower family is made.
-/
noncomputable section
namespace TLMC7474
open MvPolynomial

abbrev Param := Fin 3 → ℝ
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Poly2 := MvPolynomial (Fin 2) ℝ
abbrev Operator := ℝ →L[ℝ] ℝ

def parameterSum (x : Param) : ℝ := x 0 + x 1 + x 2
def linearPolynomial : Poly3 := X 0 + X 1 + X 2
def quadraticPolynomial : Poly3 := linearPolynomial ^ 2
def pencil (x : Param) : Operator := (parameterSum x) ^ 2 • (1 : Operator)
def parameterSpectrum : Set Param := {x | (0 : ℝ) ∈ spectrum ℝ (pencil x)}

theorem pencil_apply (x : Param) (v : ℝ) : pencil x v = (parameterSum x)^2 * v := by
  simp [pencil]

theorem polynomial_evaluation (x : Param) :
    eval x quadraticPolynomial = (parameterSum x)^2 := by
  simp [quadraticPolynomial, linearPolynomial, parameterSum]

theorem pencil_polynomial (x : Param) :
    pencil x = eval x quadraticPolynomial • (1 : Operator) := by
  rw [polynomial_evaluation]; rfl

theorem pencil_selfAdjoint (x : Param) : IsSelfAdjoint (pencil x) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro v w
  simp [pencil]
  ring

theorem pencil_continuous : Continuous pencil := by
  unfold pencil parameterSum
  fun_prop

theorem scalar_operator_isUnit_iff (a : ℝ) :
    IsUnit (a • (1 : Operator)) ↔ a ≠ 0 := by
  constructor
  · intro h ha
    subst a
    simpa using h.ne_zero
  · intro ha
    have h := (isUnit_iff_ne_zero.mpr ha).map (algebraMap ℝ Operator)
    simpa [Algebra.algebraMap_eq_smul_one] using h

theorem mem_parameterSpectrum_iff (x : Param) :
    x ∈ parameterSpectrum ↔ parameterSum x = 0 := by
  change (0 : ℝ) ∈ spectrum ℝ (pencil x) ↔ _
  rw [spectrum.zero_mem_iff, pencil, scalar_operator_isUnit_iff]
  simp

theorem parameterSpectrum_eq_plane :
    parameterSpectrum = {x : Param | x 0 + x 1 + x 2 = 0} := by
  ext x
  exact mem_parameterSpectrum_iff x

theorem zero_mem_parameterSpectrum : (0 : Param) ∈ parameterSpectrum := by
  rw [mem_parameterSpectrum_iff]
  simp [parameterSum]

theorem pencil_at_basis : pencil ![1, 0, 0] = 1 := by
  simp [pencil, parameterSum]

theorem basis_not_mem_parameterSpectrum : ![1, 0, 0] ∉ parameterSpectrum := by
  simp [mem_parameterSpectrum_iff, parameterSum]

theorem linearPolynomial_ne_zero : linearPolynomial ≠ 0 := by
  intro h
  have htwo : (2 : Fin 3) ≠ 0 := by decide
  have hv := congrArg (eval (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)) h
  norm_num [linearPolynomial, htwo] at hv

theorem quadraticPolynomial_ne_zero : quadraticPolynomial ≠ 0 :=
  pow_ne_zero _ linearPolynomial_ne_zero

theorem quadraticPolynomial_homogeneous : quadraticPolynomial.IsHomogeneous 2 := by
  have h : linearPolynomial.IsHomogeneous 1 :=
    ((isHomogeneous_X ℝ (0 : Fin 3)).add (isHomogeneous_X ℝ 1)).add (isHomogeneous_X ℝ 2)
  simpa [quadraticPolynomial, pow_two] using h.mul h

theorem quadraticPolynomial_degree : quadraticPolynomial.totalDegree = 2 := by
  exact quadraticPolynomial_homogeneous.totalDegree quadraticPolynomial_ne_zero

def chart (z : Fin 2 → ℝ) : Param := ![z 0, z 1, -(z 0 + z 1)]

theorem chart_mem (z : Fin 2 → ℝ) : chart z ∈ parameterSpectrum := by
  rw [mem_parameterSpectrum_iff]
  simp [chart, parameterSum]

def spectralChart (z : Fin 2 → ℝ) : parameterSpectrum := ⟨chart z, chart_mem z⟩

theorem chart_recover (x : parameterSpectrum) :
    chart ![x.1 0, x.1 1] = x.1 := by
  have hx := (mem_parameterSpectrum_iff x.1).mp x.2
  funext i
  fin_cases i
  · simp [chart]
  · simp [chart]
  · simp [chart]
    dsimp [parameterSum] at hx
    linarith

def projection : Poly3 →ₐ[ℝ] Poly2 :=
  aeval (![X 0, X 1, -(X 0 + X 1)] : Fin 3 → Poly2)

def inclusion : Poly2 →ₐ[ℝ] Poly3 :=
  aeval (![X 0, X 1] : Fin 2 → Poly3)

theorem projection_inclusion : projection.comp inclusion = AlgHom.id ℝ Poly2 := by
  ext i
  fin_cases i <;> simp [projection, inclusion]

theorem projection_surjective : Function.Surjective projection := by
  intro p
  exact ⟨inclusion p, AlgHom.congr_fun projection_inclusion p⟩

theorem eval_projection (p : Poly3) (z : Fin 2 → ℝ) :
    eval z (projection p) = eval (chart z) p := by
  have h : (aeval z : Poly2 →ₐ[ℝ] ℝ).comp projection = aeval (chart z) := by
    ext i
    fin_cases i <;> simp [projection, chart]
  exact AlgHom.congr_fun h p

/- Actual restriction of every polynomial to every point of the true spectrum. -/
def restriction : Poly3 →ₐ[ℝ] (parameterSpectrum → ℝ) where
  toFun p x := eval x.1 p
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' p q := by ext x; simp
  map_mul' p q := by ext x; simp
  commutes' r := by ext x; simp

def vanishingIdeal : Ideal Poly3 := RingHom.ker restriction.toRingHom
abbrev CoordinateRing := Poly3 ⧸ vanishingIdeal

theorem mem_vanishingIdeal_iff (p : Poly3) :
    p ∈ vanishingIdeal ↔ ∀ x : parameterSpectrum, eval x.1 p = 0 := by
  change restriction p = 0 ↔ _
  constructor
  · intro h x
    exact congrFun h x
  · intro h
    funext x
    exact h x

theorem vanishingIdeal_eq_projection_ker :
    vanishingIdeal = RingHom.ker projection.toRingHom := by
  ext p
  rw [mem_vanishingIdeal_iff, RingHom.mem_ker]
  change (∀ x : parameterSpectrum, eval x.1 p = 0) ↔ projection p = 0
  constructor
  · intro h
    apply MvPolynomial.funext
    intro z
    rw [map_zero, eval_projection]
    exact h (spectralChart z)
  · intro h x
    have hv := congrArg (eval (![x.1 0, x.1 1] : Fin 2 → ℝ)) h
    rw [eval_projection, chart_recover, map_zero] at hv
    exact hv

def coordinateEquiv : CoordinateRing ≃ₐ[ℝ] Poly2 :=
  (Ideal.quotientEquivAlgOfEq ℝ vanishingIdeal_eq_projection_ker).trans
    (Ideal.quotientKerAlgEquivOfSurjective projection_surjective)

theorem coordinateRing_dimension : ringKrullDim CoordinateRing = 2 := by
  rw [ringKrullDim_eq_of_ringEquiv coordinateEquiv.toRingEquiv]
  simp [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]

theorem coordinateRing_not_dimension_one : ringKrullDim CoordinateRing ≠ 1 := by
  rw [coordinateRing_dimension]
  norm_num

theorem affine_parameter_spectrum_counterexample :
    quadraticPolynomial.totalDegree = 2 ∧
    (∀ x, pencil x = eval x quadraticPolynomial • (1 : Operator)) ∧
    (∀ x, IsSelfAdjoint (pencil x)) ∧
    parameterSpectrum.Nonempty ∧ parameterSpectrum ≠ Set.univ ∧
    ringKrullDim CoordinateRing = 2 ∧ ringKrullDim CoordinateRing ≠ 1 := by
  refine ⟨quadraticPolynomial_degree, pencil_polynomial, pencil_selfAdjoint,
    ⟨0, zero_mem_parameterSpectrum⟩, ?_, coordinateRing_dimension,
    coordinateRing_not_dimension_one⟩
  intro h
  exact basis_not_mem_parameterSpectrum (h.symm ▸ Set.mem_univ _)

end TLMC7474
