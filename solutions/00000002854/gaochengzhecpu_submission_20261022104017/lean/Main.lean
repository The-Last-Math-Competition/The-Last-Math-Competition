import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Matrix
open MeasureTheory ProbabilityTheory

namespace Conjecture2854

/-- A single latent factor and an error term, both with fixed variance one.
The observed variable is Y = (a * parameter + b) H + E. -/
def loading (a b parameter : ℝ) : Matrix (Fin 1) (Fin 2) ℝ :=
  fun _ j => if j = 0 then a * parameter + b else 1

/-- The covariance matrix of the two centered, uncorrelated exogenous terms. -/
def exogenousCovariance : Matrix (Fin 2) (Fin 2) ℝ := 1

/-- The actual observed covariance, computed by L Sigma L-transpose. -/
def observedCovariance (a b parameter : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  loading a b parameter * exogenousCovariance * (loading a b parameter).transpose

def parameterMap (a b parameter : ℝ) : ℝ :=
  observedCovariance a b parameter 0 0

theorem observedCovariance_apply (a b parameter : ℝ) (i j : Fin 1) :
    observedCovariance a b parameter i j = (a * parameter + b) ^ 2 + 1 := by
  simp [observedCovariance, exogenousCovariance, Matrix.mul_apply,
    Fin.sum_univ_two, loading, Matrix.transpose_apply]
  ring

theorem parameterMap_eq (a b parameter : ℝ) :
    parameterMap a b parameter = (a * parameter + b) ^ 2 + 1 :=
  observedCovariance_apply a b parameter 0 0

/-- The ordinary Jacobian of this one-dimensional covariance parametrization. -/
noncomputable def jacobian (a b parameter : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => deriv (parameterMap a b) parameter

def GenericFullRank (a b : ℝ) : Prop :=
  ∃ exceptional : Finset ℝ, ∀ parameter ∉ exceptional,
    (jacobian a b parameter).det ≠ 0

/-- Strict, labelled parameter identifiability from the entire observed covariance matrix. -/
def GloballyIdentifiable (a b : ℝ) : Prop :=
  Function.Injective (observedCovariance a b)

/-- The source's necessary proposed equivalence, restricted to actual affine single-factor SEMs. -/
def RankCriterion : Prop :=
  ∀ a b : ℝ, GenericFullRank a b ↔ GloballyIdentifiable a b

theorem hasDerivAt_counterexample (parameter : ℝ) :
    HasDerivAt (parameterMap 1 0) (2 * parameter) parameter := by
  have h := ((hasDerivAt_id parameter).pow 2).add_const (1 : ℝ)
  have heq : parameterMap 1 0 = fun x : ℝ => x ^ 2 + 1 := by
    funext x
    rw [parameterMap_eq]
    ring
  rw [heq]
  simpa only [id, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using h

theorem jacobian_det_counterexample (parameter : ℝ) :
    (jacobian 1 0 parameter).det = 2 * parameter := by
  simp [jacobian, Matrix.det_fin_one, (hasDerivAt_counterexample parameter).deriv]

theorem generic_full_rank : GenericFullRank 1 0 := by
  classical
  refine ⟨{0}, ?_⟩
  intro parameter hparameter
  have hp : parameter ≠ 0 := by simpa using hparameter
  rw [jacobian_det_counterexample]
  exact mul_ne_zero (by norm_num) hp

theorem sign_ambiguity (parameter : ℝ) :
    observedCovariance 1 0 parameter = observedCovariance 1 0 (-parameter) := by
  ext i j
  simp only [observedCovariance_apply]
  ring

theorem not_globally_identifiable : ¬ GloballyIdentifiable 1 0 := by
  intro h
  have hbad : (1 : ℝ) = -1 := h (sign_ambiguity 1)
  norm_num at hbad

/-- Ambiguity occurs at every nonzero parameter, not merely at exceptional singular points. -/
theorem generic_two_distinct_parameters (parameter : ℝ) (hp : parameter ≠ 0) :
    parameter ≠ -parameter ∧
    observedCovariance 1 0 parameter = observedCovariance 1 0 (-parameter) := by
  refine ⟨?_, sign_ambiguity parameter⟩
  intro h
  apply hp
  linarith

/-- A concrete independent standard Gaussian latent factor and error. -/
noncomputable def exogenousLaw : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

def output (parameter : ℝ) (z : ℝ × ℝ) : ℝ := parameter * z.1 + z.2

def reflectLatent (z : ℝ × ℝ) : ℝ × ℝ := (-z.1, z.2)

theorem reflectLatent_preserves_law :
    exogenousLaw.map reflectLatent = exogenousLaw := by
  have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_const_mul (μ := 0) (v := 1) (-1))
  have hprod := Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1)
    (measurable_id.neg) measurable_id
  simpa [exogenousLaw, reflectLatent, hneg, Function.id_def, Prod.map] using hprod.symm

/-- The sign ambiguity persists at the level of the entire observed Gaussian law. -/
theorem output_law_sign (parameter : ℝ) :
    exogenousLaw.map (output parameter) = exogenousLaw.map (output (-parameter)) := by
  have ho : Measurable (output (-parameter)) :=
    (measurable_const.mul measurable_fst).add measurable_snd
  have hr : Measurable reflectLatent :=
    measurable_fst.neg.prodMk measurable_snd
  have heq : output (-parameter) ∘ reflectLatent = output parameter := by
    funext z
    simp [output, reflectLatent, Function.comp_def]
  rw [← heq, ← Measure.map_map ho hr, reflectLatent_preserves_law]

theorem disprove_rank_criterion : ¬ RankCriterion := by
  intro h
  exact not_globally_identifiable ((h 1 0).mp generic_full_rank)

end Conjecture2854

#print axioms Conjecture2854.generic_full_rank
#print axioms Conjecture2854.sign_ambiguity
#print axioms Conjecture2854.generic_two_distinct_parameters
#print axioms Conjecture2854.output_law_sign
#print axioms Conjecture2854.disprove_rank_criterion
