import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ENNReal RealInnerProductSpace
open MeasureTheory Metric Set

namespace Conjecture1030

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev S2 := Metric.sphere (0 : E) 1

def surface : Measure S2 := Measure.hausdorffMeasure 2

def sigma : Measure S2 := (surface Set.univ)⁻¹ • surface

def evalOnSphere (p : MvPolynomial (Fin 3) ℝ) (x : S2) : ℝ :=
  MvPolynomial.eval (fun i => (x : E) i) p

/-- Unweighted, nonempty finite sets and all real polynomials of total degree at most t. -/
def SphericalDesign (t : ℕ) (X : Finset S2) : Prop :=
  X.Nonempty ∧ ∀ p : MvPolynomial (Fin 3) ℝ, p.totalDegree ≤ t →
    (X.card : ℝ)⁻¹ * ∑ x ∈ X, evalOnSphere p x = ∫ x, evalOnSphere p x ∂sigma

/-- The same exactness predicate, parameterized for internal measure lemmas. -/
def DesignFor (μ : Measure S2) (t : ℕ) (X : Finset S2) : Prop :=
  X.Nonempty ∧ ∀ p : MvPolynomial (Fin 3) ℝ, p.totalDegree ≤ t →
    (X.card : ℝ)⁻¹ * ∑ x ∈ X, evalOnSphere p x = ∫ x, evalOnSphere p x ∂μ

@[simp] theorem designFor_sigma (t : ℕ) (X : Finset S2) :
    DesignFor sigma t X ↔ SphericalDesign t X := Iff.rfl

@[simp] theorem sphere_norm (x : S2) : ‖(x : E)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

/-- Restriction of an actual Euclidean linear isometry to the unit sphere. -/
def sphereIso (U : E ≃ₗᵢ[ℝ] E) : S2 ≃ᵢ S2 where
  toFun x := ⟨U (x : E), by simp only [Metric.mem_sphere, dist_zero_right, U.norm_map, sphere_norm]⟩
  invFun x := ⟨U.symm (x : E), by simp only [Metric.mem_sphere, dist_zero_right, U.symm.norm_map, sphere_norm]⟩
  left_inv x := Subtype.ext (U.symm_apply_apply (x : E))
  right_inv x := Subtype.ext (U.apply_symm_apply (x : E))
  isometry_toFun x y := U.isometry (x : E) (y : E)

@[simp] theorem sphereIso_coe (U : E ≃ₗᵢ[ℝ] E) (x : S2) :
    ((sphereIso U x : S2) : E) = U (x : E) := rfl

/-- Internal hypothesis; it must be proved for sigma before any final design theorem. -/
def OrthogonallyInvariant (μ : Measure S2) : Prop :=
  ∀ U : E ≃ₗᵢ[ℝ] E, MeasurePreserving (sphereIso U) μ μ

 theorem norm_sq3 (x : E) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp [PiLp.inner_apply, Fin.sum_univ_succ, pow_two, add_assoc]

 theorem norm_sq2 (x : E2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp [PiLp.inner_apply, Fin.sum_univ_succ, pow_two, add_assoc]

 theorem inner3 (x y : E) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]

 theorem sphere_sq (x : S2) : (x : E) 0 ^ 2 + (x : E) 1 ^ 2 + (x : E) 2 ^ 2 = 1 := by
  rw [← norm_sq3, sphere_norm]
  norm_num

end Conjecture1030
