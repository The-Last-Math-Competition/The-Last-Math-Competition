import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open MeasureTheory
namespace Conjecture7367
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def path (x y : E) (t : ℝ) : E := x + t • (y - x)
def average (D : E → E →L[ℝ] ℝ) (x y : E) : E →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, D (path x y t)

theorem path_deriv (x y : E) (t : ℝ) : HasDerivAt (path x y) (y - x) t := by
  simpa only [path, one_smul] using ((hasDerivAt_id t).smul_const (y - x)).const_add x

theorem path_continuous (x y : E) : Continuous (path x y) := by
  exact continuous_const.add (continuous_id.smul continuous_const)

theorem average_identity (H : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (hD : ∀ z, HasFDerivAt H (D z) z) (hc : Continuous D) (x y : E) :
    average D x y (y - x) = H y - H x := by
  have hcont : Continuous (fun t : ℝ => D (path x y t)) := hc.comp (path_continuous x y)
  rw [average, ContinuousLinearMap.intervalIntegral_apply (hcont.intervalIntegrable 0 1)]
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun t => H (path x y t)) (f' := fun t => D (path x y t) (y - x))
    (fun t _ => (hD _).comp_hasDerivAt t (path_deriv x y t))
    ((hcont.clm_apply continuous_const).intervalIntegrable 0 1)
  simpa [path] using hf

theorem energy_conserved (H : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (hD : ∀ z, HasFDerivAt H (D z) z) (hc : Continuous D)
    (J : (E →L[ℝ] ℝ) → E) (hJ : ∀ g : E →L[ℝ] ℝ, g (J g) = 0)
    (x y : E) (h : ℝ) (hstep : y - x = h • J (average D x y)) :
    H y = H x := by
  have hi := average_identity H D hD hc x y
  rw [hstep, map_smul, hJ, smul_zero] at hi
  exact sub_eq_zero.mp hi.symm

theorem average_diagonal (D : E → E →L[ℝ] ℝ) (x : E) :
    average D x x = D x := by
  simp [average, path]

/-- The AVF covector is the actual interval average of the Frechet derivative. -/
def avf (H : E → ℝ) (x y : E) : E →L[ℝ] ℝ := average (fderiv ℝ H) x y

/-- The exact discrete-gradient identity, consistency, and energy preservation
for every step of the average-vector-field method. -/
def Claim (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ H : E → ℝ, Differentiable ℝ H → Continuous (fderiv ℝ H) →
    (∀ x y, avf H x y (y - x) = H y - H x) ∧
    (∀ x, avf H x x = fderiv ℝ H x) ∧
    (∀ J : (E →L[ℝ] ℝ) → E, (∀ g : E →L[ℝ] ℝ, g (J g) = 0) →
      ∀ (x y : E) (h : ℝ), y - x = h • J (avf H x y) → H y = H x)

theorem conjecture7367 : Claim E := by
  intro H hH hc
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact average_identity H (fderiv ℝ H) (fun z => (hH z).hasFDerivAt) hc x y
  · intro x
    exact average_diagonal (fderiv ℝ H) x
  · intro J hJ x y h hs
    exact energy_conserved H (fderiv ℝ H) (fun z => (hH z).hasFDerivAt) hc J hJ x y h hs

#print axioms average_identity
#print axioms energy_conserved
#print axioms average_diagonal
#print axioms conjecture7367
end Conjecture7367
