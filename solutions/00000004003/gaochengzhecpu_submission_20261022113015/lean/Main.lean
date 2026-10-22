import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Conjecture4003

abbrev PathSpace := C(ℝ, ℝ)
instance : MeasurableSpace PathSpace := borel PathSpace
instance : BorelSpace PathSpace := ⟨rfl⟩
abbrev ObservedPath := C(Set.Icc (0 : ℝ) 1, ℝ)
instance : MeasurableSpace ObservedPath := borel ObservedPath
instance : BorelSpace ObservedPath := ⟨rfl⟩

def observe (p : PathSpace) : ObservedPath := p.restrict (Set.Icc (0 : ℝ) 1)
def observedLaw (μ : Measure PathSpace) : Measure ObservedPath := μ.map observe

theorem continuous_observe : Continuous observe := ContinuousMap.continuous_restrict _

/-- Actual one-dimensional iterated integrals on [0,t]. -/
def signature (p : PathSpace) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, t => intervalIntegral (fun s => signature p n s * deriv p s) 0 t volume

def curve (a : ℝ) : PathSpace :=
  ⟨fun t => 4 * a * t * (1 - t), by fun_prop⟩

theorem curve_midpoint (a : ℝ) : curve a (1 / 2) = a := by
  dsimp [curve]
  ring

theorem curve_endpoints (a : ℝ) : curve a 0 = 0 ∧ curve a 1 = 0 := by
  norm_num [curve]

theorem curve_injective : Function.Injective curve := by
  intro a b h
  have hh := congrArg (fun p : PathSpace => p (1 / 2)) h
  simpa only [curve_midpoint] using hh

theorem curve_hasDerivAt (a t : ℝ) :
    HasDerivAt (curve a) (4 * a * (1 - 2 * t)) t := by
  convert ((hasDerivAt_id t).mul ((hasDerivAt_id t).const_sub 1)).const_mul (4 * a) using 1 <;>
    dsimp [curve] <;> ring

theorem curve_deriv (a : ℝ) : deriv (curve a) = fun t => 4 * a * (1 - 2 * t) := by
  funext t
  exact (curve_hasDerivAt a t).deriv

theorem curve_signature (a : ℝ) (n : ℕ) (t : ℝ) :
    signature (curve a) n t = (curve a t) ^ n / (n.factorial : ℝ) := by
  induction n generalizing t with
  | zero => simp [signature]
  | succ n ih =>
    simp only [signature, ih, curve_deriv]
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    have hd (s : ℝ) :
        HasDerivAt (fun x : ℝ => (curve a x) ^ (n + 1) / ((n + 1).factorial : ℝ))
          ((curve a s) ^ n / (n.factorial : ℝ) * (4 * a * (1 - 2 * s))) s := by
      convert ((curve_hasDerivAt a s).pow (n + 1)).div_const ((n + 1).factorial : ℝ) using 1
      simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    have hc : Continuous (fun s : ℝ =>
        (curve a s) ^ n / (n.factorial : ℝ) * (4 * a * (1 - 2 * s))) := by
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable _ _)]
    simp [curve]

def expectedSignature (μ : Measure PathSpace) (n : ℕ) : ℝ :=
  ∫ p, signature p n 1 ∂μ

def firstLaw : Measure PathSpace := Measure.dirac (curve 1)
def secondLaw : Measure PathSpace := Measure.dirac (curve 2)

theorem all_expected_signatures_equal (n : ℕ) :
    expectedSignature firstLaw n = expectedSignature secondLaw n := by
  simp only [expectedSignature, firstLaw, secondLaw, integral_dirac]
  rw [curve_signature, curve_signature]
  norm_num [curve]

theorem different_laws : firstLaw ≠ secondLaw := by
  intro h
  have hp : curve 1 = curve 2 := injective_dirac h
  have hh := congrArg (fun p : PathSpace => p (1 / 2)) hp
  norm_num [curve] at hh

theorem different_observed_laws : observedLaw firstLaw ≠ observedLaw secondLaw := by
  intro h
  simp only [observedLaw, firstLaw, secondLaw,
    Measure.map_dirac continuous_observe.measurable] at h
  have hp := injective_dirac h
  have hh := congrArg (fun p : ObservedPath => p ⟨1 / 2, by constructor <;> norm_num⟩) hp
  norm_num [observe, curve] at hh

/-- Supremum norm on the actual observation interval [0,1]. -/
def radius (p : PathSpace) : ℝ := ‖p.restrict (Set.Icc (0 : ℝ) 1)‖

theorem radius_curve_eq {a : ℝ} (ha : 0 ≤ a) : radius (curve a) = a := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ ha).mpr
    intro t
    change |4 * a * (t : ℝ) * (1 - (t : ℝ))| ≤ a
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hnonneg : 0 ≤ 4 * a * (t : ℝ) * (1 - (t : ℝ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha) ht0) (sub_nonneg.mpr ht1)
    rw [abs_of_nonneg hnonneg]
    nlinarith [mul_nonneg ha (sq_nonneg (2 * (t : ℝ) - 1))]
  · have h := ContinuousMap.norm_coe_le_norm ((curve a).restrict (Set.Icc (0 : ℝ) 1))
      ⟨1 / 2, by constructor <;> norm_num⟩
    change ‖curve a (1 / 2)‖ ≤ radius (curve a) at h
    simpa only [curve_midpoint, Real.norm_eq_abs, abs_of_nonneg ha] using h

def moment (μ : Measure PathSpace) (n : ℕ) : ℝ := ∫ p, radius p ^ n ∂μ

/-- The usual divergent inverse-even-moment-root condition, with finite moments. -/
def Carleman (μ : Measure PathSpace) : Prop :=
  (∀ n : ℕ, Integrable (fun p => radius p ^ n) μ) ∧
  (∀ n : ℕ, 0 < moment μ (2 * (n + 1))) ∧
  ¬ Summable (fun n : ℕ =>
    (moment μ (2 * (n + 1)) ^ (((2 * (n + 1) : ℕ) : ℝ)⁻¹))⁻¹)

theorem radius_curve_positive {a : ℝ} (ha : 0 < a) : 0 < radius (curve a) := by
  rw [radius_curve_eq ha.le]
  exact ha

theorem dirac_carleman (p : PathSpace) (hp : 0 < radius p) :
    Carleman (Measure.dirac p) := by
  refine ⟨fun _ => integrable_dirac, ?_, ?_⟩
  · intro n
    simpa [moment, integral_dirac] using pow_pos hp (2 * (n + 1))
  · have he : (fun n : ℕ =>
        (moment (Measure.dirac p) (2 * (n + 1)) ^ (((2 * (n + 1) : ℕ) : ℝ)⁻¹))⁻¹) =
        (fun _ : ℕ => (radius p)⁻¹) := by
      funext n
      simp only [moment, integral_dirac]
      rw [Real.pow_rpow_inv_natCast hp.le
        (Nat.mul_ne_zero (by decide) (Nat.succ_ne_zero n))]
    rw [he]
    exact fun hs => (inv_ne_zero hp.ne') ((summable_const_iff _).mp hs)

theorem first_carleman : Carleman firstLaw :=
  dirac_carleman _ (radius_curve_positive (by norm_num))

theorem second_carleman : Carleman secondLaw :=
  dirac_carleman _ (radius_curve_positive (by norm_num))

def SmoothBasedLaw (μ : Measure PathSpace) : Prop :=
  ∀ᵐ (p : PathSpace) ∂μ, p 0 = 0 ∧ ContDiff ℝ 1 (p : ℝ → ℝ)

theorem curve_smooth (a : ℝ) : ContDiff ℝ 1 (curve a) := by
  change ContDiff ℝ 1 (fun t : ℝ => 4 * a * t * (1 - t))
  exact (contDiff_const.mul contDiff_id).mul (contDiff_const.sub contDiff_id)

theorem first_smooth : SmoothBasedLaw firstLaw := by
  simpa [SmoothBasedLaw, firstLaw, curve] using
    (show (curve 1) 0 = 0 ∧ ContDiff ℝ 1 (curve 1) from ⟨by norm_num [curve], curve_smooth 1⟩)

theorem second_smooth : SmoothBasedLaw secondLaw := by
  simpa [SmoothBasedLaw, secondLaw, curve] using
    (show (curve 2) 0 = 0 ∧ ContDiff ℝ 1 (curve 2) from ⟨by norm_num [curve], curve_smooth 2⟩)

def CarlemanSignatureDetermination : Prop :=
  ∀ μ ν : Measure PathSpace,
    IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    SmoothBasedLaw μ → SmoothBasedLaw ν →
    Carleman μ → Carleman ν →
    (∀ n, Integrable (fun p => signature p n 1) μ) →
    (∀ n, Integrable (fun p => signature p n 1) ν) →
    (∀ n, expectedSignature μ n = expectedSignature ν n) → observedLaw μ = observedLaw ν

theorem conjecture_false : ¬ CarlemanSignatureDetermination := by
  intro h
  apply different_observed_laws
  apply h firstLaw secondLaw
  · exact Measure.dirac.isProbabilityMeasure
  · exact Measure.dirac.isProbabilityMeasure
  · exact first_smooth
  · exact second_smooth
  · exact first_carleman
  · exact second_carleman
  · intro _
    exact integrable_dirac
  · intro _
    exact integrable_dirac
  · exact all_expected_signatures_equal

#print axioms curve_signature
#print axioms first_carleman
#print axioms second_carleman
#print axioms conjecture_false

end Conjecture4003
