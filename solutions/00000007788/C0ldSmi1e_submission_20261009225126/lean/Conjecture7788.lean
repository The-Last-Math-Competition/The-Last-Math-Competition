import Conjecture7788.HullMeasurable
import Conjecture7788.GenericRate
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Asymptotics

namespace Conjecture7788

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def disk : Set Plane := closedBall 0 1

noncomputable def uniformDisk : Measure Plane := ProbabilityTheory.cond volume disk

lemma volume_disk : volume disk = ENNReal.ofReal Real.pi := by
  simp [disk]

instance uniformDisk_probability : IsProbabilityMeasure uniformDisk := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [volume_disk]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr Real.pi_pos)
  · rw [volume_disk]
    exact ENNReal.ofReal_ne_top

noncomputable def samples (N : ℕ) : Measure (Fin N → Plane) :=
  Measure.pi (fun _ => uniformDisk)

instance samples_probability (N : ℕ) : IsProbabilityMeasure (samples N) := by
  unfold samples
  infer_instance

/-- The joint law has exactly the rectangle probabilities of independent uniform samples. -/
lemma samples_rectangle (N : ℕ) (s : Fin N → Set Plane) :
    samples N (Set.univ.pi s) = ∏ i, uniformDisk (s i) :=
  Measure.pi_pi (fun _ => uniformDisk) s

noncomputable def hullArea {N : ℕ} (x : Fin N → Plane) : ℝ :=
  (volume (convexHull ℝ (Set.range x))).toReal / Real.pi

noncomputable def deficit (N : ℕ) : ℝ :=
  1 - ∫ x, hullArea x ∂samples N

/-- The chosen deficit is exactly the expected-volume deficit in the source statement. -/
lemma deficit_eq_expected_volume_deficit (N : ℕ) :
    deficit N = 1 -
      (∫ x : Fin N → Plane, (volume (convexHull ℝ (Set.range x))).toReal ∂samples N) /
      (volume disk).toReal := by
  simp only [deficit, hullArea, integral_div, volume_disk,
    ENNReal.toReal_ofReal Real.pi_pos.le]

/-- A finite sample always has a finite-area convex hull. -/
lemma hull_volume_ne_top {N : ℕ} (x : Fin N → Plane) :
    volume (convexHull ℝ (Set.range x)) ≠ ⊤ :=
  (Set.finite_range x).isCompact_convexHull.measure_lt_top.ne

lemma hullArea_nonneg {N : ℕ} (x : Fin N → Plane) : 0 ≤ hullArea x :=
  div_nonneg ENNReal.toReal_nonneg Real.pi_pos.le

lemma hullArea_le {N : ℕ} {x : Fin N → Plane} {r : ℝ} (hr : 0 ≤ r)
    (hx : ∀ i, x i ∈ closedBall 0 r) : hullArea x ≤ r ^ 2 := by
  have hs : convexHull ℝ (range x) ⊆ closedBall 0 r := by
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      exact hx i
    · exact convex_closedBall 0 r
  have hv := measure_mono (μ := (volume : Measure Plane)) hs
  have hb : (volume (closedBall (0 : Plane) r)).toReal = r ^ 2 * Real.pi := by
    simp [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
      ENNReal.toReal_ofReal Real.pi_pos.le]
  have ht : volume (closedBall (0 : Plane) r) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hreal := ENNReal.toReal_mono ht hv
  rw [hb] at hreal
  exact (div_le_iff₀ Real.pi_pos).2 hreal

/-- Event that all N independently sampled points lie in a concentric radius-r disk. -/
def innerEvent (N : ℕ) (r : ℝ) : Set (Fin N → Plane) :=
  Set.univ.pi (fun _ => closedBall 0 r)

lemma innerEvent_measurable (N : ℕ) (r : ℝ) : MeasurableSet (innerEvent N r) := by
  exact MeasurableSet.univ_pi (fun _ => isClosed_closedBall.measurableSet)

lemma uniformDisk_inner (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    uniformDisk (closedBall 0 r) = ENNReal.ofReal (r ^ 2) := by
  have hs : closedBall (0 : Plane) r ⊆ disk := closedBall_subset_closedBall hr1
  rw [uniformDisk, cond_apply (show MeasurableSet disk from isClosed_closedBall.measurableSet)]
  rw [Set.inter_eq_right.mpr hs, volume_disk, EuclideanSpace.volume_closedBall_fin_two]
  rw [← ENNReal.ofReal_pow hr]
  have hp0 : ENNReal.ofReal Real.pi ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr Real.pi_pos)
  have hpT : ENNReal.ofReal Real.pi ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [mul_left_comm, ENNReal.inv_mul_cancel hp0 hpT, mul_one]

lemma innerEvent_probability (N : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (samples N).real (innerEvent N r) = (r ^ 2) ^ N := by
  simp only [Measure.real, samples, innerEvent, Measure.pi_pi,
    uniformDisk_inner r hr hr1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (sq_nonneg r)]

lemma samples_in_disk (N : ℕ) : ∀ᵐ x ∂samples N, ∀ i, x i ∈ disk := by
  apply Filter.eventually_all.mpr
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually (ae_cond_mem isClosed_closedBall.measurableSet)

lemma hullArea_measurable (N : ℕ) : Measurable (@hullArea N) :=
  (hull_volume_measurable N).ennreal_toReal.div_const Real.pi

lemma hullArea_integrable (N : ℕ) : Integrable (@hullArea N) (samples N) := by
  refine (integrable_const (1 : ℝ)).mono' (hullArea_measurable N).aestronglyMeasurable ?_
  filter_upwards [samples_in_disk N] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hullArea_nonneg x)]
  simpa using hullArea_le (x := x) (r := 1) (by norm_num) hx

/-- The unnormalized random hull volume is also an ordinary integrable random variable. -/
lemma hull_volume_integrable (N : ℕ) :
    Integrable (fun x : Fin N → Plane => (volume (convexHull ℝ (range x))).toReal)
      (samples N) := by
  convert (hullArea_integrable N).mul_const Real.pi using 1
  ext x
  simp [hullArea, Real.pi_ne_zero]

lemma deficit_lower_from_radius (N : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hInt : Integrable (@hullArea N) (samples N)) :
    (1 - r ^ 2) * (r ^ 2) ^ N ≤ deficit N := by
  let E := innerEvent N r
  have hE : MeasurableSet E := innerEvent_measurable N r
  let envelope : (Fin N → Plane) → ℝ :=
    fun x => 1 - E.indicator (fun _ => 1 - r ^ 2) x
  have henv : Integrable envelope (samples N) :=
    (integrable_const 1).sub ((integrable_const (1 - r ^ 2)).indicator hE)
  have hbound : ∀ᵐ x ∂samples N, hullArea x ≤ envelope x := by
    filter_upwards [samples_in_disk N] with x hx
    by_cases he : x ∈ E
    · have hxr : ∀ i, x i ∈ closedBall 0 r := fun i => he i (mem_univ i)
      simpa [envelope, Set.indicator_of_mem he] using hullArea_le hr hxr
    · have hxu := hullArea_le (x := x) (r := 1) (by norm_num) hx
      simpa [envelope, Set.indicator_of_not_mem he] using hxu
  have hm := integral_mono_ae hInt henv hbound
  have heval : ∫ x, envelope x ∂samples N =
      1 - (samples N).real E * (1 - r ^ 2) := by
    change (∫ x, (1 : ℝ) - E.indicator (fun _ => 1 - r ^ 2) x ∂samples N) = _
    rw [integral_sub (integrable_const (1 : ℝ)) ((integrable_const (1 - r ^ 2)).indicator hE)]
    rw [integral_indicator_const _ hE]
    simp
  rw [heval, innerEvent_probability N r hr hr1] at hm
  unfold deficit
  nlinarith

lemma deficit_lower (N : ℕ) :
    1 / (4 * ((N : ℝ) + 1)) ≤ deficit N := by
  let t : ℝ := 1 / (2 * ((N : ℝ) + 1))
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hden : 0 < 2 * ((N : ℝ) + 1) := by positivity
  have htpos : 0 < t := by dsimp [t]; positivity
  have htle : t ≤ 1 / 2 := by
    dsimp [t]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hu : 0 ≤ 1 - t := by linarith
  have hsqrt : (Real.sqrt (1 - t)) ^ 2 = 1 - t := Real.sq_sqrt hu
  have hr1 : Real.sqrt (1 - t) ≤ 1 := by
    apply (Real.sqrt_le_one).2
    linarith
  have hb := deficit_lower_from_radius N (Real.sqrt (1 - t))
    (Real.sqrt_nonneg _) hr1 (hullArea_integrable N)
  rw [hsqrt] at hb
  have hber := one_add_mul_le_pow (a := -t) (by linarith : (-2 : ℝ) ≤ -t) N
  have hNt : (N : ℝ) * t ≤ 1 / 2 := by
    dsimp [t]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hpow : 1 / 2 ≤ (1 - t) ^ N := by
    simp only [mul_neg, ← sub_eq_add_neg] at hber
    linarith
  have hlower : t / 2 ≤ deficit N := by
    have := mul_le_mul_of_nonneg_left hpow htpos.le
    nlinarith
  have heq : t / 2 = 1 / (4 * ((N : ℝ) + 1)) := by
    dsimp [t]
    field_simp
    ring
  rwa [heq] at hlower

/-- The normalized deficit for independent interior-uniform disk samples diverges. -/
theorem normalized_deficit_tendsto_atTop :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * deficit N) atTop atTop :=
  GenericRate.quadratic_tendsto_atTop deficit deficit_lower

/-- No finite constant can be the claimed dimension-two leading coefficient. -/
theorem no_finite_normalized_limit (c : ℝ) :
    ¬ Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * deficit N) atTop (𝓝 c) :=
  GenericRate.quadratic_not_tendsto_nhds deficit deficit_lower c

/-- The ratio to each positive conjectured dimension-two power law diverges. -/
theorem deficit_ratio_tendsto_atTop (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => deficit N / (c * (N : ℝ) ^ (-2 : ℝ))) atTop atTop :=
  GenericRate.real_power_ratio_tendsto_atTop deficit deficit_lower c hc

/-- The exponent in the source is `-2` when the dimension is two. -/
lemma source_exponent_dimension_two : -(2 : ℝ) / ((2 : ℝ) - 1) = -2 := by norm_num

/-- The necessary disk assertion of conjecture 00000007788 is false. -/
theorem conjecture_00000007788_false :
    ¬ ∃ c : ℝ, 0 < c ∧
      (deficit ~[atTop] (fun N : ℕ => c * (N : ℝ) ^ (-2 : ℝ))) := by
  rintro ⟨c, hc, h⟩
  exact GenericRate.not_isEquivalent_real_power deficit deficit_lower c hc h

end Conjecture7788
