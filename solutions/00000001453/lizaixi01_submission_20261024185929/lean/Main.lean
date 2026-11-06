import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section
namespace TLMC1453

def body : Set ℝ := Icc 0 1

theorem body_compact : IsCompact body := isCompact_Icc

theorem body_convex : Convex ℝ body := convex_Icc 0 1

theorem body_interior_nonempty : (interior body).Nonempty := by
  rw [body, interior_Icc]
  exact ⟨1 / 2, by norm_num⟩

theorem body_volume : volume body = 1 := by norm_num [body]

theorem ambient_dimension : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ

def uniform : Measure ℝ := volume.restrict body

instance uniform_probability : IsProbabilityMeasure uniform where
  measure_univ := by simp [uniform, body_volume]

abbrev Sample (n : ℕ) := Fin (n + 2) → ℝ

def sampleMeasure (n : ℕ) : Measure (Sample n) :=
  Measure.pi fun _ => uniform

instance sample_probability (n : ℕ) : IsProbabilityMeasure (sampleMeasure n) := by
  unfold sampleMeasure
  infer_instance

theorem samples_independent (n : ℕ) :
    iIndepFun (fun i (ω : Sample n) => ω i) (sampleMeasure n) := by
  exact iIndepFun_pi (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)

theorem sample_uniform (n : ℕ) (i : Fin (n + 2)) :
    pdf.IsUniform (fun ω : Sample n => ω i) body (sampleMeasure n) volume := by
  change Measure.map (Function.eval i) (Measure.pi (fun _ : Fin (n + 2) => uniform)) =
    ProbabilityTheory.cond volume body
  rw [(measurePreserving_eval (fun _ : Fin (n + 2) => uniform) i).map_eq]
  simp [ProbabilityTheory.cond, uniform, body_volume]

theorem sample_in_body (n : ℕ) :
    ∀ᵐ ω ∂sampleMeasure n, ∀ i, ω i ∈ body := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : Fin (n + 2) => uniform) i).quasiMeasurePreserving.ae
    (ae_restrict_mem measurableSet_Icc)

def lower (n : ℕ) (ω : Sample n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty ω

def upper (n : ℕ) (ω : Sample n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty ω

def right (n : ℕ) (ω : Sample n) : ℝ := 1 - upper n ω

def polytope (n : ℕ) (ω : Sample n) : Set ℝ := convexHull ℝ (Set.range ω)

def deficit (n : ℕ) (ω : Sample n) : ℝ :=
  (volume body).toReal - (volume (polytope n ω)).toReal

theorem lower_le_coordinate (n : ℕ) (ω : Sample n) (i : Fin (n + 2)) :
    lower n ω ≤ ω i := Finset.inf'_le ω (Finset.mem_univ i)

theorem coordinate_le_upper (n : ℕ) (ω : Sample n) (i : Fin (n + 2)) :
    ω i ≤ upper n ω := Finset.le_sup' ω (Finset.mem_univ i)

theorem lower_le_upper (n : ℕ) (ω : Sample n) : lower n ω ≤ upper n ω :=
  (lower_le_coordinate n ω 0).trans (coordinate_le_upper n ω 0)

theorem lower_in_range (n : ℕ) (ω : Sample n) : lower n ω ∈ Set.range ω := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty ω
  exact ⟨i, hi.symm⟩

theorem upper_in_range (n : ℕ) (ω : Sample n) : upper n ω ∈ Set.range ω := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty ω
  exact ⟨i, hi.symm⟩

theorem polytope_interval (n : ℕ) (ω : Sample n) :
    polytope n ω = Icc (lower n ω) (upper n ω) := by
  apply subset_antisymm
  · apply convexHull_min _ (convex_Icc _ _)
    rintro x ⟨i, rfl⟩
    exact ⟨lower_le_coordinate n ω i, coordinate_le_upper n ω i⟩
  · rw [← segment_eq_Icc (lower_le_upper n ω)]
    exact (convex_convexHull ℝ (Set.range ω)).segment_subset
      (subset_convexHull ℝ _ (lower_in_range n ω))
      (subset_convexHull ℝ _ (upper_in_range n ω))

theorem deficit_eq (n : ℕ) (ω : Sample n) :
    deficit n ω = lower n ω + right n ω := by
  rw [deficit, body_volume, ENNReal.toReal_one, polytope_interval, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (lower_le_upper n ω))]
  simp only [right]
  ring

theorem lower_continuous (n : ℕ) : Continuous (lower n) :=
  Continuous.finset_inf'_apply _ (fun i _ => continuous_apply i)

theorem upper_continuous (n : ℕ) : Continuous (upper n) :=
  Continuous.finset_sup'_apply _ (fun i _ => continuous_apply i)

theorem right_continuous (n : ℕ) : Continuous (right n) :=
  continuous_const.sub (upper_continuous n)

theorem deficit_continuous (n : ℕ) : Continuous (deficit n) := by
  have h : deficit n = fun ω => lower n ω + right n ω := funext (deficit_eq n)
  rw [h]
  exact (lower_continuous n).add (right_continuous n)

theorem endpoint_bounds (n : ℕ) :
    ∀ᵐ ω ∂sampleMeasure n,
      (0 ≤ lower n ω ∧ lower n ω ≤ 1) ∧ (0 ≤ right n ω ∧ right n ω ≤ 1) := by
  filter_upwards [sample_in_body n] with ω hω
  have hl : 0 ≤ lower n ω := Finset.le_inf' _ _ (fun i _ => (hω i).1)
  have hu : upper n ω ≤ 1 := Finset.sup'_le _ _ (fun i _ => (hω i).2)
  have hl1 := (lower_le_coordinate n ω 0).trans (hω 0).2
  have hu0 := (hω 0).1.trans (coordinate_le_upper n ω 0)
  exact ⟨⟨hl, hl1⟩, by dsimp [right]; constructor <;> linarith⟩

theorem uniform_upper_tail {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    uniform (Ici t) = ENNReal.ofReal (1 - t) := by
  rw [uniform, Measure.restrict_apply measurableSet_Ici]
  have h : Ici t ∩ body = Icc t 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, body, Set.mem_Icc]
    constructor
    · rintro ⟨htx, _, hx1⟩; exact ⟨htx, hx1⟩
    · rintro ⟨htx, hx1⟩; exact ⟨htx, ht.1.trans htx, hx1⟩
  rw [h, Real.volume_Icc]

theorem uniform_lower_tail {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    uniform (Iic (1 - t)) = ENNReal.ofReal (1 - t) := by
  rw [uniform, Measure.restrict_apply measurableSet_Iic]
  have h : Iic (1 - t) ∩ body = Icc 0 (1 - t) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, body, Set.mem_Icc]
    constructor
    · rintro ⟨hxt, hx0, _⟩; exact ⟨hx0, hxt⟩
    · rintro ⟨hx0, hxt⟩; exact ⟨hxt, hx0, by linarith [ht.1]⟩
  rw [h, Real.volume_Icc, sub_zero]

theorem lower_tail (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sampleMeasure n {ω | t ≤ lower n ω} = ENNReal.ofReal (1 - t) ^ (n + 2) := by
  have h : {ω : Sample n | t ≤ lower n ω} = Set.univ.pi (fun _ => Ici t) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Ici, lower,
      Finset.le_inf'_iff, Finset.mem_univ, true_implies]
  rw [h, sampleMeasure, Measure.pi_pi]
  simp [uniform_upper_tail ht]

theorem right_ge_iff (n : ℕ) (ω : Sample n) (t : ℝ) :
    t ≤ right n ω ↔ ∀ i, ω i ≤ 1 - t := by
  constructor
  · intro h i
    have hi := coordinate_le_upper n ω i
    dsimp [right] at h
    linarith
  · intro h
    have hu : upper n ω ≤ 1 - t := Finset.sup'_le _ _ (fun i _ => h i)
    dsimp [right]
    linarith

theorem right_tail (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sampleMeasure n {ω | t ≤ right n ω} = ENNReal.ofReal (1 - t) ^ (n + 2) := by
  have h : {ω : Sample n | t ≤ right n ω} = Set.univ.pi (fun _ => Iic (1 - t)) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Iic, right_ge_iff]
  rw [h, sampleMeasure, Measure.pi_pi]
  simp [uniform_lower_tail ht]

theorem uniform_interval {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    uniform (Icc u (1 - v)) = ENNReal.ofReal (1 - u - v) := by
  rw [uniform, Measure.restrict_apply measurableSet_Icc]
  have h : Icc u (1 - v) ∩ body = Icc u (1 - v) := by
    apply inter_eq_left.mpr
    intro x hx
    exact ⟨hu.1.trans hx.1, by linarith [hx.2, hv.1]⟩
  rw [h, Real.volume_Icc]
  congr 1
  ring

theorem joint_tail (n : ℕ) {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    sampleMeasure n {ω | u ≤ lower n ω ∧ v ≤ right n ω} =
      ENNReal.ofReal (1 - u - v) ^ (n + 2) := by
  have h : {ω : Sample n | u ≤ lower n ω ∧ v ≤ right n ω} =
      Set.univ.pi (fun _ => Icc u (1 - v)) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc, lower, Finset.le_inf'_iff,
      Finset.mem_univ, true_implies, right_ge_iff]
    exact forall_and.symm
  rw [h, sampleMeasure, Measure.pi_pi]
  simp [uniform_interval hu hv]

theorem integral_cut_power (k : ℕ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    (∫ t, (if t ≤ a then t ^ k else 0) ∂uniform) = a ^ (k + 1) / (k + 1) := by
  change (∫ t, (Iic a).indicator (fun t : ℝ => t ^ k) t ∂uniform) = _
  rw [integral_indicator measurableSet_Iic, uniform,
    Measure.restrict_restrict measurableSet_Iic]
  have h : Iic a ∩ body = Icc 0 a := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, body, Set.mem_Icc]
    constructor
    · rintro ⟨hta, ht0, _⟩; exact ⟨ht0, hta⟩
    · rintro ⟨ht0, hta⟩; exact ⟨hta, ht0, hta.trans ha.2⟩
  rw [h, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.1,
    integral_pow]
  simp

section WeightedTail
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {X W : Ω → ℝ}

theorem weighted_tail (hX : Measurable X) (hW : Measurable W)
    (hXb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1)
    (hWb : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ 1) (k : ℕ) :
    (∫ ω, W ω * (X ω ^ (k + 1) / (k + 1)) ∂μ) =
      ∫ t in Icc (0 : ℝ) 1, t ^ k * ∫ ω in {ω | t ≤ X ω}, W ω ∂μ := by
  let f : Ω × ℝ → ℝ := fun p => if p.2 ≤ X p.1 then W p.1 * p.2 ^ k else 0
  have hfm : Measurable f := by
    exact Measurable.ite (measurableSet_le measurable_snd (hX.comp measurable_fst))
      ((hW.comp measurable_fst).mul (measurable_snd.pow_const k)) measurable_const
  have hfb : ∀ᵐ p ∂μ.prod uniform, ‖f p‖ ≤ 1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hWb,
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := uniform)).ae
        (ae_restrict_mem (μ := volume) measurableSet_Icc)] with p hpW hpt
    dsimp [f]
    split_ifs
    · rw [abs_mul, abs_pow, abs_of_nonneg hpt.1]
      exact mul_le_one₀ hpW (pow_nonneg hpt.1 _) (pow_le_one₀ hpt.1 hpt.2)
    · norm_num
  have hfi : Integrable f (μ.prod uniform) :=
    ((MemLp.of_bound hfm.aestronglyMeasurable 1 hfb : MemLp f 1 (μ.prod uniform))).integrable le_rfl
  have hlhs : (∫ ω, ∫ t, f (ω, t) ∂uniform ∂μ) =
      ∫ ω, W ω * (X ω ^ (k + 1) / (k + 1)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hXb] with ω hω
    have hfun : (fun t => f (ω, t)) =
        fun t => W ω * (if t ≤ X ω then t ^ k else 0) := by
      ext t
      dsimp [f]
      split_ifs <;> simp
    rw [hfun, integral_const_mul, integral_cut_power k hω]
  rw [← hlhs, integral_integral_swap hfi]
  change (∫ t, ∫ ω, f (ω, t) ∂μ ∂uniform) = _
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _
  change (∫ ω, f (ω, t) ∂μ) = t ^ k * ∫ ω in {ω | t ≤ X ω}, W ω ∂μ
  have hfun : (fun ω => f (ω, t)) =
      {ω | t ≤ X ω}.indicator (fun ω => t ^ k * W ω) := by
    ext ω
    dsimp [f]
    by_cases h : t ≤ X ω <;> simp [h, mul_comm]
  rw [hfun, integral_indicator (measurableSet_le measurable_const hX), integral_const_mul]

theorem moment_tail (hX : Measurable X)
    (hXb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    (∫ ω, X ω ^ (k + 1) ∂μ) / (k + 1) =
      ∫ t in Icc (0 : ℝ) 1, t ^ k * μ.real {ω | t ≤ X ω} := by
  have h := weighted_tail hX (W := fun _ => (1 : ℝ)) measurable_const hXb
    (Filter.Eventually.of_forall (fun _ => by norm_num)) k
  simpa only [one_mul, integral_div, integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply MeasurableSet.univ, univ_inter] using h

end WeightedTail

theorem integral_one_sub_pow (k : ℕ) :
    (∫ t in Icc (0 : ℝ) 1, (1 - t) ^ k) = 1 / (k + 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ k) 1,
    sub_self, sub_zero, integral_pow]
  simp

theorem integral_mul_one_sub_pow (k : ℕ) :
    (∫ t in Icc (0 : ℝ) 1, t * (1 - t) ^ k) = 1 / ((k + 1) * (k + 2)) := by
  have hfun : (fun t : ℝ => t * (1 - t) ^ k) =
      fun t => (1 - t) ^ k - (1 - t) ^ (k + 1) := by
    ext t
    rw [pow_succ]
    ring
  rw [hfun, integral_sub]
  · rw [integral_one_sub_pow k, integral_one_sub_pow (k + 1)]
    push_cast
    field_simp
    ring
  · exact (Continuous.integrableOn_Icc (by fun_prop))
  · exact (Continuous.integrableOn_Icc (by fun_prop))

section TailMoments
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}

theorem moments_from_tail (m : ℕ) (hX : Measurable X)
    (hXb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1)
    (ht : ∀ t ∈ Icc (0 : ℝ) 1, μ {ω | t ≤ X ω} = ENNReal.ofReal (1 - t) ^ m) :
    (∫ ω, X ω ∂μ) = 1 / (m + 1) ∧
      (∫ ω, X ω ^ 2 ∂μ) = 2 / ((m + 1) * (m + 2)) := by
  have heq (k : ℕ) : (∫ t in Icc (0 : ℝ) 1, t ^ k * μ.real {ω | t ≤ X ω}) =
      ∫ t in Icc (0 : ℝ) 1, t ^ k * (1 - t) ^ m := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht0
    change t ^ k * μ.real {ω | t ≤ X ω} = t ^ k * (1 - t) ^ m
    rw [measureReal_def, ht t ht0, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (sub_nonneg.mpr ht0.2)]
  constructor
  · have h := moment_tail hX hXb 0
    rw [heq 0] at h
    simpa only [zero_add, pow_one, pow_zero, one_mul, Nat.cast_zero, Nat.cast_one, div_one,
      integral_one_sub_pow] using h
  · have h := moment_tail hX hXb 1
    rw [heq 1] at h
    norm_num only [one_add_one_eq_two, pow_one, Nat.cast_ofNat] at h
    rw [integral_mul_one_sub_pow] at h
    have h' := (div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)).mp h
    rw [h']
    ring

end TailMoments

theorem lower_moments (n : ℕ) :
    (∫ ω, lower n ω ∂sampleMeasure n) = 1 / ((n : ℝ) + 3) ∧
      (∫ ω, lower n ω ^ 2 ∂sampleMeasure n) = 2 / (((n : ℝ) + 3) * (n + 4)) := by
  obtain ⟨h₁, h₂⟩ := moments_from_tail (n + 2) (lower_continuous n).measurable
    ((endpoint_bounds n).mono (fun _ h => h.1)) (fun _ h => lower_tail n h)
  constructor
  · convert h₁ using 1; push_cast; ring
  · convert h₂ using 1; push_cast; ring

theorem right_moments (n : ℕ) :
    (∫ ω, right n ω ∂sampleMeasure n) = 1 / ((n : ℝ) + 3) ∧
      (∫ ω, right n ω ^ 2 ∂sampleMeasure n) = 2 / (((n : ℝ) + 3) * (n + 4)) := by
  obtain ⟨h₁, h₂⟩ := moments_from_tail (n + 2) (right_continuous n).measurable
    ((endpoint_bounds n).mono (fun _ h => h.2)) (fun _ h => right_tail n h)
  constructor
  · convert h₁ using 1; push_cast; ring
  · convert h₂ using 1; push_cast; ring

theorem integral_truncated_power (m : ℕ) (hm : 0 < m) {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ v in Icc (0 : ℝ) 1, (ENNReal.ofReal (b - v) ^ m).toReal) =
      b ^ (m + 1) / (m + 1) := by
  have hfun : (fun v : ℝ => (ENNReal.ofReal (b - v) ^ m).toReal) =
      (Iic b).indicator (fun v => (b - v) ^ m) := by
    ext v
    by_cases hv : v ≤ b
    · simp [hv, ENNReal.toReal_pow, ENNReal.toReal_ofReal (sub_nonneg.mpr hv)]
    · rw [ENNReal.ofReal_of_nonpos (by linarith : b - v ≤ 0), zero_pow hm.ne',
        ENNReal.toReal_zero, Set.indicator_of_notMem (show v ∉ Iic b from hv)]
  rw [hfun, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have h : Iic b ∩ Icc (0 : ℝ) 1 = Icc 0 b := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hvb, hv0, _⟩; exact ⟨hv0, hvb⟩
    · rintro ⟨hv0, hvb⟩; exact ⟨hvb, hv0, hvb.trans hb.2⟩
  rw [h, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb.1,
    intervalIntegral.integral_comp_sub_left (fun v : ℝ => v ^ m) b,
    sub_self, sub_zero, integral_pow]
  simp

theorem endpoint_cross_moment (n : ℕ) :
    (∫ ω, lower n ω * right n ω ∂sampleMeasure n) =
      1 / (((n : ℝ) + 3) * (n + 4)) := by
  have hlb := (endpoint_bounds n).mono (fun _ h => h.1)
  have hrb := (endpoint_bounds n).mono (fun _ h => h.2)
  have hrnorm : ∀ᵐ ω ∂sampleMeasure n, ‖right n ω‖ ≤ 1 := by
    filter_upwards [hrb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
    exact hω.2
  have h := weighted_tail (lower_continuous n).measurable (right_continuous n).measurable
    hlb hrnorm 0
  simp only [zero_add, pow_one, Nat.cast_zero, zero_add, div_one, pow_zero, one_mul] at h
  simp_rw [mul_comm] at h
  rw [h]
  have hi (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      (∫ ω in {ω | u ≤ lower n ω}, right n ω ∂sampleMeasure n) =
        (1 - u) ^ (n + 3) / ((n : ℝ) + 3) := by
    have ht := moment_tail (μ := (sampleMeasure n).restrict {ω | u ≤ lower n ω})
      (right_continuous n).measurable (ae_restrict_of_ae hrb) 0
    simp only [zero_add, pow_one, Nat.cast_zero, zero_add, div_one, pow_zero, one_mul] at ht
    rw [ht]
    calc
      (∫ v in Icc (0 : ℝ) 1,
        ((sampleMeasure n).restrict {ω | u ≤ lower n ω}).real {ω | v ≤ right n ω}) =
          ∫ v in Icc (0 : ℝ) 1, (ENNReal.ofReal (1 - u - v) ^ (n + 2)).toReal := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro v hv
        change ((sampleMeasure n).restrict {ω | u ≤ lower n ω}).real
          {ω | v ≤ right n ω} = _
        rw [measureReal_def, Measure.restrict_apply
          (measurableSet_le measurable_const (right_continuous n).measurable)]
        have he : {ω : Sample n | v ≤ right n ω} ∩ {ω | u ≤ lower n ω} =
            {ω | u ≤ lower n ω ∧ v ≤ right n ω} := by ext ω; simp [and_comm]
        rw [he, joint_tail n hu hv]
      _ = (1 - u) ^ (n + 3) / ((n : ℝ) + 3) := by
        rw [integral_truncated_power (n + 2) (by omega)
          (show 1 - u ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hu.2], by linarith [hu.1]⟩)]
        push_cast
        ring
  calc
    (∫ u in Icc (0 : ℝ) 1, ∫ ω in {ω | u ≤ lower n ω}, right n ω ∂sampleMeasure n) =
        ∫ u in Icc (0 : ℝ) 1, (1 - u) ^ (n + 3) / ((n : ℝ) + 3) :=
      setIntegral_congr_fun measurableSet_Icc hi
    _ = 1 / (((n : ℝ) + 3) * (n + 4)) := by
      rw [integral_div, integral_one_sub_pow]
      push_cast
      field_simp
      ring

theorem endpoint_memLp (n : ℕ) (p : ℝ≥0∞) :
    MemLp (lower n) p (sampleMeasure n) ∧ MemLp (right n) p (sampleMeasure n) := by
  exact ⟨memLp_of_bounded ((endpoint_bounds n).mono (fun _ h => h.1))
      (lower_continuous n).aestronglyMeasurable p,
    memLp_of_bounded ((endpoint_bounds n).mono (fun _ h => h.2))
      (right_continuous n).aestronglyMeasurable p⟩

theorem deficit_bounds (n : ℕ) :
    ∀ᵐ ω ∂sampleMeasure n, deficit n ω ∈ Icc (0 : ℝ) 2 := by
  filter_upwards [endpoint_bounds n] with ω hω
  rw [deficit_eq]
  exact ⟨add_nonneg hω.1.1 hω.2.1, by linarith [hω.1.2, hω.2.2]⟩

theorem deficit_memLp (n : ℕ) (p : ℝ≥0∞) : MemLp (deficit n) p (sampleMeasure n) :=
  memLp_of_bounded (deficit_bounds n) (deficit_continuous n).aestronglyMeasurable p

theorem deficit_expectation (n : ℕ) :
    (∫ ω, deficit n ω ∂sampleMeasure n) = 2 / ((n : ℝ) + 3) := by
  have h : deficit n = fun ω => lower n ω + right n ω := funext (deficit_eq n)
  rw [h, integral_add ((endpoint_memLp n 1).1.integrable le_rfl)
    ((endpoint_memLp n 1).2.integrable le_rfl), (lower_moments n).1, (right_moments n).1]
  ring

theorem deficit_second_moment (n : ℕ) :
    (∫ ω, deficit n ω ^ 2 ∂sampleMeasure n) = 6 / (((n : ℝ) + 3) * (n + 4)) := by
  have hli : Integrable (fun ω => lower n ω ^ 2) (sampleMeasure n) := by
    convert! (endpoint_memLp n 2).1.integrable_mul (endpoint_memLp n 2).1 using 1
    ext ω
    simp [pow_two]
  have hri : Integrable (fun ω => right n ω ^ 2) (sampleMeasure n) := by
    convert! (endpoint_memLp n 2).2.integrable_mul (endpoint_memLp n 2).2 using 1
    ext ω
    simp [pow_two]
  have hci : Integrable (fun ω => lower n ω * right n ω) (sampleMeasure n) := by
    convert! (endpoint_memLp n 2).1.integrable_mul (endpoint_memLp n 2).2 using 1
  have hfun : (fun ω => deficit n ω ^ 2) =
      fun ω => lower n ω ^ 2 + right n ω ^ 2 + 2 * (lower n ω * right n ω) := by
    ext ω
    rw [deficit_eq]
    ring
  have hsum : Integrable (fun ω => lower n ω ^ 2 + right n ω ^ 2) (sampleMeasure n) := by
    convert! hli.add hri using 1
  rw [hfun, integral_add hsum (hci.const_mul 2), integral_add hli hri,
    integral_const_mul, (lower_moments n).2, (right_moments n).2, endpoint_cross_moment]
  ring

theorem deficit_variance (n : ℕ) :
    variance (deficit n) (sampleMeasure n) =
      2 * ((n : ℝ) + 1) / (((n : ℝ) + 3) ^ 2 * (n + 4)) := by
  rw [variance_eq_sub (deficit_memLp n 2)]
  change (∫ ω, deficit n ω ^ 2 ∂sampleMeasure n) -
    (∫ ω, deficit n ω ∂sampleMeasure n) ^ 2 = _
  rw [deficit_second_moment, deficit_expectation]
  have h₃ : (n : ℝ) + 3 ≠ 0 := ne_of_gt (by positivity)
  have h₄ : (n : ℝ) + 4 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem deficit_variance_positive (n : ℕ) : 0 < variance (deficit n) (sampleMeasure n) := by
  rw [deficit_variance]
  positivity

def standardized (n : ℕ) (ω : Sample n) : ℝ :=
  (deficit n ω - ∫ v, deficit n v ∂sampleMeasure n) /
    Real.sqrt (variance (deficit n) (sampleMeasure n))

theorem standardized_measurable (n : ℕ) : Measurable (standardized n) :=
  ((deficit_continuous n).measurable.sub_const _).div_const _

theorem mean_square_bound (n : ℕ) :
    (∫ ω, deficit n ω ∂sampleMeasure n) ^ 2 ≤
      9 * variance (deficit n) (sampleMeasure n) := by
  rw [deficit_expectation, deficit_variance]
  have h₃ : 0 < (n : ℝ) + 3 := by positivity
  have h₄ : 0 < (n : ℝ) + 4 := by positivity
  apply (mul_le_mul_iff_left₀ (mul_pos (sq_pos_of_pos h₃) h₄)).mp
  field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem standardized_lower_bound (n : ℕ) :
    ∀ᵐ ω ∂sampleMeasure n, -3 ≤ standardized n ω := by
  have hv := deficit_variance_positive n
  have hs := Real.sqrt_pos.mpr hv
  have hsq := Real.sq_sqrt hv.le
  have hm : 0 ≤ ∫ ω, deficit n ω ∂sampleMeasure n := by rw [deficit_expectation]; positivity
  have hms : (∫ ω, deficit n ω ∂sampleMeasure n) ≤
      3 * Real.sqrt (variance (deficit n) (sampleMeasure n)) := by
    nlinarith [mean_square_bound n]
  filter_upwards [deficit_bounds n] with ω hω
  dsimp [standardized]
  apply (le_div_iff₀ hs).mpr
  linarith [hω.1]

def standardizedLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (⟨sampleMeasure n, inferInstance⟩ : ProbabilityMeasure (Sample n))
    (standardized_measurable n).aemeasurable

def standardGaussian : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩

theorem standardizedLaw_is_native_map (n : ℕ) :
    (standardizedLaw n : Measure ℝ) = (sampleMeasure n).map (standardized n) := rfl

theorem standardizedLaw_left_tail (n : ℕ) :
    (standardizedLaw n : Measure ℝ) (Iic (-4)) = 0 := by
  rw [standardizedLaw_is_native_map, Measure.map_apply (standardized_measurable n) measurableSet_Iic]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [standardized_lower_bound n] with ω hω
  change ¬standardized n ω ≤ -4
  linarith

theorem standardGaussian_left_tail_positive :
    0 < (standardGaussian : Measure ℝ) (Iic (-4)) := by
  apply pos_iff_ne_zero.mpr
  intro h
  have hv : volume (Iic (-4 : ℝ)) = 0 :=
    gaussianReal_absolutelyContinuous' 0 (v := 1) (by norm_num) h
  have hi : volume (Icc (-5 : ℝ) (-4)) = 0 :=
    measure_mono_null (fun _ hx => hx.2) hv
  norm_num at hi

theorem standardGaussian_null_frontier :
    (standardGaussian : Measure ℝ) (frontier (Iic (-4))) = 0 := by
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  change gaussianReal 0 1 (frontier (Iic (-4 : ℝ))) = 0
  simp

theorem not_weak_standardGaussian :
    ¬Tendsto standardizedLaw atTop (𝓝 standardGaussian) := by
  intro h
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    h standardGaussian_null_frontier
  have hz : (fun n => (standardizedLaw n : Measure ℝ) (Iic (-4))) = fun _ => 0 :=
    funext standardizedLaw_left_tail
  rw [hz] at hlim
  have he := tendsto_nhds_unique tendsto_const_nhds hlim
  exact (ne_of_gt standardGaussian_left_tail_positive) he.symm

theorem not_gaussian_cdf_convergence :
    ¬∀ x : ℝ, Tendsto (fun n => (standardizedLaw n : Measure ℝ).real (Iic x))
      atTop (𝓝 ((standardGaussian : Measure ℝ).real (Iic x))) := by
  intro h
  have ht := h (-4)
  have hz : (fun n => (standardizedLaw n : Measure ℝ).real (Iic (-4))) = fun _ => 0 := by
    ext n
    simp [measureReal_def, standardizedLaw_left_tail]
  rw [hz] at ht
  have he := tendsto_nhds_unique tendsto_const_nhds ht
  have hp : 0 < (standardGaussian : Measure ℝ).real (Iic (-4)) :=
    ENNReal.toReal_pos (ne_of_gt standardGaussian_left_tail_positive) (measure_ne_top _ _)
  exact (ne_of_gt hp) he.symm

theorem complete_counterexample :
    IsCompact body ∧ Convex ℝ body ∧ (interior body).Nonempty ∧ volume body = 1 ∧
      Module.finrank ℝ ℝ = 1 ∧
      (∀ n, iIndepFun (fun i (ω : Sample n) => ω i) (sampleMeasure n)) ∧
      (∀ n i, pdf.IsUniform (fun ω : Sample n => ω i) body (sampleMeasure n) volume) ∧
      (∀ n ω, polytope n ω = Icc (lower n ω) (upper n ω)) ∧
      (∀ n, (∫ ω, deficit n ω ∂sampleMeasure n) = 2 / ((n : ℝ) + 3)) ∧
      (∀ n, (∫ ω, deficit n ω ^ 2 ∂sampleMeasure n) =
        6 / (((n : ℝ) + 3) * (n + 4))) ∧
      (∀ n, variance (deficit n) (sampleMeasure n) =
        2 * ((n : ℝ) + 1) / (((n : ℝ) + 3) ^ 2 * (n + 4))) ∧
      (∀ n, 0 < variance (deficit n) (sampleMeasure n)) ∧
      ¬Tendsto standardizedLaw atTop (𝓝 standardGaussian) :=
  ⟨body_compact, body_convex, body_interior_nonempty, body_volume, ambient_dimension,
    samples_independent, sample_uniform, polytope_interval, deficit_expectation,
    deficit_second_moment, deficit_variance, deficit_variance_positive, not_weak_standardGaussian⟩

end TLMC1453
