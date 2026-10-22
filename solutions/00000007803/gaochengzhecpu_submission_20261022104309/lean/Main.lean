import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.CDF
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal BigOperators Classical
set_option maxHeartbeats 1500000
set_option maxRecDepth 2000

namespace Conjecture7803

def r : ℝ := Real.sqrt 3
lemma r_pos : 0<r := Real.sqrt_pos.mpr (by norm_num)
lemma r_sq : r^2=3 := Real.sq_sqrt (by norm_num)
def support : Set ℝ := Icc (-r) r
def μ : Measure ℝ := cond volume support

lemma support_volume : volume support=ENNReal.ofReal (2*r) := by
  simp [support, Real.volume_Icc]
  congr 1
  ring

lemma volume_ne_zero : volume support≠0 := by
  rw [support_volume]
  exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith [r_pos])

lemma volume_ne_top : volume support≠∞ := by rw [support_volume]; exact ENNReal.ofReal_ne_top

instance : IsProbabilityMeasure μ :=
  cond_isProbabilityMeasure_of_finite volume_ne_zero volume_ne_top

def density (x : ℝ) : ℝ := if x∈support then (2*r)⁻¹ else 0

lemma density_nonneg (x : ℝ) : 0≤density x := by
  have hr := r_pos
  unfold density
  split_ifs <;> positivity

theorem density_representation : μ=volume.withDensity (fun x => ENNReal.ofReal (density x)) := by
  have hf : (fun x => ENNReal.ofReal (density x)) =
      support.indicator (fun _ => ENNReal.ofReal ((2*r)⁻¹)) := by
    ext x
    simp [density, Set.indicator]
    split_ifs <;> simp
  rw [hf, withDensity_indicator (show MeasurableSet support from measurableSet_Icc),
    withDensity_const]
  unfold μ ProbabilityTheory.cond
  rw [support_volume, ENNReal.ofReal_inv_of_pos (by linarith [r_pos])]

/-- The standard multiplicative definition of a log-concave density. -/
theorem density_logConcave (x y t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    density x ^ t * density y ^ (1-t) ≤ density (t*x+(1-t)*y) := by
  by_cases h0 : t=0
  · subst t; simp
  by_cases h1 : t=1
  · subst t; simp
  have ht' : 0<t := lt_of_le_of_ne ht (Ne.symm h0)
  have htlt : t<1 := lt_of_le_of_ne ht1 h1
  have hu' : 0<1-t := by linarith
  by_cases hx : x∈support
  · by_cases hy : y∈support
    · have hm : t*x+(1-t)*y∈support :=
        (convex_Icc (-r) r) hx hy ht (by linarith) (by ring)
      simp only [density, if_pos hx, if_pos hy, if_pos hm]
      rw [← Real.rpow_add (inv_pos.mpr (mul_pos (by norm_num) r_pos))]
      simp
    · have hy0 : density y=0 := by simp [density, hy]
      rw [hy0, Real.zero_rpow (ne_of_gt hu'), mul_zero]
      exact density_nonneg _
  · have hx0 : density x=0 := by simp [density, hx]
    rw [hx0, Real.zero_rpow h0, zero_mul]
    exact density_nonneg _

lemma integral_uniform (f : ℝ→ℝ) :
    ∫ x, f x ∂μ = (2*r)⁻¹ * ∫ x in (-r)..r, f x := by
  rw [μ, ProbabilityTheory.cond, integral_smul_measure, support_volume,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith [r_pos])]
  rw [support, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [r_pos])]
  rfl

theorem centered : ∫ x : ℝ, x ∂μ=0 := by
  rw [integral_uniform, integral_id]
  ring

theorem unit_second_moment : ∫ x : ℝ, x^2 ∂μ=1 := by
  rw [integral_uniform, integral_pow]
  have hr : r≠0 := ne_of_gt r_pos
  have hcube : r^3=3*r := by calc
    _ = r^2*r := by ring
    _ = 3*r := by rw [r_sq]
  field_simp [hr]
  norm_num
  nlinarith [hcube]

theorem integrable_id : Integrable (fun x : ℝ => x) μ := by
  have hi : IntegrableOn (fun x : ℝ => x) support volume :=
    continuous_id.continuousOn.integrableOn_compact isCompact_Icc
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr volume_ne_zero)

theorem integrable_square : Integrable (fun x : ℝ => x^2) μ := by
  have hi : IntegrableOn (fun x : ℝ => x^2) support volume :=
    (continuous_id.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr volume_ne_zero)

lemma support_ae : ∀ᵐ x ∂μ, x∈support := by
  change ∀ᵐ x ∂((volume support)⁻¹ • volume.restrict support), x∈support
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

abbrev Ω := ℕ→ℝ
def law : Measure Ω := Measure.infinitePi (fun _ : ℕ => μ)
instance : IsProbabilityMeasure law := inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))
def X (i : ℕ) (ω : Ω) : ℝ := ω i

theorem cylinder (S : Finset ℕ) (s : ℕ→Set ℝ) (hs : ∀ i∈S, MeasurableSet (s i)) :
    law (Set.pi S s)=∏ i∈S, μ (s i) := Measure.infinitePi_pi _ hs

lemma marginal (i : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    law (X i ⁻¹' s)=μ s := by
  have he : X i ⁻¹' s=Set.pi ({i}:Finset ℕ) (fun _ => s) := by
    ext ω
    simp [X, Set.mem_pi]
  rw [he, cylinder _ _ (by simpa using hs)]
  simp

theorem marginal_map (i : ℕ) : law.map (X i)=μ := by
  ext s hs
  rw [Measure.map_apply (show Measurable (X i) from measurable_pi_apply i) hs, marginal i s hs]

theorem independent : iIndepFun X law := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  have he : (⋂ i∈S, X i ⁻¹' sets i)=Set.pi S sets := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [he, cylinder S sets hs]
  exact Finset.prod_congr rfl (fun i hi => (marginal i (sets i) (hs i hi)).symm)

theorem coordinates_centered (i : ℕ) : ∫ ω, X i ω ∂law=0 := by
  calc
    _ = ∫ x : ℝ, x ∂law.map (X i) :=
      (integral_map (show AEMeasurable (X i) law from (measurable_pi_apply i).aemeasurable)
        aestronglyMeasurable_id).symm
    _ = 0 := by rw [marginal_map, centered]

theorem coordinates_unit_second_moment (i : ℕ) : ∫ ω, (X i ω)^2 ∂law=1 := by
  calc
    _ = ∫ x : ℝ, x^2 ∂law.map (X i) :=
      (integral_map (show AEMeasurable (X i) law from (measurable_pi_apply i).aemeasurable)
        (continuous_id.pow 2).aestronglyMeasurable).symm
    _ = 1 := by rw [marginal_map, unit_second_moment]

lemma all_bounded : ∀ᵐ ω ∂law, ∀ i, |X i ω|≤r := by
  rw [ae_all_iff]
  intro i
  have hi : ∀ᵐ x ∂law.map (X i), x∈support := by rw [marginal_map]; exact support_ae
  have hb := ae_of_ae_map
    (show AEMeasurable (X i) law from (measurable_pi_apply i).aemeasurable) hi
  filter_upwards [hb] with ω hω
  exact abs_le.mpr hω

/-- The genuine maximum of the first n+1 coordinate samples. -/
def maximum : ℕ→Ω→ℝ
  | 0, ω => |X 0 ω|
  | n+1, ω => max (maximum n ω) |X (n+1) ω|

theorem maximum_le_iff (n : ℕ) (ω : Ω) (b : ℝ) :
    maximum n ω≤b ↔ ∀ i≤n, |X i ω|≤b := by
  induction n with
  | zero => simp [maximum]
  | succ n ih =>
    rw [maximum, max_le_iff, ih]
    constructor
    · rintro ⟨h, h'⟩ i hi
      obtain hi'|rfl := Nat.le_add_one_iff.mp hi
      · exact h i hi'
      · exact h'
    · intro h
      exact ⟨fun i hi => h i (by omega), h (n+1) le_rfl⟩

lemma maximum_nonneg (n : ℕ) (ω : Ω) : 0≤maximum n ω := by
  induction n with
  | zero => exact abs_nonneg _
  | succ n ih => exact ih.trans (le_max_left _ _)

lemma maximum_measurable (n : ℕ) : Measurable (maximum n) := by
  induction n with
  | zero => exact continuous_abs.measurable.comp (measurable_pi_apply 0)
  | succ n ih => exact ih.max (continuous_abs.measurable.comp (measurable_pi_apply (n+1)))

lemma maximum_bound : ∀ᵐ ω ∂law, ∀ n, 0≤maximum n ω ∧ maximum n ω≤r := by
  filter_upwards [all_bounded] with ω hω n
  exact ⟨maximum_nonneg n ω, (maximum_le_iff n ω r).mpr (fun i _ => hω i)⟩

def size (n : ℕ) : ℝ := n+1
def center (n : ℕ) : ℝ := Real.sqrt (2*Real.log (size n))/Real.sqrt (size n)
def correction (n : ℕ) : ℝ :=
  (Real.log (Real.log (size n))/Real.sqrt (2*Real.log (size n)))/Real.sqrt (size n)

lemma size_pos (n : ℕ) : 0<size n := by unfold size; positivity
lemma size_ge_one (n : ℕ) : 1≤size n := by
  unfold size
  linarith [show (0:ℝ)≤n from Nat.cast_nonneg n]

lemma size_tendsto : Tendsto size atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hc : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hc.eventually (eventually_ge_atTop b)] with n hn
  unfold size
  linarith

lemma sqrt_size_tendsto : Tendsto (fun n => Real.sqrt (size n)) atTop atTop := by
  simpa only [Real.sqrt_eq_rpow] using
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp size_tendsto

lemma inv_sqrt_size_tendsto :
    Tendsto (fun n => (Real.sqrt (size n))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp sqrt_size_tendsto

theorem center_tendsto : Tendsto center atTop (𝓝 0) := by
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp size_tendsto
  have htwice := hratio.const_mul 2
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp htwice
  have he : (fun k => Real.sqrt (2* (Real.log (size k)/size k)))=center := by
    ext n
    unfold center
    rw [← mul_div_assoc, Real.sqrt_div' _ (size_pos n).le]
  simpa only [Function.comp_def, id_eq, mul_zero, Real.sqrt_zero, he] using hs

theorem correction_tendsto : Tendsto correction atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Real.log (size n)) atTop atTop :=
    Real.tendsto_log_atTop.comp size_tendsto
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp hlog
  have h' : Tendsto (fun n => Real.log (Real.log (size n))/Real.sqrt (Real.log (size n)))
      atTop (𝓝 0) := by simpa only [← Real.sqrt_eq_rpow] using h
  have h'' := (h'.div_const (Real.sqrt 2)).mul inv_sqrt_size_tendsto
  convert h'' using 1
  · ext n
    unfold correction
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    ring
  · simp

def Z (b : ℕ→ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  maximum n ω/Real.sqrt (size n)-b n

lemma Z_measurable (b : ℕ→ℝ) (n : ℕ) : Measurable (Z b n) :=
  ((maximum_measurable n).div_const _).sub_const _

def actualCDF (b : ℕ→ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (law {ω | Z b n ω≤x}).toReal

theorem actualCDF_eq_cdf (b : ℕ→ℝ) (n : ℕ) (x : ℝ) :
    actualCDF b n x=cdf (law.map (Z b n)) x := by
  letI : IsProbabilityMeasure (law.map (Z b n)) :=
    isProbabilityMeasure_map (Z_measurable b n).aemeasurable
  rw [cdf_eq_real, Measure.real, Measure.map_apply (Z_measurable b n) measurableSet_Iic]
  rfl

/-- Any bounded nonnegative sequence has zero limit on the proposed scale;
in particular no coupling assumptions are needed for this analytic step. -/
theorem bounded_sequence_sqrt_zero (m : ℕ→ℝ) (B : ℝ)
    (hm : ∀ n, 0≤m n ∧ m n≤B) :
    Tendsto (fun n => m n/Real.sqrt (size n)) atTop (𝓝 0) := by
  have hu : Tendsto (fun n => B/Real.sqrt (size n)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using inv_sqrt_size_tendsto.const_mul B
  exact squeeze_zero (fun n => div_nonneg (hm n).1 (Real.sqrt_nonneg _))
    (fun n => div_le_div_of_nonneg_right (hm n).2 (Real.sqrt_nonneg _)) hu

theorem almostSure_zero_limit {b : ℕ→ℝ} (hb : Tendsto b atTop (𝓝 0)) :
    ∀ᵐ ω ∂law, Tendsto (fun n => Z b n ω) atTop (𝓝 0) := by
  filter_upwards [maximum_bound] with ω hω
  have hm : Tendsto (fun n => maximum n ω/Real.sqrt (size n)) atTop (𝓝 0) :=
    bounded_sequence_sqrt_zero _ r hω
  simpa only [sub_zero] using hm.sub hb

theorem cdf_eventually_one {b : ℕ→ℝ} (hb : Tendsto b atTop (𝓝 0)) :
    ∀ᶠ n in atTop, actualCDF b n 1=1 := by
  have hu : Tendsto (fun n => r/Real.sqrt (size n)-b n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using
      (inv_sqrt_size_tendsto.const_mul r).sub hb
  filter_upwards [hu.eventually (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))] with n hn
  have hs : {ω | Z b n ω≤1}=ᵐ[law] Set.univ := by
    filter_upwards [maximum_bound] with ω hω
    have hle := div_le_div_of_nonneg_right (hω n).2 (Real.sqrt_nonneg (size n))
    apply propext
    change (Z b n ω≤1) ↔ True
    exact iff_true_intro (by unfold Z; linarith)
  unfold actualCDF
  rw [measure_congr hs, measure_univ, ENNReal.toReal_one]

def gumbelCDF (location scale x : ℝ) : ℝ :=
  Real.exp (-Real.exp (-(x-location)/scale))

lemma gumbelCDF_continuous (location scale : ℝ) : Continuous (gumbelCDF location scale) := by
  unfold gumbelCDF
  fun_prop

lemma gumbelCDF_lt_one (location scale x : ℝ) : gumbelCDF location scale x<1 := by
  unfold gumbelCDF
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos _))

/-- The standard characterization of convergence in law by CDFs at all
continuity points, using the actual pushforward law above. -/
def ConvergesToCDF (b : ℕ→ℝ) (G : ℝ→ℝ) : Prop :=
  ∀ x, ContinuousAt G x → Tendsto (fun n => actualCDF b n x) atTop (𝓝 (G x))

theorem no_gumbel_limit {b : ℕ→ℝ} (hb : Tendsto b atTop (𝓝 0))
    (location scale : ℝ) : ¬ConvergesToCDF b (gumbelCDF location scale) := by
  intro h
  have h1 : Tendsto (fun n => actualCDF b n 1) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' ((cdf_eventually_one hb).mono (fun _ h => h.symm))
  have hg := h 1 (gumbelCDF_continuous location scale).continuousAt
  have he : (1:ℝ)=gumbelCDF location scale 1 := tendsto_nhds_unique h1 hg
  linarith [gumbelCDF_lt_one location scale 1]

theorem original_center_no_gumbel (location scale : ℝ) :
    ¬ConvergesToCDF center (gumbelCDF location scale) :=
  no_gumbel_limit center_tendsto location scale

theorem corrected_center_no_gumbel (a location scale : ℝ) :
    ¬ConvergesToCDF (fun n => center n+a*correction n) (gumbelCDF location scale) := by
  apply no_gumbel_limit _ location scale
  simpa using center_tendsto.add (correction_tendsto.const_mul a)

theorem original_almostSure_zero :
    ∀ᵐ ω ∂law, Tendsto (fun n => Z center n ω) atTop (𝓝 0) :=
  almostSure_zero_limit center_tendsto

theorem corrected_almostSure_zero (a : ℝ) :
    ∀ᵐ ω ∂law, Tendsto (fun n => Z (fun k => center k+a*correction k) n ω) atTop (𝓝 0) := by
  apply almostSure_zero_limit
  simpa using center_tendsto.add (correction_tendsto.const_mul a)

#print axioms density_representation
#print axioms density_logConcave
#print axioms integrable_id
#print axioms integrable_square
#print axioms centered
#print axioms unit_second_moment
#print axioms cylinder
#print axioms marginal_map
#print axioms independent
#print axioms coordinates_centered
#print axioms coordinates_unit_second_moment
#print axioms maximum_le_iff
#print axioms center_tendsto
#print axioms correction_tendsto
#print axioms actualCDF_eq_cdf
#print axioms original_almostSure_zero
#print axioms corrected_almostSure_zero
#print axioms original_center_no_gumbel
#print axioms corrected_center_no_gumbel

end Conjecture7803

