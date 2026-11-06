import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal SchwartzMap

namespace TLMC1911

/-- Complex carries its genuine Euclidean, rather than product-sup, norm. -/
theorem euclidean_norm (z : ℂ) : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) :=
  Complex.norm_eq_sqrt_sq_add_sq z

theorem euclidean_volume :
    MeasurePreserving Complex.measurableEquivRealProd :=
  Complex.volume_preserving_equiv_real_prod

def clipped (z : ℂ) : ℂ := ⟨max 1 z.re, z.im⟩

theorem clipped_norm (z : ℂ) : 1 ≤ ‖clipped z‖ := by
  have h := Complex.abs_re_le_norm (clipped z)
  have hc : 1 ≤ max 1 z.re := le_max_left _ _
  apply hc.trans
  simpa only [clipped, abs_of_nonneg (by linarith : 0 ≤ max 1 z.re)] using h

theorem clipped_lipschitz : LipschitzWith 1 clipped := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hc : |max 1 z.re - max 1 w.re| ≤ |z.re - w.re| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq] using
      ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max 1).dist_le_mul z.re w.re
  have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 hc
  simp only [sq_abs] at hs
  have hn : ‖clipped z - clipped w‖ ^ 2 ≤ ‖z - w‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      clipped]
    nlinarith
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hn

def field (z : ℂ) : ℂ := ‖clipped z‖⁻¹ • clipped z

theorem field_unit (z : ℂ) : ‖field z‖ = 1 := by
  have hn : 0 < ‖clipped z‖ := lt_of_lt_of_le zero_lt_one (clipped_norm z)
  simp [field, hn.ne']

theorem field_ne_zero (z : ℂ) : field z ≠ 0 := by
  intro h
  have := field_unit z
  simp [h] at this

theorem normalization_bound {u v : ℂ} (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖ ≤ 2 * ‖u - v‖ := by
  have hu0 : 0 < ‖u‖ := lt_of_lt_of_le zero_lt_one hu
  have hv0 : 0 < ‖v‖ := lt_of_lt_of_le zero_lt_one hv
  have hi : |‖u‖⁻¹ - ‖v‖⁻¹| * ‖v‖ = |‖v‖ - ‖u‖| / ‖u‖ := by
    rw [inv_sub_inv hu0.ne' hv0.ne', abs_div, abs_mul, abs_of_pos hu0,
      abs_of_pos hv0]
    field_simp
  calc
    ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖ =
        ‖‖u‖⁻¹ • (u - v) + (‖u‖⁻¹ - ‖v‖⁻¹) • v‖ := by
      congr 1
      rw [smul_sub, sub_smul]
      abel
    _ ≤ ‖‖u‖⁻¹ • (u - v)‖ + ‖(‖u‖⁻¹ - ‖v‖⁻¹) • v‖ := norm_add_le _ _
    _ = ‖u - v‖ / ‖u‖ + |‖v‖ - ‖u‖| / ‖u‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hu0, hi]
      ring
    _ ≤ ‖u - v‖ / ‖u‖ + ‖u - v‖ / ‖u‖ := by
      gcongr
      simpa only [abs_sub_comm] using abs_norm_sub_norm_le u v
    _ ≤ 2 * ‖u - v‖ := by
      have hd : ‖u - v‖ / ‖u‖ ≤ ‖u - v‖ :=
        div_le_self (norm_nonneg _) hu
      linarith

theorem field_lipschitz : LipschitzWith 2 field := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hc : ‖clipped z - clipped w‖ ≤ ‖z - w‖ := by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using clipped_lipschitz.dist_le_mul z w
  simpa only [dist_eq_norm, field, NNReal.coe_ofNat] using
    (normalization_bound (clipped_norm z) (clipped_norm w)).trans
      (mul_le_mul_of_nonneg_left hc (by norm_num))

theorem field_radial {z : ℂ} (hz : 1 ≤ z.re) : field z = ‖z‖⁻¹ • z := by
  have hc : clipped z = z := by apply Complex.ext <;> simp [clipped, max_eq_right hz]
  simp [field, hc]

def bump : ContDiffBump (0 : ℂ) := ⟨1, 2, by norm_num, by norm_num⟩

def test : 𝓢(ℂ, ℝ) := bump.hasCompactSupport.toSchwartzMap bump.contDiff

theorem test_nonneg (z : ℂ) : 0 ≤ test z := bump.nonneg

theorem test_le_one (z : ℂ) : test z ≤ 1 := bump.le_one

theorem test_one {z : ℂ} (hz : ‖z‖ ≤ 1) : test z = 1 := by
  exact bump.one_of_mem_closedBall (by simpa [bump, Metric.mem_closedBall, dist_eq_norm] using hz)

theorem test_zero {z : ℂ} (hz : 2 ≤ ‖z‖) : test z = 0 := by
  exact bump.zero_of_le_dist (by simpa [bump, dist_eq_norm] using hz)

theorem test_memLp : MemLp test 2 := test.memLp 2

def cone : Set ℂ := {z | 4 ≤ z.re ∧ 0 ≤ z.im ∧ z.im ≤ z.re}

theorem cone_norm {z : ℂ} (hz : z ∈ cone) : 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * z.re := by
  have hx : 0 ≤ z.re := by linarith [hz.1]
  have h := Complex.re_le_norm z
  have hu := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg hx, abs_of_nonneg hz.2.1] at hu
  constructor <;> linarith [hz.1, hz.2.2]

theorem radial_line {z : ℂ} (hz : z ∈ cone) (t : ℝ) :
    ‖z - t • field z‖ = |‖z‖ - t| := by
  have hn : 0 < ‖z‖ := by linarith [(cone_norm hz).1]
  rw [field_radial (by linarith [hz.1]), smul_smul]
  calc
    ‖z - (t * ‖z‖⁻¹) • z‖ = ‖(1 - t * ‖z‖⁻¹) • z‖ := by
      rw [sub_smul, one_smul]
    _ = |1 - t * ‖z‖⁻¹| * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ = |‖z‖ - t| := by
      calc
        |1 - t * ‖z‖⁻¹| * ‖z‖ = |1 - t * ‖z‖⁻¹| * |‖z‖| := by rw [abs_of_pos hn]
        _ = |(1 - t * ‖z‖⁻¹) * ‖z‖| := (abs_mul _ _).symm
        _ = |‖z‖ - t| := by congr 1; field_simp

def kernel (f : ℂ → ℝ) (V : ℂ → ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  f (z - t • V z) / t

def cutoff (f : ℂ → ℝ) (V : ℂ → ℂ) (ε R : ℝ) (z : ℂ) : ℝ :=
  ∫ t in {t : ℝ | ε ≤ |t| ∧ |t| ≤ R}, kernel f V z t

def conePV (z : ℂ) : ℝ := ∫ t in Icc (‖z‖ - 2) (‖z‖ + 2), kernel test field z t

theorem kernel_zero_outside {z : ℂ} (hz : z ∈ cone) {t : ℝ}
    (ht : t ∉ Icc (‖z‖ - 2) (‖z‖ + 2)) : kernel test field z t = 0 := by
  have hn : 2 ≤ |‖z‖ - t| := by
    rcases not_and_or.mp ht with h | h
    · have : t < ‖z‖ - 2 := lt_of_not_ge h
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have : ‖z‖ + 2 < t := lt_of_not_ge h
      rw [abs_of_nonpos (by linarith)]
      linarith
  rw [kernel, test_zero (by simpa only [radial_line hz] using hn), zero_div]

theorem kernel_nonneg {z : ℂ} (hz : z ∈ cone) (t : ℝ) : 0 ≤ kernel test field z t := by
  by_cases ht : t ∈ Icc (‖z‖ - 2) (‖z‖ + 2)
  · exact div_nonneg (test_nonneg _) (by linarith [(cone_norm hz).1, ht.1])
  · rw [kernel_zero_outside hz ht]

theorem kernel_integrableOn {z : ℂ} (hz : z ∈ cone) :
    IntegrableOn (kernel test field z) (Icc (‖z‖ - 2) (‖z‖ + 2)) := by
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.div
  · exact (test.continuous.comp
      (continuous_const.sub (continuous_id.smul continuous_const))).continuousOn
  · exact continuous_id.continuousOn
  · intro t ht
    linarith [(cone_norm hz).1, ht.1]

theorem kernel_integrable {z : ℂ} (hz : z ∈ cone) :
    Integrable (kernel test field z) :=
  (kernel_integrableOn hz).integrable_of_forall_notMem_eq_zero
    (fun _t ht => kernel_zero_outside hz ht)

theorem cutoff_integrable {z : ℂ} (hz : z ∈ cone) (ε R : ℝ) :
    IntegrableOn (kernel test field z) {t : ℝ | ε ≤ |t| ∧ |t| ≤ R} :=
  (kernel_integrable hz).integrableOn

theorem kernel_plateau {z : ℂ} (hz : z ∈ cone) {t : ℝ}
    (ht : t ∈ Icc (‖z‖ - 1) (‖z‖ + 1)) : kernel test field z t = t⁻¹ := by
  have ha : |‖z‖ - t| ≤ 1 := abs_le.mpr (by constructor <;> linarith [ht.1, ht.2])
  rw [kernel, test_one (by simpa only [radial_line hz] using ha), one_div]

theorem conePV_lower {z : ℂ} (hz : z ∈ cone) : 1 / (2 * z.re) ≤ conePV z := by
  have hr := (cone_norm hz).1
  have hx : 0 < z.re := by linarith [hz.1]
  have hr0 : 0 < ‖z‖ := by linarith
  have hsub : Icc (‖z‖ - 1) (‖z‖ + 1) ⊆ Icc (‖z‖ - 2) (‖z‖ + 2) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hmon := setIntegral_mono_set (kernel_integrableOn hz)
    (ae_of_all _ (fun t => kernel_nonneg hz t)) (Eventually.of_forall hsub)
  have hc : (2 : ℝ) / (‖z‖ + 1) ≤
      ∫ t in Icc (‖z‖ - 1) (‖z‖ + 1), kernel test field z t := by
    have hm := setIntegral_ge_of_const_le_real measurableSet_Icc
      (measure_Icc_lt_top.ne) (c := (‖z‖ + 1)⁻¹)
      (fun t ht => by
        rw [kernel_plateau hz ht]
        exact inv_anti₀ (by linarith [ht.1]) ht.2)
      ((kernel_integrableOn hz).mono_set hsub)
    simpa only [Real.volume_real_Icc_of_le (by linarith : ‖z‖ - 1 ≤ ‖z‖ + 1),
      add_sub_sub_cancel, inv_mul_eq_div, one_add_one_eq_two] using hm
  have h1 : 1 / ‖z‖ ≤ 2 / (‖z‖ + 1) := by
    apply (div_le_div_iff₀ hr0 (by positivity)).2
    linarith
  have h2 : 1 / (2 * z.re) ≤ 1 / ‖z‖ :=
    one_div_le_one_div_of_le hr0 (cone_norm hz).2
  exact h2.trans (h1.trans (hc.trans hmon))

theorem cutoff_eq_conePV {z : ℂ} (hz : z ∈ cone) {ε R : ℝ}
    (hε : ε ≤ ‖z‖ - 2) (hR : ‖z‖ + 2 ≤ R) :
    cutoff test field ε R z = conePV z := by
  have heq : cutoff test field ε R z = ∫ t, kernel test field z t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    apply kernel_zero_outside hz
    intro hs
    apply ht
    have ht0 : 0 ≤ t := by linarith [(cone_norm hz).1, hs.1]
    change ε ≤ |t| ∧ |t| ≤ R
    rw [abs_of_nonneg ht0]
    exact ⟨hε.trans hs.1, hs.2.trans hR⟩
  rw [heq]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => kernel_zero_outside hz ht)).symm

/-- Both inner and outer cutoffs are genuine limits, with no chosen totalized limit. -/
theorem conePV_tendsto {z : ℂ} (hz : z ∈ cone) :
    Tendsto (fun p : ℝ × ℝ => cutoff test field p.1 p.2 z)
      ((𝓝[>] (0 : ℝ)) ×ˢ atTop) (𝓝 (conePV z)) := by
  apply tendsto_const_nhds.congr'
  have hinner : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ ‖z‖ - 2 :=
    ((eventually_lt_nhds (by linarith [(cone_norm hz).1] : (0 : ℝ) < ‖z‖ - 2)).filter_mono
      nhdsWithin_le_nhds).mono (fun _ h => h.le)
  exact (hinner.prod_mk (eventually_ge_atTop (‖z‖ + 2))).mono
    (fun p hp => (cutoff_eq_conePV hz hp.1 hp.2).symm)

/-- The actual positive-width Euclidean cone makes the square lower bound nonintegrable. -/
theorem no_memLp_cone_lower (g : ℂ → ℝ) (hg : MemLp g 2)
    (hb : ∀ᵐ z, z ∈ cone → 1 / (2 * z.re) ≤ g z) : False := by
  let e := Complex.measurableEquivRealProd
  have hi : Integrable (fun p : ℝ × ℝ => g (e.symm p) ^ 2)
      (volume.prod volume) :=
    euclidean_volume.symm.integrable_comp_of_integrable hg.integrable_sq
  have hb' : ∀ᵐ p : ℝ × ℝ, e.symm p ∈ cone →
      1 / (2 * (e.symm p).re) ≤ g (e.symm p) :=
    euclidean_volume.symm.quasiMeasurePreserving.ae hb
  have hrows := hi.integral_prod_left
  have hdom : ∀ᵐ x : ℝ, x ∈ Ici 4 →
      1 / (4 * x) ≤ ∫ y : ℝ, g (e.symm (x, y)) ^ 2 := by
    filter_upwards [hi.prod_right_ae, Measure.ae_ae_of_ae_prod hb'] with x hix hbx hx
    have hx4 : 4 ≤ x := hx
    have hx0 : 0 < x := by linarith
    have hlower : ∫ y in Icc (0 : ℝ) x, (1 / (2 * x)) ^ 2 ≤
        ∫ y in Icc (0 : ℝ) x, g (e.symm (x, y)) ^ 2 := by
      have hconst : IntegrableOn (fun _ : ℝ => (1 / (2 * x)) ^ 2) (Icc 0 x) :=
        integrableOn_const measure_Icc_lt_top.ne
      apply setIntegral_mono_on_ae hconst hix.integrableOn measurableSet_Icc
      filter_upwards [hbx] with y hy hxy
      have hc : e.symm (x, y) ∈ cone := ⟨hx, hxy.1, hxy.2⟩
      have hxy' : 1 / (2 * x) ≤ g (e.symm (x, y)) := by
        simpa only [e, Complex.measurableEquivRealProd_symm_apply] using hy hc
      have hp : 0 ≤ 1 / (2 * x) := by positivity
      exact (sq_le_sq₀ hp (hp.trans hxy')).2 hxy'
    have he : (∫ y in Icc (0 : ℝ) x, (1 / (2 * x)) ^ 2) = 1 / (4 * x) := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hx0.le]
      simp only [sub_zero]
      field_simp
      ring
    rw [he] at hlower
    exact hlower.trans (setIntegral_le_integral hix (ae_of_all _ (fun y => sq_nonneg _)))
  have hsmall : IntegrableOn (fun x : ℝ => 1 / (4 * x)) (Ici 4) := by
    refine hrows.integrableOn.mono' ?_ ?_
    · exact (measurable_const.div (measurable_const.mul measurable_id)).aestronglyMeasurable
    · filter_upwards [(ae_restrict_iff' measurableSet_Ici).2 hdom,
        ae_restrict_mem measurableSet_Ici] with x hdx hx
      have hx4 : 4 ≤ x := hx
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (4 * x))]
        using hdx
  apply (not_integrableOn_Ici_inv (a := (4 : ℝ)))
  have hfour := hsmall.const_mul 4
  exact hfour.congr (ae_of_all _ (fun x => by
    simp only [one_div, mul_inv_rev]
    ring))

theorem no_L2_PV_representative (g : ℂ → ℝ) (hg : MemLp g 2)
    (hPV : ∀ᵐ z, z ∈ cone →
      Tendsto (fun p : ℝ × ℝ => cutoff test field p.1 p.2 z)
        ((𝓝[>] (0 : ℝ)) ×ˢ atTop) (𝓝 (g z))) : False := by
  apply no_memLp_cone_lower g hg
  filter_upwards [hPV] with z hz hcone
  have he : conePV z = g z := tendsto_nhds_unique (conePV_tendsto hcone) (hz hcone)
  rw [← he]
  exact conePV_lower hcone

/-- Native strong-L2 bounded operators, with the actual full principal values on Schwartz tests. -/
def RepresentsFullPV (V : ℂ → ℂ)
    (T : Lp ℝ 2 (volume : Measure ℂ) →L[ℝ] Lp ℝ 2 (volume : Measure ℂ)) : Prop :=
  ∀ f : 𝓢(ℂ, ℝ), ∀ᵐ z : ℂ,
    Tendsto (fun p : ℝ × ℝ => cutoff f V p.1 p.2 z)
      ((𝓝[>] (0 : ℝ)) ×ˢ atTop) (𝓝 ((T (f.toLp 2)) z))

theorem no_bounded_fullPV_operator :
    ¬ ∃ T : Lp ℝ 2 (volume : Measure ℂ) →L[ℝ] Lp ℝ 2 (volume : Measure ℂ),
      RepresentsFullPV field T := by
  rintro ⟨T, hT⟩
  apply no_L2_PV_representative (T (test.toLp 2)) (Lp.memLp _)
  exact (hT test).mono (fun z hz _ => hz)

theorem printed_untruncated_conjunct_false :
    ∃ V : ℂ → ℂ, LipschitzWith 2 V ∧ (∀ z, ‖V z‖ = 1) ∧
      ¬ ∃ T : Lp ℝ 2 (volume : Measure ℂ) →L[ℝ] Lp ℝ 2 (volume : Measure ℂ),
        RepresentsFullPV V T :=
  ⟨field, field_lipschitz, field_unit, no_bounded_fullPV_operator⟩

end TLMC1911
