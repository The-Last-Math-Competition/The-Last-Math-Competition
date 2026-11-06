import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped FourierTransform ENNReal Topology Interval

namespace TLMC1906

noncomputable section

def input (R : ℝ) : ℝ → ℂ := (Icc (-R) R).indicator (fun _ => 1)

def projection (a b : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  𝓕⁻ ((Icc a b).indicator (𝓕 f))

def squareFunction {m : ℕ} (a b : Fin m → ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  Real.sqrt (∑ i, ‖projection (a i) (b i) f x‖ ^ 2)

def Admissible (p C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (m : ℕ) (a b : Fin m → ℝ), (∀ i, a i ≤ b i) →
    Pairwise (fun i j => Disjoint (Icc (a i) (b i)) (Icc (a j) (b j))) →
    ∀ f : ℝ → ℂ, Integrable f → MemLp f (ENNReal.ofReal p) →
      eLpNorm (squareFunction a b f) (ENNReal.ofReal p) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p)

theorem singleton_square (a b : ℝ) (f : ℝ → ℂ) :
    squareFunction (fun _ : Fin 1 => a) (fun _ => b) f = fun x => ‖projection a b f x‖ := by
  funext x
  simp [squareFunction]

theorem Admissible.singleton {p C : ℝ} (h : Admissible p C) {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℂ} (hf : Integrable f) (hfp : MemLp f (ENNReal.ofReal p)) :
    eLpNorm (projection a b f) (ENNReal.ofReal p) ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) := by
  have hdis : Pairwise (fun i j : Fin 1 =>
      Disjoint (Icc a b) (Icc a b)) := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  have hb := h.2 1 (fun _ => a) (fun _ => b) (fun _ => hab) hdis f hf hfp
  simpa only [singleton_square, eLpNorm_norm] using hb

theorem input_memLp (R : ℝ) (p : ℝ≥0∞) : MemLp (input R) p := by
  apply memLp_indicator_const p measurableSet_Icc (1 : ℂ)
  right
  simp [Real.volume_Icc]

theorem input_integrable (R : ℝ) : Integrable (input R) :=
  memLp_one_iff_integrable.mp (input_memLp R 1)

theorem input_fourier (R ξ : ℝ) :
    𝓕 (input R) ξ = ∫ y in Icc (-R) R,
      Complex.exp ((↑(-2 * Real.pi * y * ξ) : ℂ) * Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Icc (-R) R
  · simp [input, hy]
  · simp [input, hy]

theorem projection_integral (a b : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    projection a b f x = ∫ ξ in Icc a b,
      Complex.exp ((↑(2 * Real.pi * x * ξ) : ℂ) * Complex.I) * 𝓕 f ξ := by
  rw [projection, Real.fourierInv_eq_fourier_neg,
    Real.fourier_real_eq_integral_exp_smul, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with ξ
  by_cases hξ : ξ ∈ Icc a b
  · simp only [indicator_of_mem hξ, smul_eq_mul]
    congr 2
    push_cast
    ring
  · simp [hξ]

def phase (x ξ y : ℝ) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * (x - y) * ξ) : ℂ) * Complex.I)

theorem phase_norm (x ξ y : ℝ) : ‖phase x ξ y‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem phase_integrable (R x : ℝ) :
    Integrable (Function.uncurry (phase x))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (-R) R))) := by
  apply (integrable_const (1 : ℝ)).mono'
    (show AEStronglyMeasurable (Function.uncurry (phase x)) _ from
      (by unfold phase Function.uncurry; fun_prop :
        Continuous (Function.uncurry (phase x))).aestronglyMeasurable)
  filter_upwards with z
  simp [Function.uncurry, phase_norm]

theorem projection_input_double (R x : ℝ) :
    projection 0 1 (input R) x = ∫ ξ in Icc (0 : ℝ) 1,
      ∫ y in Icc (-R) R, phase x ξ y := by
  rw [projection_integral]
  apply setIntegral_congr_fun measurableSet_Icc
  intro ξ _
  dsimp only
  rw [input_fourier, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y _
  dsimp only [phase]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem projection_input_swap (R x : ℝ) :
    projection 0 1 (input R) x = ∫ y in Icc (-R) R,
      ∫ ξ in Icc (0 : ℝ) 1, phase x ξ y := by
  rw [projection_input_double]
  exact integral_integral_swap (phase_integrable R x)

def kernel (t : ℝ) : ℂ :=
  (Complex.exp ((↑(2 * Real.pi * t) : ℂ) * Complex.I) - 1) /
    ((↑(2 * Real.pi * t) : ℂ) * Complex.I)

theorem phase_interval (x y : ℝ) (hxy : x - y ≠ 0) :
    (∫ ξ in Icc (0 : ℝ) 1, phase x ξ y) = kernel (x - y) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hn : (↑(2 * Real.pi * (x - y)) : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hxy)) Complex.I_ne_zero
  have he : (fun ξ : ℝ => phase x ξ y) = fun ξ : ℝ =>
      Complex.exp (((↑(2 * Real.pi * (x - y)) : ℂ) * Complex.I) * ξ) := by
    funext ξ
    unfold phase
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex hn]
  simp [kernel]

theorem projection_input_kernel {R x : ℝ} (hR : 0 ≤ R) (hx : R < x) :
    projection 0 1 (input R) x = ∫ y in -R..R, kernel (x - y) := by
  rw [projection_input_swap]
  calc
    (∫ y in Icc (-R) R, ∫ ξ in Icc (0 : ℝ) 1, phase x ξ y) =
        ∫ y in Icc (-R) R, kernel (x - y) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      apply phase_interval
      linarith [hy.2]
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]

theorem projection_input_kernel_shift {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    projection 0 1 (input R) (R + δ) = ∫ t in δ..(2 * R + δ), kernel t := by
  rw [projection_input_kernel hR (by linarith), intervalIntegral.integral_comp_sub_left]
  congr 1 <;> ring

theorem inv_square_integral {a b A : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (A * t ^ 2)) = (1 / A) * (1 / a - 1 / b) := by
  have hn : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    intro h
    linarith [h.1]
  calc
    (∫ t in a..b, 1 / (A * t ^ 2)) =
        (1 / A) * ∫ t in a..b, t ^ (-2 : ℤ) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext t
      simp only [div_eq_mul_inv, zpow_neg, zpow_ofNat, one_mul, mul_inv_rev]
      ring
    _ = _ := by
      rw [integral_zpow (a := a) (b := b) (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hn⟩)]
      norm_num only [Int.reduceAdd, Int.cast_neg, Int.cast_one, zpow_neg_one, div_neg, div_one]
      ring

theorem cosine_integral_bound {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, Real.cos (2 * Real.pi * t) / t) ≤ 1 := by
  let A : ℝ := 2 * Real.pi
  have hA : 0 < A := by dsimp [A]; positivity
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have ht0 : ∀ t ∈ uIcc a b, t ≠ 0 := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  have hC : ContinuousOn (fun t => Real.cos (A * t) / t) (uIcc a b) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact ht0
  have hS : ContinuousOn (fun t => Real.sin (A * t) / (A * t ^ 2)) (uIcc a b) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact mul_ne_zero hA.ne' (pow_ne_zero 2 (ht0 t ht))
  have hQ : ContinuousOn (fun t => 1 / (A * t ^ 2)) (uIcc a b) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact mul_ne_zero hA.ne' (pow_ne_zero 2 (ht0 t ht))
  have hF : ∀ t ∈ uIcc a b, HasDerivAt
      (fun s => Real.sin (A * s) / (A * s))
      (Real.cos (A * t) / t - Real.sin (A * t) / (A * t ^ 2)) t := by
    intro t ht
    have hs := (Real.hasDerivAt_sin (A * t)).comp t ((hasDerivAt_id t).const_mul A)
    have hd := (hasDerivAt_id t).const_mul A
    convert hs.div hd (mul_ne_zero hA.ne' (ht0 t ht)) using 1 <;>
      (try dsimp only [Function.comp_apply, id_eq]) <;>
      first | rfl | field_simp [hA.ne', ht0 t ht]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((hC.sub hS).intervalIntegrable)
  rw [intervalIntegral.integral_sub hC.intervalIntegrable hS.intervalIntegrable] at hFTC
  have hSQ : (∫ t in a..b, Real.sin (A * t) / (A * t ^ 2)) ≤
      (1 / A) * (1 / a - 1 / b) := by
    rw [← inv_square_integral ha0 hab]
    apply intervalIntegral.integral_mono_on hab hS.intervalIntegrable hQ.intervalIntegrable
    intro t ht
    apply div_le_div_of_nonneg_right (Real.sin_le_one _)
    positivity
  have hFb : Real.sin (A * b) / (A * b) ≤ 1 / (A * b) :=
    div_le_div_of_nonneg_right (Real.sin_le_one _) (by positivity)
  have hFa : -1 / (A * a) ≤ Real.sin (A * a) / (A * a) :=
    div_le_div_of_nonneg_right (Real.neg_one_le_sin _) (by positivity)
  have he : 1 / (A * b) - (-1 / (A * a)) + (1 / A) * (1 / a - 1 / b) =
      2 / (A * a) := by
    field_simp
    ring
  have hbound : (∫ t in a..b, Real.cos (A * t) / t) ≤ 2 / (A * a) := by
    linarith
  apply hbound.trans
  apply (div_le_one (by positivity : 0 < A * a)).mpr
  dsimp [A]
  nlinarith [Real.two_le_pi]

theorem kernel_im (t : ℝ) :
    (kernel t).im = (1 - Real.cos (2 * Real.pi * t)) / (2 * Real.pi * t) := by
  by_cases ht : t = 0
  · simp [ht, kernel]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp [kernel, Complex.div_im, Complex.normSq, Complex.exp_re, Complex.exp_im]
  field_simp
  ring

theorem projection_input_im {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    (projection 0 1 (input R) (R + δ)).im =
      (∫ t in δ..(2 * R + δ), (1 - Real.cos (2 * Real.pi * t)) / t) /
        (2 * Real.pi) := by
  have hab : δ ≤ 2 * R + δ := by linarith
  have hn : ∀ t ∈ uIcc δ (2 * R + δ),
      (↑(2 * Real.pi * t) : ℂ) * Complex.I ≠ 0 := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) ht0)) Complex.I_ne_zero
  have hk : IntervalIntegrable kernel volume δ (2 * R + δ) := by
    apply ContinuousOn.intervalIntegrable
    unfold kernel
    exact ContinuousOn.div (by fun_prop) (by fun_prop) hn
  rw [projection_input_kernel_shift hR hδ,
    intervalIntegral.integral_of_le hab]
  change RCLike.im (∫ t in Ioc δ (2 * R + δ), kernel t) = _
  rw [← integral_im hk.1]
  have him : ∀ t, RCLike.im (kernel t) =
      ((1 - Real.cos (2 * Real.pi * t)) / t) / (2 * Real.pi) := by
    intro t
    rw [show RCLike.im (kernel t) = (kernel t).im from rfl, kernel_im]
    rw [mul_comm (2 * Real.pi), div_mul_eq_div_div]
  simp_rw [him]
  rw [integral_div, ← intervalIntegral.integral_of_le hab]

theorem projection_input_im_lower {R δ : ℝ} (hR : 1 ≤ R) (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2) :
    (Real.log R - 1) / (2 * Real.pi) ≤
      (projection 0 1 (input R) (R + δ)).im := by
  have hR0 : 0 < R := by linarith
  have hδ0 : 0 < δ := by linarith
  have hab : δ ≤ 2 * R + δ := by linarith
  have ht : ∀ t ∈ uIcc δ (2 * R + δ), t ≠ 0 := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  have hi : ContinuousOn (fun t : ℝ => 1 / t) (uIcc δ (2 * R + δ)) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) ht
  have hc : ContinuousOn (fun t : ℝ => Real.cos (2 * Real.pi * t) / t)
      (uIcc δ (2 * R + δ)) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) ht
  rw [projection_input_im (by linarith) hδ0]
  have hd : (fun t : ℝ => (1 - Real.cos (2 * Real.pi * t)) / t) =
      (fun t : ℝ => 1 / t - Real.cos (2 * Real.pi * t) / t) := by
    funext t
    exact sub_div _ _ _
  rw [hd]
  rw [intervalIntegral.integral_sub hi.intervalIntegrable hc.intervalIntegrable,
    integral_one_div_of_pos hδ0 (by linarith)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hratio : R ≤ (2 * R + δ) / δ := by
    apply (le_div_iff₀ hδ0).mpr
    nlinarith
  have hl := Real.log_le_log hR0 hratio
  have hb := cosine_integral_bound hδ hab
  linarith

theorem input_eLpNorm {p : ℝ} (hp : 0 < p) (R : ℝ) :
    eLpNorm (input R) (ENNReal.ofReal p) =
      ENNReal.ofReal (2 * R) ^ (1 / p) := by
  unfold input
  rw [eLpNorm_indicator_const measurableSet_Icc
    (ENNReal.ofReal_pos.mpr hp).ne' (by finiteness)]
  simp [Real.volume_Icc, ENNReal.toReal_ofReal hp.le, sub_neg_eq_add, ← two_mul]

theorem input_exponential_norm {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (input (Real.exp p)) (ENNReal.ofReal p) ≤
      ENNReal.ofReal (2 * Real.exp 1) := by
  have hp0 : 0 < p := by linarith
  rw [input_eLpNorm hp0, ENNReal.ofReal_rpow_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos p).le]
  have he : (Real.exp p) ^ (1 / p) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos (Real.exp_pos p), Real.log_exp,
      mul_one_div_cancel hp0.ne']
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos 1).le
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      ((div_le_one hp0).mpr hp)

theorem projection_input_continuous (R : ℝ) :
    Continuous (projection 0 1 (input R)) := by
  have hc : Continuous (𝓕 (input R)) := by
    have h := (Real.Lp.fourierTransform (input_memLp R 1).toLp).continuous
    simpa only [Real.fourierTransform_toLp] using h
  have hf : Integrable ((Icc (0 : ℝ) 1).indicator (𝓕 (input R))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hc.integrableOn_Icc
  have hm := memLp_one_iff_integrable.mpr hf
  have hi := (Real.Lp.fourierTransformInv hm.toLp).continuous
  simpa only [Real.Lp.fourierTransformInv_toLp, projection] using hi

theorem Admissible.output_memLp {p C : ℝ} (h : Admissible p C) (R : ℝ) :
    MemLp (projection 0 1 (input R)) (ENNReal.ofReal p) := by
  refine ⟨(projection_input_continuous R).aestronglyMeasurable, ?_⟩
  have hb := h.singleton (by norm_num : (0 : ℝ) ≤ 1)
    (input_integrable R) (input_memLp R (ENNReal.ofReal p))
  apply hb.trans_lt
  exact ENNReal.mul_lt_top (by finiteness) (input_memLp R (ENNReal.ofReal p)).2

theorem output_eLpNorm_lower {p R c : ℝ} (hp : 0 < p) (hc : 0 ≤ c)
    (hpoint : ∀ x ∈ Icc (R + 1) (R + 2), c ≤ ‖projection 0 1 (input R) x‖) :
    ENNReal.ofReal c ≤ eLpNorm (projection 0 1 (input R)) (ENNReal.ofReal p) := by
  have hμ : volume (Icc (R + 1) (R + 2)) = 1 := by
    rw [Real.volume_Icc, show R + 2 - (R + 1) = 1 by ring]
    norm_num
  have hi : eLpNorm ((Icc (R + 1) (R + 2)).indicator (fun _ : ℝ => c))
      (ENNReal.ofReal p) = ENNReal.ofReal c := by
    rw [eLpNorm_indicator_const measurableSet_Icc
      (ENNReal.ofReal_pos.mpr hp).ne' (by finiteness), hμ]
    simp [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [← hi]
  apply eLpNorm_mono
  intro x
  by_cases hx : x ∈ Icc (R + 1) (R + 2)
  · simpa only [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hc] using hpoint x hx
  · simp [indicator_of_notMem hx]

theorem exponential_output_lower {p : ℝ} (hp : 2 ≤ p) :
    ENNReal.ofReal ((p - 1) / (2 * Real.pi)) ≤
      eLpNorm (projection 0 1 (input (Real.exp p))) (ENNReal.ofReal p) := by
  apply output_eLpNorm_lower (by linarith : 0 < p)
    (div_nonneg (by linarith) (by positivity))
  intro x hx
  have hR : 1 ≤ Real.exp p := Real.one_le_exp (by linarith)
  have h := projection_input_im_lower hR (δ := x - Real.exp p)
    (by linarith [hx.1]) (by linarith [hx.2])
  rw [Real.log_exp, add_sub_cancel] at h
  exact h.trans (Complex.im_le_norm _)

theorem Admissible.linear_lower {p C : ℝ} (hp : 2 ≤ p) (h : Admissible p C) :
    p / (8 * Real.pi * Real.exp 1) ≤ C := by
  have hnorm := h.singleton (by norm_num : (0 : ℝ) ≤ 1)
    (input_integrable (Real.exp p)) (input_memLp (Real.exp p) (ENNReal.ofReal p))
  have hinput := input_exponential_norm (by linarith : 1 ≤ p)
  have hmul : ENNReal.ofReal C * eLpNorm (input (Real.exp p)) (ENNReal.ofReal p) ≤
      ENNReal.ofReal C * ENNReal.ofReal (2 * Real.exp 1) := by
    gcongr
  have hlow := (exponential_output_lower hp).trans
    (hnorm.trans hmul)
  rw [← ENNReal.ofReal_mul h.1] at hlow
  have hr : (p - 1) / (2 * Real.pi) ≤ C * (2 * Real.exp 1) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg h.1 (by positivity))).mp hlow
  have hr' := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hr
  apply (div_le_iff₀ (by positivity : 0 < 8 * Real.pi * Real.exp 1)).mpr
  nlinarith

theorem no_sqrt_bigO (C : ℝ → ℝ) (hC : ∀ p, 2 ≤ p → Admissible p (C p)) :
    ¬ Asymptotics.IsBigO atTop C Real.sqrt := by
  intro ho
  obtain ⟨K, hK, hb⟩ := ho.exists_pos
  obtain ⟨P, hP⟩ := eventually_atTop.mp hb.bound
  let A : ℝ := 8 * Real.pi * Real.exp 1
  have hA : 0 < A := by dsimp [A]; positivity
  let t : ℝ := |P| + A * K + 2
  have ht : 2 ≤ t := by dsimp [t]; linarith [abs_nonneg P, mul_pos hA hK]
  have htK : A * K < t := by dsimp [t]; linarith [abs_nonneg P]
  have hp2 : 2 ≤ t ^ 2 := by nlinarith
  have hpP : P ≤ t ^ 2 := by
    have habs : P ≤ |P| := le_abs_self P
    have habst : |P| ≤ t := by dsimp [t]; linarith [mul_pos hA hK]
    nlinarith
  have hbound := hP (t ^ 2) hpP
  have hvalid := hC (t ^ 2) hp2
  have hlower := hvalid.linear_lower hp2
  have hnonneg : 0 ≤ C (t ^ 2) := hvalid.1
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_sq (by linarith : 0 ≤ t)] at hbound
  have hmul := mul_le_mul_of_nonneg_right hbound hA.le
  have hlin : t ^ 2 ≤ C (t ^ 2) * A := (div_le_iff₀ hA).mp hlower
  nlinarith

theorem no_finite_sqrt_coefficient (C : ℝ → ℝ)
    (hC : ∀ p, 2 ≤ p → Admissible p (C p)) (L : ℝ) :
    ¬ Tendsto (fun p => C p / Real.sqrt p) atTop (𝓝 L) := by
  intro hL
  apply no_sqrt_bigO C hC
  obtain ⟨K, _, hb⟩ := (hL.isBigO_one ℝ).exists_pos
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [hb.bound, eventually_ge_atTop (2 : ℝ)] with p hp hp2
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  simp only [norm_div, Real.norm_eq_abs, abs_of_nonneg hs.le, norm_one, mul_one] at hp
  have h := (div_le_iff₀ hs).mp hp
  simpa only [Real.norm_eq_abs, abs_of_nonneg hs.le] using h

end
end TLMC1906
