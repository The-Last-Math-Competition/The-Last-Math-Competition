import Mathlib
import Conjecture4391.Statement

/-!
# Conjecture 00000004391: spectral radius extremes among graphons of fixed edge density

The conjecture says that, among graphons of fixed edge density, the maximum spectral radius is
attained only by the twin-clique graphon and the minimum only by the half-graph graphon.
We refute the *minimum* conjunct (hence the conjunction): the half graph is not a minimizer,
because the constant graphon of the same density has strictly smaller spectral radius.
-/

-- (formal statement: see Statement.lean)

namespace C4391
open MeasureTheory Set

/-- The constant graphon `W ≡ p`. -/
noncomputable def constG (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : Graphon where
  W _ _ := p
  meas := measurable_const
  symm _ _ := rfl
  nonneg _ _ := hp.1
  le_one _ _ := hp.2

/-- Every eigenvalue of a graphon bounded by `c` has `|lam| ≤ c`. -/
theorem eig_abs_le (G : Graphon) {c : ℝ} (hc : ∀ x y, G.W x y ≤ c) {lam : ℝ}
    (h : IsEigenvalue G lam) : |lam| ≤ c := by
  obtain ⟨f, hf2, hne, hae⟩ := h
  have hint : IntegrableOn f (Ioc (0:ℝ) 1) := hf2.integrable (by norm_num)
  have habs : IntervalIntegrable (fun x => |f x|) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hint.abs
  set M : ℝ := ∫ x in (0:ℝ)..1, |f x| with hMdef
  have hM : 0 < M := by
    rw [hMdef, intervalIntegral.integral_of_le zero_le_one]
    by_contra hle
    push Not at hle
    have h0 : ∫ x in Ioc (0:ℝ) 1, |f x| = 0 :=
      le_antisymm hle (integral_nonneg fun _ => abs_nonneg _)
    rw [integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) hint.abs] at h0
    exact hne (by filter_upwards [h0] with x hx using abs_eq_zero.1 hx)
  have hpt : ∀ x, |op G f x| ≤ c * M := by
    intro x
    have hc0 : 0 ≤ c := (G.nonneg x x).trans (hc x x)
    have := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := 1) (μ := volume)
      (f := fun y => G.W x y * f y) (g := fun y => c * |f y|) zero_le_one
      (Filter.Eventually.of_forall fun y _ => by
        rw [norm_mul, Real.norm_of_nonneg (G.nonneg x y), Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hc x y) (abs_nonneg _)) (habs.const_mul c)
    rwa [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at this
  have hle : ∫ x in (0:ℝ)..1, |lam| * |f x| ≤ ∫ x in (0:ℝ)..1, c * M := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_mono_ae_restrict (hint.abs.const_mul _) (integrableOn_const (by simp)) ?_
    filter_upwards [hae] with x hx
    have := hpt x
    rw [hx, abs_mul] at this
    exact this
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hle
  simp only [sub_zero, smul_eq_mul, one_mul] at hle
  nlinarith

theorem bdd (G : Graphon) : BddAbove {lam | IsEigenvalue G lam} :=
  ⟨1, fun _ hl => (le_abs_self _).trans (eig_abs_le G G.le_one hl)⟩

theorem bddAbs (G : Graphon) : BddAbove {r | ∃ lam, IsEigenvalue G lam ∧ r = |lam|} :=
  ⟨1, fun _ ⟨_, hl, hr⟩ => hr ▸ eig_abs_le G G.le_one hl⟩

theorem not_ae_zero {f : ℝ → ℝ} {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1)
    (h : ∫ x in (0:ℝ)..b, f x ≠ 0) :
    ¬ (f =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] 0) := fun hae => by
  apply h
  rw [intervalIntegral.integral_of_le hb0]
  have : f =ᵐ[volume.restrict (Ioc (0:ℝ) b)] 0 :=
    ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right hb) le_rfl) hae
  exact (integral_congr_ae this).trans (by simp)

theorem memLp_of_bdd {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)) :=
  MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hC x)

/-! ### The constant graphon -/

theorem density_const (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : density (constG p hp) = p := by
  simp [density, constG]

theorem const_eig (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : IsEigenvalue (constG p hp) p :=
  ⟨fun _ => 1, memLp_of_bdd continuous_const (C := 1) (by simp),
    not_ae_zero (b := 1) zero_le_one le_rfl (by simp),
    Filter.Eventually.of_forall fun x => by simp [op, constG]⟩

theorem rad_const (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : spectralRadius (constG p hp) = p :=
  le_antisymm (csSup_le ⟨_, const_eig p hp⟩ fun _ hl => (le_abs_self _).trans
      (eig_abs_le (constG p hp) (fun _ _ => le_rfl) hl))
    (le_csSup (bdd _) (const_eig p hp))

theorem radAbs_const (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : spectralRadiusAbs (constG p hp) = p :=
  le_antisymm (csSup_le ⟨_, _, const_eig p hp, rfl⟩ fun _ ⟨_, hl, hr⟩ => hr ▸
      eig_abs_le (constG p hp) (fun _ _ => le_rfl) hl)
    (le_csSup (bddAbs _) ⟨_, const_eig p hp, (abs_of_nonneg hp.1).symm⟩)

/-! ### The half graph `1[x+y ≤ 1]` -/

theorem halfOp {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (g : ℝ → ℝ) :
    ∫ y in (0:ℝ)..1, halfGraph.W x y * g y = ∫ y in (0:ℝ)..(1 - x), g y := by
  have : (fun y => halfGraph.W x y * g y) = (Iic (1 - x)).indicator g := by
    ext y
    simp only [halfGraph, indicator, mem_Iic]
    by_cases h : y ≤ 1 - x
    · simp [h, show x + y ≤ 1 by linarith]
    · simp [h, show ¬ x + y ≤ 1 by intro h'; apply h; linarith]
  rw [this, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by linarith), integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  congr 2
  ext y
  simp only [mem_inter_iff, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩

theorem density_half : density halfGraph = 1/2 := by
  unfold density
  have : ∀ x ∈ uIcc (0:ℝ) 1, (∫ y in (0:ℝ)..1, halfGraph.W x y) = 1 - x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have := halfOp hx.1 hx.2 (fun _ => 1)
    simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    rw [this]
  rw [intervalIntegral.integral_congr this]
  rw [intervalIntegral.integral_sub (by simp) (by simp)]
  simp
  norm_num

theorem half_eig : IsEigenvalue halfGraph (2 / Real.pi) := by
  have hcos : ∀ a b : ℝ, ∫ y in a..b, Real.cos (Real.pi / 2 * y) =
      2 / Real.pi * (Real.sin (Real.pi / 2 * b) - Real.sin (Real.pi / 2 * a)) := by
    intro a b
    rw [intervalIntegral.integral_comp_mul_left (fun y => Real.cos y) (by positivity),
      integral_cos]
    simp only [smul_eq_mul]
    field_simp
  refine ⟨fun y => Real.cos (Real.pi / 2 * y),
    memLp_of_bdd (by fun_prop) (C := 1) fun x => Real.abs_cos_le_one _,
    not_ae_zero (b := 1) zero_le_one le_rfl ?_, ?_⟩
  · rw [hcos]; simp
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
    simp only [op]
    rw [halfOp hx.1.le hx.2, hcos]
    have : Real.sin (Real.pi / 2 * (1 - x)) = Real.cos (Real.pi / 2 * x) := by
      rw [mul_sub, mul_one, Real.sin_pi_div_two_sub]
    rw [this]
    simp

theorem rad_half_ge : 2 / Real.pi ≤ spectralRadius halfGraph :=
  le_csSup (bdd _) half_eig

theorem radAbs_half_ge : 2 / Real.pi ≤ spectralRadiusAbs halfGraph :=
  le_csSup (bddAbs _) ⟨_, half_eig, (abs_of_pos (by positivity)).symm⟩

theorem two_div_pi_gt : (1/2 : ℝ) < 2 / Real.pi := by
  rw [lt_div_iff₀ Real.pi_pos]
  linarith [Real.pi_lt_four]

theorem not_minPart (ρ : Graphon → ℝ) (H : Graphon) {p r : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hd : density H = p) (hH : r ≤ ρ H) (hC : ρ (constG p hp) ≤ p) (hlt : p < r) :
    ¬ MinPart ρ H := fun h => by
  have := ((h H rfl).2 (Filter.Eventually.of_forall fun _ => rfl)) (constG p hp)
    (by rw [density_const, hd])
  linarith

/-! ### The bipartite half graph -/

theorem halfOpBip {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (g : ℝ → ℝ) :
    ∫ y in (0:ℝ)..1, halfGraphBip.W x y * g y =
      if x ≤ 1/2 then ∫ y in (x + 1/2)..1, g y else ∫ y in (0:ℝ)..(x - 1/2), g y := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hx
  · have e1 : ∫ y in Ioc (0:ℝ) 1, halfGraphBip.W x y * g y =
        ∫ y in Ioc (0:ℝ) 1, (Ici (x + 1/2)).indicator g y := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun y hy => ?_)
      simp only [halfGraphBip]
      by_cases h : x + 1/2 ≤ y
      · rw [if_pos (Or.inl ⟨hx, h⟩), indicator_of_mem (mem_Ici.2 h), one_mul]
      · rw [if_neg (by rintro (⟨_, h'⟩ | ⟨h1, h2⟩) <;> [exact h h'; linarith [hy.1]]),
          indicator_of_notMem (by simpa using h), zero_mul]
    rw [e1, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    congr 2
    ext y
    simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  · push Not at hx
    have e1 : ∫ y in Ioc (0:ℝ) 1, halfGraphBip.W x y * g y =
        ∫ y in Ioc (0:ℝ) 1, (Iic (x - 1/2)).indicator g y := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun y hy => ?_)
      simp only [halfGraphBip]
      by_cases h : y ≤ x - 1/2
      · rw [if_pos (Or.inr ⟨by linarith, by linarith⟩), indicator_of_mem (mem_Iic.2 h), one_mul]
      · rw [if_neg (by rintro (⟨h1, _⟩ | ⟨h1, h2⟩) <;> [linarith; (apply h; linarith)]),
          indicator_of_notMem (by simpa using h), zero_mul]
    rw [e1, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      intervalIntegral.integral_of_le (by linarith)]
    congr 2
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩

theorem density_bip : density halfGraphBip = 1/4 := by
  unfold density
  have : ∀ x ∈ uIcc (0:ℝ) 1, (∫ y in (0:ℝ)..1, halfGraphBip.W x y) = |x - 1/2| := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have := halfOpBip hx.1 hx.2 (fun _ => 1)
    simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at this
    rw [this]
    split_ifs with h
    · rw [abs_of_nonpos (by linarith)]; ring
    · rw [abs_of_nonneg (by linarith)]; ring
  rw [intervalIntegral.integral_congr this,
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1/2)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_congr (g := fun x => 1/2 - x) (a := 0) (b := 1/2) (fun x hx => by
      rw [uIcc_of_le (by norm_num)] at hx; simp only; rw [abs_of_nonpos (by linarith [hx.2])]; ring),
    intervalIntegral.integral_congr (g := fun x => x - 1/2) (a := 1/2) (b := 1) (fun x hx => by
      rw [uIcc_of_le (by norm_num)] at hx; simp only; rw [abs_of_nonneg (by linarith [hx.1])])]
  rw [intervalIntegral.integral_sub (by simp) (by simp),
    intervalIntegral.integral_sub (by simp) (by simp)]
  simp
  norm_num

/-- Eigenfunction `cos(π x)` on the first half, `sin(π x - π/2)` on the second. -/
noncomputable def efB (y : ℝ) : ℝ :=
  if y < 1/2 then Real.cos (Real.pi * y) else Real.sin (Real.pi * y - Real.pi / 2)

theorem bip_eig : IsEigenvalue halfGraphBip (1 / Real.pi) := by
  have hpi := Real.pi_pos
  have hsin : ∀ a b : ℝ, ∫ y in a..b, Real.sin (Real.pi * y - Real.pi / 2) =
      (Real.pi)⁻¹ * (Real.cos (Real.pi * a - Real.pi / 2) -
        Real.cos (Real.pi * b - Real.pi / 2)) := by
    intro a b
    rw [intervalIntegral.integral_comp_mul_sub (fun y => Real.sin y) hpi.ne', integral_sin]
    simp only [smul_eq_mul]
  have hcos : ∀ a b : ℝ, ∫ y in a..b, Real.cos (Real.pi * y) =
      (Real.pi)⁻¹ * (Real.sin (Real.pi * b) - Real.sin (Real.pi * a)) := by
    intro a b
    rw [intervalIntegral.integral_comp_mul_left (fun y => Real.cos y) hpi.ne', integral_cos]
    simp only [smul_eq_mul]
  have hef1 : ∀ y, 1/2 ≤ y → efB y = Real.sin (Real.pi * y - Real.pi / 2) := fun y hy => by
    unfold efB; rw [if_neg (not_lt.2 hy)]
  have hef2 : ∀ y, y ≤ 1/2 → efB y = Real.cos (Real.pi * y) := fun y hy => by
    by_cases h : y < 1/2
    · unfold efB; rw [if_pos h]
    · have : y = 1/2 := le_antisymm hy (not_lt.1 h)
      subst this
      have e : Real.pi * (1/2) - Real.pi / 2 = 0 := by ring
      have e' : Real.pi * (1/2) = Real.pi / 2 := by ring
      unfold efB; rw [if_neg (by norm_num), e, e', Real.sin_zero, Real.cos_pi_div_two]
  have hmeas : Measurable efB :=
    Measurable.ite measurableSet_Iio (by fun_prop) (by fun_prop)
  refine ⟨efB, MemLp.of_bound hmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => ?_),
    not_ae_zero (b := 1/4) (by norm_num) (by norm_num) ?_, ?_⟩
  · unfold efB; split_ifs <;> simp [Real.abs_cos_le_one, Real.abs_sin_le_one]
  · rw [intervalIntegral.integral_congr (g := fun y => Real.cos (Real.pi * y)) (fun y hy => by
      rw [uIcc_of_le (by norm_num)] at hy; exact hef2 y (by linarith [hy.2])), hcos]
    have : 0 < Real.sin (Real.pi * (1/4)) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith
    simp only [mul_zero, Real.sin_zero, sub_zero]
    positivity
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
    simp only [op]
    rw [halfOpBip hx.1.le hx.2]
    split_ifs with h
    · rw [intervalIntegral.integral_congr (g := fun y => Real.sin (Real.pi * y - Real.pi / 2))
        (fun y hy => by
          rw [uIcc_of_le (by linarith)] at hy; exact hef1 y (by linarith [hy.1, hx.1])), hsin]
      have e1 : Real.pi * (x + 1/2) - Real.pi / 2 = Real.pi * x := by ring
      have e2 : Real.pi * 1 - Real.pi / 2 = Real.pi / 2 := by ring
      rw [e1, e2, Real.cos_pi_div_two, hef2 x h, sub_zero]
      field_simp
    · push Not at h
      rw [intervalIntegral.integral_congr (g := fun y => Real.cos (Real.pi * y))
        (fun y hy => by
          rw [uIcc_of_le (by linarith)] at hy; exact hef2 y (by linarith [hy.2, hx.2])), hcos,
        hef1 x h.le]
      have e1 : Real.pi * (x - 1/2) = Real.pi * x - Real.pi / 2 := by ring
      rw [e1]
      simp

theorem rad_bip_ge : 1 / Real.pi ≤ spectralRadius halfGraphBip := le_csSup (bdd _) bip_eig

theorem radAbs_bip_ge : 1 / Real.pi ≤ spectralRadiusAbs halfGraphBip :=
  le_csSup (bddAbs _) ⟨_, bip_eig, (abs_of_pos (by positivity)).symm⟩

theorem one_div_pi_gt : (1/4 : ℝ) < 1 / Real.pi := by
  rw [lt_div_iff₀ Real.pi_pos]
  linarith [Real.pi_lt_four]

theorem main : Claim := by
  have hh : (0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) ≤ 1 := by norm_num
  have hb : (0:ℝ) ≤ 1/4 ∧ (1/4:ℝ) ≤ 1 := by norm_num
  rintro (h | h | h | h)
  · exact not_minPart _ _ hh density_half rad_half_ge (rad_const _ hh).le two_div_pi_gt h
  · exact not_minPart _ _ hh density_half radAbs_half_ge (radAbs_const _ hh).le two_div_pi_gt h
  · exact not_minPart _ _ hb density_bip rad_bip_ge (rad_const _ hb).le one_div_pi_gt h
  · exact not_minPart _ _ hb density_bip radAbs_bip_ge (radAbs_const _ hb).le one_div_pi_gt h

end C4391
