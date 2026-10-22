import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option maxRecDepth 2000
set_option maxHeartbeats 1200000

noncomputable section
open Set Metric Filter
open scoped Topology ENNReal NNReal

namespace Conjecture947

abbrev E := Fin 2 → ℝ

/-- All genuine real norms on the fixed two-dimensional vector space. -/
structure IsNorm (N : E → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ N x
  eq_zero : ∀ x, N x = 0 ↔ x = 0
  add_le : ∀ x y, N (x + y) ≤ N x + N y
  smul_eq : ∀ (a : ℝ) x, N (a • x) = |a| * N x

def pairs (N : E → ℝ) (ε : ℝ) : Set (E × E) :=
  {z | N z.1 = 1 ∧ N z.2 = 1 ∧ ε ≤ N (z.1 - z.2)}

def defect (N : E → ℝ) (z : E × E) : ℝ :=
  1 - N ((1 / 2 : ℝ) • (z.1 + z.2))

/-- Clarkson's modulus, with its actual infimum over all admissible unit vectors. -/
def modulus (N : E → ℝ) (ε : ℝ) : ℝ := sInf (defect N '' pairs N ε)

def envelopeValues (ε : ℝ) : Set ℝ := {d | ∃ N, IsNorm N ∧ d = modulus N ε}
def envelope (ε : ℝ) : ℝ := sInf (envelopeValues ε)

lemma defect_nonneg {N : E → ℝ} (hN : IsNorm N) {ε : ℝ} {z : E × E}
    (hz : z ∈ pairs N ε) : 0 ≤ defect N z := by
  rcases hz with ⟨hx, hy, _⟩
  have ht := hN.add_le z.1 z.2
  rw [hx, hy] at ht
  dsimp [defect]
  rw [hN.smul_eq]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

lemma modulus_nonneg {N : E → ℝ} (hN : IsNorm N) (ε : ℝ) :
    0 ≤ modulus N ε := by
  apply Real.sInf_nonneg
  rintro _ ⟨z, hz, rfl⟩
  exact defect_nonneg hN hz

/-- The infimum is over a nonempty set throughout the geometric domain, for every norm. -/
lemma pairs_nonempty {N : E → ℝ} (hN : IsNorm N) {ε : ℝ} (hε2 : ε ≤ 2) :
    (pairs N ε).Nonempty := by
  let e : E := ![1,0]
  have he : e ≠ 0 := by intro h; have := congrFun h 0; norm_num [e] at this
  have hNe : N e ≠ 0 := fun h => he ((hN.eq_zero e).mp h)
  have hpos : 0 < N e := lt_of_le_of_ne (hN.nonneg e) hNe.symm
  let x := (N e)⁻¹ • e
  have hx : N x = 1 := by
    dsimp [x]
    rw [hN.smul_eq, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hNe]
  have hneg : N (-x) = 1 := by
    have := hN.smul_eq (-1) x
    simpa [hx] using this
  have hsub : x - -x = (2 : ℝ) • x := by ext i; simp; ring
  refine ⟨(x, -x), hx, hneg, ?_⟩
  rw [hsub, hN.smul_eq, hx]
  norm_num
  exact hε2

def infinityNorm (x : E) : ℝ := ‖x‖

lemma infinity_isNorm : IsNorm infinityNorm := by
  refine ⟨norm_nonneg, ?_, norm_add_le, ?_⟩
  · intro x
    exact norm_eq_zero
  · intro a x
    exact norm_smul a x

def u (ε : ℝ) : E := ![1, ε / 2]
def v (ε : ℝ) : E := ![1, -ε / 2]

lemma norm_vec2 (a b : ℝ) : ‖(![a,b] : E)‖ = max |a| |b| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg a))).2
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs, le_max_left, le_max_right]
  · exact max_le (by simpa using norm_le_pi_norm (![a,b] : E) 0)
      (by simpa using norm_le_pi_norm (![a,b] : E) 1)

lemma infinity_pair {ε : ℝ} (hε : 0 ≤ ε) (hε2 : ε ≤ 2) :
    (u ε, v ε) ∈ pairs infinityNorm ε ∧ defect infinityNorm (u ε, v ε) = 0 := by
  have habs : |ε / 2| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hu : infinityNorm (u ε) = 1 := by
    simp [infinityNorm, u, norm_vec2, habs, max_eq_left habs]
  have hv : infinityNorm (v ε) = 1 := by
    simp [infinityNorm, v, norm_vec2, abs_div, abs_neg, abs_of_nonneg hε,
      show ε / 2 ≤ 1 by linarith]
  have huv : infinityNorm (u ε - v ε) = ε := by
    have hvec : u ε - v ε = ![0, ε] := by ext i; fin_cases i <;> simp [u,v]; ring
    rw [hvec]
    simp [infinityNorm, norm_vec2, abs_of_nonneg hε, max_eq_right hε]
  constructor
  · exact ⟨hu, hv, huv.ge⟩
  · have hvec : (1 / 2 : ℝ) • (u ε + v ε) = ![1,0] := by
      ext i; fin_cases i <;> simp [u,v] <;> ring
    rw [defect, hvec]
    norm_num [infinityNorm, norm_vec2]

theorem infinity_modulus_zero {ε : ℝ} (hε : 0 ≤ ε) (hε2 : ε ≤ 2) :
    modulus infinityNorm ε = 0 := by
  apply le_antisymm _ (modulus_nonneg infinity_isNorm ε)
  obtain ⟨hz, hd⟩ := infinity_pair hε hε2
  have hb : BddBelow (defect infinityNorm '' pairs infinityNorm ε) :=
    ⟨0, by rintro _ ⟨z, hz, rfl⟩; exact defect_nonneg infinity_isNorm hz⟩
  exact (csInf_le hb (mem_image_of_mem _ hz)).trans_eq hd

theorem envelope_zero {ε : ℝ} (hε : 0 ≤ ε) (hε2 : ε ≤ 2) : envelope ε = 0 := by
  have hn : ∀ d ∈ envelopeValues ε, 0 ≤ d := by
    rintro d ⟨N, hN, rfl⟩
    exact modulus_nonneg hN ε
  apply le_antisymm _ (Real.sInf_nonneg hn)
  apply csInf_le ⟨0, hn⟩
  exact ⟨infinityNorm, infinity_isNorm, (infinity_modulus_zero hε hε2).symm⟩

lemma abs_mid_rpow_le {p : ℝ} (hp : 1 < p) (a b : ℝ) :
    |(a + b) / 2| ^ p ≤ (|a| ^ p + |b| ^ p) / 2 := by
  have htri : |(a + b) / 2| ≤ (|a| + |b|) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add a b) (by norm_num)
  have hconv := (convexOn_rpow hp.le).2 (abs_nonneg a) (abs_nonneg b)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hpow := Real.rpow_le_rpow (abs_nonneg ((a+b)/2)) htri (by linarith : 0 ≤ p)
  dsimp at hconv
  have hc : ((|a| + |b|) / 2) ^ p ≤ (|a| ^ p + |b| ^ p) / 2 := by
    convert hconv using 1 <;> congr 1 <;> ring
  exact hpow.trans hc

lemma abs_mid_rpow_lt {p : ℝ} (hp : 1 < p) {a b : ℝ} (hab : a ≠ b) :
    |(a + b) / 2| ^ p < (|a| ^ p + |b| ^ p) / 2 := by
  by_cases he : |a| = |b|
  · have hneg : a = -b := (abs_eq_abs.mp he).resolve_left hab
    have hb : b ≠ 0 := by intro hb; apply hab; simp_all
    rw [hneg]
    simp only [neg_add_cancel, zero_div, abs_zero, Real.zero_rpow (by linarith : p ≠ 0), abs_neg]
    have : 0 < |b| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr hb) p
    linarith
  · have htri : |(a + b) / 2| ≤ (|a| + |b|) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right (abs_add a b) (by norm_num)
    have hc := (strictConvexOn_rpow hp).2 (abs_nonneg a) (abs_nonneg b) he
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hpow := Real.rpow_le_rpow (abs_nonneg ((a+b)/2)) htri (by linarith : 0 ≤ p)
    dsimp at hc
    have hc' : ((|a| + |b|) / 2) ^ p < (|a| ^ p + |b| ^ p) / 2 := by
      convert hc using 1 <;> congr 1 <;> ring
    exact hpow.trans_lt hc'

abbrev lpVector (p : ℝ≥0∞) (x : E) : PiLp p (fun _ : Fin 2 => ℝ) :=
  (WithLp.equiv p E).symm x

def lpNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : E) : ℝ := ‖lpVector p x‖

lemma lp_isNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] : IsNorm (lpNorm p) := by
  refine ⟨fun x => norm_nonneg _, ?_, ?_, ?_⟩
  · intro x
    change ‖lpVector p x‖ = 0 ↔ x = 0
    rw [norm_eq_zero]
    exact (WithLp.equiv p E).symm.injective.eq_iff
  · intro x y
    exact norm_add_le (lpVector p x) (lpVector p y)
  · intro a x
    exact norm_smul a (lpVector p x)

lemma continuous_lpNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] : Continuous (lpNorm p) :=
  continuous_norm.comp (PiLp.continuous_equiv_symm p (fun _ : Fin 2 => ℝ))

lemma lpNorm_rpow (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (x : E) :
    lpNorm p x ^ p.toReal = ∑ i, |x i| ^ p.toReal := by
  rw [lpNorm, PiLp.norm_eq_sum hp]
  simp only [Real.norm_eq_abs, WithLp.equiv_symm_pi_apply, one_div]
  exact Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) hp.ne'

lemma lp_mid_lt (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    {x y : E} (hx : lpNorm p x = 1) (hy : lpNorm p y = 1) (hne : x ≠ y) :
    lpNorm p ((1 / 2 : ℝ) • (x+y)) < 1 := by
  classical
  have hp0 : 0 < p.toReal := by linarith
  have hs : (∑ i : Fin 2, |((1 / 2 : ℝ) • (x+y)) i| ^ p.toReal) <
      ∑ i : Fin 2, (|x i| ^ p.toReal + |y i| ^ p.toReal) / 2 := by
    apply Finset.sum_lt_sum
    · intro i _
      simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, div_eq_mul_inv, one_mul, mul_comm] using
        abs_mid_rpow_le hp (x i) (y i)
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra h
        apply hne
        funext i
        exact not_ne_iff.mp (not_exists.mp h i)
      refine ⟨i, Finset.mem_univ _, ?_⟩
      simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, div_eq_mul_inv, one_mul, mul_comm] using
        abs_mid_rpow_lt hp hi
  have hx' := lpNorm_rpow p hp0 x
  have hy' := lpNorm_rpow p hp0 y
  rw [hx, Real.one_rpow] at hx'
  rw [hy, Real.one_rpow] at hy'
  have hs' : (∑ i : Fin 2, (|x i| ^ p.toReal + |y i| ^ p.toReal) / 2) = 1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← hx', ← hy']
    norm_num
  rw [hs', ← lpNorm_rpow p hp0] at hs
  exact (Real.rpow_lt_one_iff' (norm_nonneg _) hp0).mp hs

lemma lp_pair_nonempty (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    {ε : ℝ} (hε2 : ε ≤ 2) : (pairs (lpNorm p) ε).Nonempty := by
  let e : E := ![1,0]
  have he : lpNorm p e = 1 := by
    rw [lpNorm, PiLp.norm_eq_sum hp]
    simp [e, Fin.sum_univ_two, Real.zero_rpow hp.ne']
  refine ⟨(e, -e), he, ?_, ?_⟩
  · change ‖-lpVector p e‖ = 1
    simpa only [norm_neg] using he
  · have hsub : e - -e = (2 : ℝ) • e := by ext i; simp; ring
    rw [hsub, (lp_isNorm p).smul_eq, he]
    norm_num
    exact hε2

lemma lp_pairs_compact (p : ℝ≥0∞) [Fact (1 ≤ p)] (ε : ℝ) :
    IsCompact (pairs (lpNorm p) ε) := by
  have hN := continuous_lpNorm p
  have hclosed : IsClosed (pairs (lpNorm p) ε) :=
    (isClosed_eq (hN.comp continuous_fst) continuous_const).inter
      ((isClosed_eq (hN.comp continuous_snd) continuous_const).inter
        (isClosed_le continuous_const (hN.comp (continuous_fst.sub continuous_snd))))
  apply (isCompact_closedBall (0 : E × E) 1).of_isClosed_subset hclosed
  intro z hz
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro i
    exact (PiLp.norm_apply_le (lpVector p z.1) i).trans_eq hz.1
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro i
    exact (PiLp.norm_apply_le (lpVector p z.2) i).trans_eq hz.2.1

theorem lp_modulus_pos (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 2) : 0 < modulus (lpNorm p) ε := by
  have hc : Continuous (defect (lpNorm p)) :=
    continuous_const.sub ((continuous_lpNorm p).comp
      ((continuous_fst.add continuous_snd).const_smul (1 / 2 : ℝ)))
  obtain ⟨z, hz, hmin⟩ := (lp_pairs_compact p ε).exists_isMinOn
    (lp_pair_nonempty p (by linarith : 0 < p.toReal) hε2) hc.continuousOn
  have hne : z.1 ≠ z.2 := by
    intro h
    have hd := hz.2.2
    rw [h, sub_self, (lp_isNorm p).eq_zero 0 |>.mpr rfl] at hd
    linarith
  have hd : 0 < defect (lpNorm p) z := by
    exact sub_pos.mpr (lp_mid_lt p hp hz.1 hz.2.1 hne)
  have hle : defect (lpNorm p) z ≤ modulus (lpNorm p) ε := by
    apply le_csInf (lp_pair_nonempty p (by linarith : 0 < p.toReal) hε2 |>.image _)
    rintro _ ⟨w, hw, rfl⟩
    exact hmin hw
  exact hd.trans_le hle

theorem no_finite_lp_minimizer (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 2) : modulus (lpNorm p) ε ≠ envelope ε := by
  rw [envelope_zero hε.le hε2]
  exact (lp_modulus_pos p hp hε hε2).ne'

/-- Even arbitrary pointwise selection of exponents cannot have the claimed small-epsilon limit. -/
theorem no_selector_tending_two (p : ℝ → ℝ≥0∞) (hP : ∀ ε, 0 < ε → 1 ≤ p ε)
    (ht : Tendsto (fun ε => (p ε).toReal) (𝓝[>] 0) (𝓝 2)) :
    ¬ (∀ ε (hε : 0 < ε), ε < 2 →
      letI : Fact (1 ≤ p ε) := ⟨hP ε hε⟩
      modulus (lpNorm (p ε)) ε = envelope ε) := by
  intro ha
  have hq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 < (p ε).toReal :=
    ht.eventually (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have he0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have he2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hqε, hε, hε2⟩ := (hq.and (he0.and he2)).exists
  letI : Fact (1 ≤ p ε) := ⟨hP ε hε⟩
  exact no_finite_lp_minimizer (p ε) hqε hε hε2.le (ha ε hε hε2)

/-- A checked bridge from the infimum proof to the standard Mathlib uniform-convexity class. -/
theorem lp_uniformConvex (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal) :
    UniformConvexSpace (PiLp p (fun _ : Fin 2 => ℝ)) := by
  refine ⟨fun {ε} hε => ?_⟩
  by_cases hε2 : ε ≤ 2
  · refine ⟨2 * modulus (lpNorm p) ε, mul_pos (by norm_num) (lp_modulus_pos p hp hε hε2), ?_⟩
    intro x hx y hy hxy
    let z : E × E := (WithLp.equiv p E x, WithLp.equiv p E y)
    have hz : z ∈ pairs (lpNorm p) ε := by
      exact ⟨hx, hy, hxy⟩
    have hb : BddBelow (defect (lpNorm p) '' pairs (lpNorm p) ε) :=
      ⟨0, by rintro _ ⟨w, hw, rfl⟩; exact defect_nonneg (lp_isNorm p) hw⟩
    have hm : modulus (lpNorm p) ε ≤ defect (lpNorm p) z := csInf_le hb ⟨z, hz, rfl⟩
    have hd : defect (lpNorm p) z = 1 - ‖x + y‖ / 2 := by
      change 1 - ‖(1 / 2 : ℝ) • (x+y)‖ = 1 - ‖x+y‖ / 2
      rw [norm_smul]
      norm_num
      ring
    rw [hd] at hm
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx y hy hxy
    have hd := norm_sub_le x y
    rw [hx, hy] at hd
    exact False.elim (hε2 (by linarith))

/-- A test pair gives only an upper bound; it is never used as an exact-modulus formula. -/
lemma lp_trial_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) {ε : ℝ}
    (hε : ε ≤ 2 * ((2 : ℝ) ^ (1 / p.toReal))⁻¹) :
    modulus (lpNorm p) ε ≤ 1 - ((2 : ℝ) ^ (1 / p.toReal))⁻¹ := by
  let k : ℝ := (2 : ℝ) ^ (1 / p.toReal)
  have hk : 0 < k := Real.rpow_pos_of_pos (by norm_num) _
  let a : E := ![1,1]
  let b : E := ![1,-1]
  let e : E := ![1,0]
  let f : E := ![0,1]
  have hNa : lpNorm p a = k := by
    rw [lpNorm, PiLp.norm_eq_sum hp]
    norm_num [a, k, Fin.sum_univ_two]
  have hNb : lpNorm p b = k := by
    rw [lpNorm, PiLp.norm_eq_sum hp]
    norm_num [b, k, Fin.sum_univ_two]
  have hNe : lpNorm p e = 1 := by
    rw [lpNorm, PiLp.norm_eq_sum hp]
    simp [e, Fin.sum_univ_two, Real.zero_rpow hp.ne']
  have hNf : lpNorm p f = 1 := by
    rw [lpNorm, PiLp.norm_eq_sum hp]
    simp [f, Fin.sum_univ_two, Real.zero_rpow hp.ne']
  let x := k⁻¹ • a
  let y := k⁻¹ • b
  have hx : lpNorm p x = 1 := by
    rw [(lp_isNorm p).smul_eq, abs_of_pos (inv_pos.mpr hk), hNa, inv_mul_cancel₀ hk.ne']
  have hy : lpNorm p y = 1 := by
    rw [(lp_isNorm p).smul_eq, abs_of_pos (inv_pos.mpr hk), hNb, inv_mul_cancel₀ hk.ne']
  have hdvec : x - y = (2 * k⁻¹) • f := by
    ext i; fin_cases i <;> simp [x, y, a, b, f]; ring
  have hmvec : (1 / 2 : ℝ) • (x + y) = k⁻¹ • e := by
    ext i; fin_cases i <;> simp [x, y, a, b, e]; ring
  have hz : (x,y) ∈ pairs (lpNorm p) ε := by
    refine ⟨hx, hy, ?_⟩
    rw [hdvec, (lp_isNorm p).smul_eq, hNf, mul_one, abs_of_pos (by positivity)]
    exact hε
  have hd : defect (lpNorm p) (x,y) = 1 - k⁻¹ := by
    rw [defect, hmvec, (lp_isNorm p).smul_eq, hNe, mul_one, abs_of_pos (inv_pos.mpr hk)]
  have hb : BddBelow (defect (lpNorm p) '' pairs (lpNorm p) ε) :=
    ⟨0, by rintro _ ⟨w, hw, rfl⟩; exact defect_nonneg (lp_isNorm p) hw⟩
  exact (csInf_le hb ⟨(x,y), hz, rfl⟩).trans_eq hd

/-- The lower envelope stays zero if only uniformly convex norms are allowed. -/
theorem arbitrarily_small_uniformly_convex_lp {ε η : ℝ}
    (hε : 0 < ε) (hε2 : ε < 2) (hη : 0 < η) :
    ∃ q : ℝ, ∃ hq : 2 ≤ q,
      letI : Fact (1 ≤ ENNReal.ofReal q) :=
        ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
      UniformConvexSpace (PiLp (ENNReal.ofReal q) (fun _ : Fin 2 => ℝ)) ∧
        0 < modulus (lpNorm (ENNReal.ofReal q)) ε ∧
        modulus (lpNorm (ENNReal.ofReal q)) ε < η := by
  have hk : Tendsto (fun q : ℝ => (2 : ℝ) ^ (1 / q)) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero, one_div] using
      (tendsto_const_nhds.rpow tendsto_inv_atTop_zero (Or.inl (by norm_num : (2 : ℝ) ≠ 0)))
  have hr : Tendsto (fun q : ℝ => ((2 : ℝ) ^ (1 / q))⁻¹) atTop (𝓝 1) := by
    simpa using hk.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have he : ∀ᶠ q : ℝ in atTop, ε / 2 < ((2 : ℝ) ^ (1 / q))⁻¹ :=
    hr.eventually (eventually_gt_nhds (by linarith : ε / 2 < 1))
  have hη' : ∀ᶠ q : ℝ in atTop, 1 - η < ((2 : ℝ) ^ (1 / q))⁻¹ :=
    hr.eventually (eventually_gt_nhds (by linarith : 1 - η < 1))
  obtain ⟨q, hq, heq, hηq⟩ := ((eventually_ge_atTop (2 : ℝ)).and (he.and hη')).exists
  refine ⟨q, hq, ?_⟩
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have hq0 : 0 ≤ q := by linarith
  have hp : 1 < (ENNReal.ofReal q).toReal := by rw [ENNReal.toReal_ofReal hq0]; linarith
  refine ⟨lp_uniformConvex _ hp, lp_modulus_pos _ hp hε hε2.le, ?_⟩
  have hbound := lp_trial_bound (ENNReal.ofReal q) (by linarith : 0 < (ENNReal.ofReal q).toReal)
    (ε := ε) (by rw [ENNReal.toReal_ofReal hq0]; linarith)
  rw [ENNReal.toReal_ofReal hq0] at hbound
  exact hbound.trans_lt (by linarith)

#print axioms infinity_modulus_zero
#print axioms envelope_zero
#print axioms pairs_nonempty
#print axioms lp_modulus_pos
#print axioms no_finite_lp_minimizer
#print axioms no_selector_tending_two
#print axioms lp_uniformConvex
#print axioms arbitrarily_small_uniformly_convex_lp

end Conjecture947
