import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal BigOperators Classical
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

namespace Conjecture5501

def up (ρ : ℝ) := ρ/(1+ρ)
def down (ρ : ℝ) := 1/(1+ρ)

lemma weights {ρ : ℝ} (hρ : 0<ρ) : 0<up ρ ∧ 0<down ρ ∧ up ρ+down ρ=1 := by
  refine ⟨div_pos hρ (by linarith), div_pos (by norm_num) (by linarith), ?_⟩
  unfold up down
  rw [← add_div]
  rw [add_comm ρ 1]
  exact div_self (by linarith)

def clockCoin (ρ : ℝ) (hρ : 0<ρ) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (if b then up ρ else down ρ)) (by
    rw [Fintype.sum_bool]
    change ENNReal.ofReal (up ρ) + ENNReal.ofReal (down ρ) = 1
    rw [← ENNReal.ofReal_add (weights hρ).1.le (weights hρ).2.1.le,
      (weights hρ).2.2, ENNReal.ofReal_one])

/-- Uniformized M/M/1 transition: an arrival raises the queue; a service lowers
it when nonempty and leaves zero unchanged. -/
def tick (ρ : ℝ) (hρ : 0<ρ) (n : ℕ) : PMF ℕ :=
  (clockCoin ρ hρ).map (fun b => if b then n+1 else n-1)

def T (ρ : ℝ) (n m : ℕ) : ℝ :=
  (if m=n+1 then up ρ else 0) + (if m=n-1 then down ρ else 0)

lemma T_nonneg {ρ : ℝ} (hρ : 0<ρ) (n m : ℕ) : 0≤T ρ n m := by
  unfold T
  split_ifs <;> linarith [(weights hρ).1, (weights hρ).2.1]

lemma tick_mass {ρ : ℝ} (hρ : 0<ρ) (n m : ℕ) :
    tick ρ hρ n m = ENNReal.ofReal (T ρ n m) := by
  rw [tick, PMF.map_apply, tsum_bool]
  simp only [Bool.false_eq_true, Bool.true_eq_false, if_true, if_false]
  change (if m=n-1 then ENNReal.ofReal (down ρ) else 0) +
    (if m=n+1 then ENNReal.ofReal (up ρ) else 0) = ENNReal.ofReal (T ρ n m)
  unfold T
  rw [ENNReal.ofReal_add (by split_ifs <;> linarith [(weights hρ).1])
    (by split_ifs <;> linarith [(weights hρ).2.1])]
  split_ifs <;> simp [add_comm]

def piMass (ρ : ℝ) (n : ℕ) : ℝ := (1-ρ)*ρ^n

def stationary (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1) : PMF ℕ :=
  geometricPMF (p := 1-ρ) (by linarith) (by linarith)

lemma stationary_mass {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) (n : ℕ) :
    stationary ρ hρ hρ1 n = ENNReal.ofReal (piMass ρ n) := by
  change ENNReal.ofReal (((1-(1-ρ))^n)*(1-ρ)) = ENNReal.ofReal (piMass ρ n)
  rw [sub_sub_cancel]
  congr 1
  unfold piMass
  ring

lemma piMass_nonneg {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) (n : ℕ) : 0≤piMass ρ n := by
  unfold piMass
  exact mul_nonneg (sub_nonneg.mpr hρ1.le) (pow_nonneg hρ.le n)

lemma T_up (ρ : ℝ) (n : ℕ) : T ρ n (n+1)=up ρ := by
  have hn : n+1≠n-1 := by omega
  simp [T, hn]

lemma T_down (ρ : ℝ) (n : ℕ) : T ρ (n+1) n=down ρ := by
  have hn : n≠n+1+1 := by omega
  simp [T, hn]

lemma real_detailed_balance (ρ : ℝ) (n m : ℕ) :
    piMass ρ n * T ρ n m = piMass ρ m * T ρ m n := by
  have hadj : ∀ k, piMass ρ k * T ρ k (k+1) = piMass ρ (k+1) * T ρ (k+1) k := by
    intro k
    rw [T_up, T_down]
    unfold piMass up down
    rw [pow_succ]
    ring
  by_cases hm : m=n+1
  · subst m; exact hadj n
  by_cases hn : n=m+1
  · subst n; exact (hadj m).symm
  by_cases he : n=m
  · subst n; rfl
  have hmn : m≠n-1 := by omega
  have hnm : n≠m-1 := by omega
  simp [T, hm, hn, hmn, hnm]

theorem detailed_balance {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) (n m : ℕ) :
    stationary ρ hρ hρ1 n * tick ρ hρ n m =
      stationary ρ hρ hρ1 m * tick ρ hρ m n := by
  rw [stationary_mass hρ hρ1, stationary_mass hρ hρ1, tick_mass hρ, tick_mass hρ,
    ← ENNReal.ofReal_mul (piMass_nonneg hρ hρ1 n),
    ← ENNReal.ofReal_mul (piMass_nonneg hρ hρ1 m), real_detailed_balance]

theorem stationary_tick {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) :
    (stationary ρ hρ hρ1).bind (tick ρ hρ) = stationary ρ hρ hρ1 := by
  ext m
  rw [PMF.bind_apply]
  simp_rw [detailed_balance hρ hρ1]
  rw [ENNReal.tsum_mul_left, (tick ρ hρ m).tsum_coe, mul_one]

def advance (ρ : ℝ) (hρ : 0<ρ) : ℕ → PMF ℕ → PMF ℕ
  | 0, ν => ν
  | k+1, ν => (advance ρ hρ k ν).bind (tick ρ hρ)

lemma stationary_advance {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) (k : ℕ) :
    advance ρ hρ k (stationary ρ hρ hρ1) = stationary ρ hρ hρ1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [advance, ih, stationary_tick hρ hρ1]

/-- Actual Poisson uniformization at clock rate 1+rho; this is the M/M/1 queue law. -/
def queueLaw (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1) (t : ℝ≥0) : PMF ℕ :=
  (poissonPMF ⟨(1+ρ)*t, by positivity⟩).bind
    (fun k => advance ρ hρ k (stationary ρ hρ hρ1))

theorem queueLaw_stationary {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) (t : ℝ≥0) :
    queueLaw ρ hρ hρ1 t = stationary ρ hρ hρ1 := by
  simp only [queueLaw, stationary_advance hρ hρ1, PMF.bind_const]

/-- The actual generator obtained from uniformization. -/
def Q (ρ : ℝ) (n m : ℕ) : ℝ := (1+ρ) * (T ρ n m - if n=m then 1 else 0)

theorem generator_arrival {ρ : ℝ} (hρ : 0<ρ) (n : ℕ) : Q ρ n (n+1)=ρ := by
  have hn : n≠n+1 := by omega
  rw [Q, T_up, if_neg hn, sub_zero]
  unfold up
  exact mul_div_cancel₀ _ (by linarith)

theorem generator_service {ρ : ℝ} (hρ : 0<ρ) (n : ℕ) : Q ρ (n+1) n=1 := by
  have hn : n+1≠n := by omega
  rw [Q, T_down, if_neg hn, sub_zero]
  unfold down
  exact mul_div_cancel₀ _ (by linarith)

theorem generator_empty {ρ : ℝ} (hρ : 0<ρ) : Q ρ 0 0 = -ρ := by
  simp [Q, T, down]
  have hd : 1+ρ≠0 := by linarith
  field_simp [hd]
  ring

theorem generator_busy (ρ : ℝ) (n : ℕ) : Q ρ (n+1) (n+1) = -(1+ρ) := by
  have hu : n+1≠n+1+1 := by omega
  have hd : n+1≠n+1-1 := by omega
  simp [Q, T, hu, hd]

theorem generator_other (ρ : ℝ) (n m : ℕ) (he : m≠n)
    (hu : m≠n+1) (hd : m≠n-1) : Q ρ n m=0 := by
  simp [Q, T, hu, hd, Ne.symm he]

lemma weighted_sum {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) :
    HasSum (fun n : ℕ => (n:ℝ)*piMass ρ n) (ρ/(1-ρ)) := by
  have hn : ‖ρ‖<1 := by simpa [Real.norm_eq_abs, abs_of_pos hρ] using hρ1
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left (1-ρ)
  convert hs using 1
  · ext n; unfold piMass; ring
  · have hd : 1-ρ≠0 := by linarith
    field_simp [hd]
    ring

/-- Expected queue length as a genuine nonnegative Lebesgue integral. -/
def mean (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1) : ℝ≥0∞ :=
  ∫⁻ n : ℕ, (n:ℝ≥0∞) ∂(stationary ρ hρ hρ1).toMeasure

theorem mean_eq {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) :
    mean ρ hρ hρ1 = ENNReal.ofReal (ρ/(1-ρ)) := by
  rw [mean, lintegral_countable']
  simp only [PMF.toMeasure_apply_singleton, measurableSet_singleton, stationary_mass hρ hρ1]
  have hw := weighted_sum hρ hρ1
  rw [← hw.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (Nat.cast_nonneg n) (piMass_nonneg hρ hρ1 n)) hw.summable]
  congr 1
  ext n
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  simp

theorem deficit_times_mean {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) :
    (1-ρ)*(mean ρ hρ hρ1).toReal=ρ := by
  rw [mean_eq, ENNReal.toReal_ofReal (div_nonneg hρ.le (by linarith))]
  exact mul_div_cancel₀ _ (by linarith)

lemma atom_bound {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) (n : ℕ) :
    piMass ρ n ≤ 1-ρ := by
  unfold piMass
  simpa using mul_le_mul_of_nonneg_left
    (pow_le_one₀ hρ.le hρ1.le) (sub_nonneg.mpr hρ1.le)

/-- Probability of a finite queue-length cutoff, for the actual stationary law. -/
def cdf (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1) (K : ℕ) : ℝ :=
  ((stationary ρ hρ hρ1).toMeasure (Finset.range (K+1) : Set ℕ)).toReal

lemma cdf_eq_sum {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) (K : ℕ) :
    cdf ρ hρ hρ1 K = ∑ n ∈ Finset.range (K+1), piMass ρ n := by
  rw [cdf, PMF.toMeasure_apply_finset]
  simp only [stationary_mass hρ hρ1]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => piMass_nonneg hρ hρ1 n),
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun n _ => piMass_nonneg hρ hρ1 n))]

theorem cdf_bound {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) (K : ℕ) :
    0 ≤ cdf ρ hρ hρ1 K ∧ cdf ρ hρ hρ1 K ≤ (K+1:ℕ)*(1-ρ) := by
  rw [cdf_eq_sum]
  refine ⟨Finset.sum_nonneg (fun n _ => piMass_nonneg hρ hρ1 n), ?_⟩
  calc
    _ ≤ ∑ _n ∈ Finset.range (K+1), (1-ρ) :=
      Finset.sum_le_sum (fun n _ => atom_bound hρ hρ1 n)
    _ = _ := by simp; ring

def a (k : ℕ) : ℝ := k+2
def load (k : ℕ) : ℝ := 1-(a k)⁻¹^2

lemma a_pos (k : ℕ) : 0<a k := by unfold a; positivity
lemma a_ge_two (k : ℕ) : 2≤a k := by unfold a; linarith [show (0:ℝ)≤k from Nat.cast_nonneg k]
lemma inv_a (k : ℕ) : 0<(a k)⁻¹ ∧ (a k)⁻¹<1 := by
  exact ⟨inv_pos.mpr (a_pos k), (inv_lt_one₀ (a_pos k)).mpr (by linarith [a_ge_two k])⟩

lemma load_mem (k : ℕ) : 0<load k ∧ load k<1 := by
  have hi := inv_a k
  unfold load
  constructor <;> nlinarith [sq_pos_of_pos hi.1]

lemma deficit (k : ℕ) : 1-load k=(a k)⁻¹^2 := by unfold load; ring

lemma sqrt_deficit (k : ℕ) : Real.sqrt (1-load k)=(a k)⁻¹ := by
  rw [deficit, Real.sqrt_sq_eq_abs, abs_of_pos (inv_a k).1]

lemma a_tendsto : Tendsto a atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hc : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hc.eventually (eventually_ge_atTop b)] with k hk
  unfold a
  linarith

theorem load_tendsto : Tendsto load atTop (𝓝 1) := by
  have hi : Tendsto (fun k => (a k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp a_tendsto
  change Tendsto (fun k => 1-(a k)⁻¹^2) atTop (𝓝 1)
  simpa only [zero_pow (by norm_num : 2≠0), sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub (hi.pow 2)

/-- On this heavy-traffic sequence the actual normalized mean tends to infinity. -/
theorem normalized_mean_eq (k : ℕ) :
    Real.sqrt (1-load k) * (mean (load k) (load_mem k).1 (load_mem k).2).toReal =
      a k-(a k)⁻¹ := by
  rw [sqrt_deficit, mean_eq, ENNReal.toReal_ofReal
    (div_nonneg (load_mem k).1.le (by linarith [(load_mem k).2]))]
  rw [deficit]
  unfold load
  have ha : a k≠0 := ne_of_gt (a_pos k)
  field_simp [ha]
  ring

theorem normalized_mean_tendsto :
    Tendsto (fun k => Real.sqrt (1-load k) *
      (mean (load k) (load_mem k).1 (load_mem k).2).toReal) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [a_tendsto.eventually (eventually_ge_atTop (b+1))] with k hk
  rw [normalized_mean_eq]
  linarith [(inv_a k).2]

lemma scaled_cdf_bound (M k : ℕ) :
    cdf (load k) (load_mem k).1 (load_mem k).2 (M*(k+2)) ≤ (M+1:ℝ)/(a k) := by
  have hc := (cdf_bound (load_mem k).1 (load_mem k).2 (M*(k+2))).2
  rw [deficit] at hc
  have ha : a k≠0 := ne_of_gt (a_pos k)
  apply hc.trans
  have h : (M:ℝ)*a k+1 ≤ ((M:ℝ)+1)*a k := by nlinarith [a_ge_two k]
  have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg ((a k)⁻¹))
  convert hmul using 1
  · simp [a, Nat.cast_add, Nat.cast_mul]
  · field_simp [ha]
    ring

/-- Every fixed multiple of the proposed deficit^(-1/2) scale captures
asymptotically zero stationary probability. -/
theorem proposed_scale_not_tight (M : ℕ) :
    Tendsto (fun k => cdf (load k) (load_mem k).1 (load_mem k).2 (M*(k+2)))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun k => (a k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp a_tendsto
  have hb : Tendsto (fun k => (M+1:ℝ)/(a k)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hi.const_mul (M+1:ℝ)
  exact squeeze_zero
    (fun k => (cdf_bound (load_mem k).1 (load_mem k).2 (M*(k+2))).1)
    (scaled_cdf_bound M) hb

/-- Queue length excluding the customer currently being served. -/
def waiting (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1) : PMF ℕ :=
  (stationary ρ hρ hρ1).map (fun n => n-1)

def waitingCDF (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1) (K : ℕ) : ℝ :=
  ((waiting ρ hρ hρ1).toMeasure (Finset.range (K+1) : Set ℕ)).toReal

lemma waitingCDF_eq {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) (K : ℕ) :
    waitingCDF ρ hρ hρ1 K = cdf ρ hρ hρ1 (K+1) := by
  unfold waitingCDF waiting cdf
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) (Finset.measurableSet _)]
  congr 2
  ext n
  simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_range]
  omega

lemma waiting_scaled_bound (M k : ℕ) :
    0≤waitingCDF (load k) (load_mem k).1 (load_mem k).2 (M*(k+2)) ∧
    waitingCDF (load k) (load_mem k).1 (load_mem k).2 (M*(k+2)) ≤ (M+2:ℝ)/(a k) := by
  rw [waitingCDF_eq]
  have hc := cdf_bound (load_mem k).1 (load_mem k).2 (M*(k+2)+1)
  refine ⟨hc.1, hc.2.trans ?_⟩
  rw [deficit]
  have ha : a k≠0 := ne_of_gt (a_pos k)
  have h : (M:ℝ)*a k+2 ≤ ((M:ℝ)+2)*a k := by nlinarith [a_ge_two k]
  have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg ((a k)⁻¹))
  convert hmul using 1
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    congr 1
    unfold a
    ring
  · field_simp [ha]
    ring

theorem waiting_proposed_scale_not_tight (M : ℕ) :
    Tendsto (fun k => waitingCDF (load k) (load_mem k).1 (load_mem k).2 (M*(k+2)))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun k => (a k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp a_tendsto
  have hb : Tendsto (fun k => (M+2:ℝ)/(a k)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hi.const_mul (M+2:ℝ)
  exact squeeze_zero (fun k => (waiting_scaled_bound M k).1)
    (fun k => (waiting_scaled_bound M k).2) hb

theorem no_fixed_scaled_half_mass (M : ℕ) :
    ¬ ∀ᶠ k in atTop,
      (1/2:ℝ)≤cdf (load k) (load_mem k).1 (load_mem k).2 (M*(k+2)) := by
  intro h
  have hl := (proposed_scale_not_tight M).eventually
    (eventually_lt_nhds (show (0:ℝ)<1/2 by norm_num))
  obtain ⟨k, hk, hk'⟩ := (h.and hl).exists
  linarith

theorem no_fixed_waiting_scaled_half_mass (M : ℕ) :
    ¬ ∀ᶠ k in atTop,
      (1/2:ℝ)≤waitingCDF (load k) (load_mem k).1 (load_mem k).2 (M*(k+2)) := by
  intro h
  have hl := (waiting_proposed_scale_not_tight M).eventually
    (eventually_lt_nhds (show (0:ℝ)<1/2 by norm_num))
  obtain ⟨k, hk, hk'⟩ := (h.and hl).exists
  linarith

#print axioms detailed_balance
#print axioms stationary_tick
#print axioms queueLaw_stationary
#print axioms generator_arrival
#print axioms generator_service
#print axioms generator_empty
#print axioms generator_busy
#print axioms generator_other
#print axioms mean_eq
#print axioms deficit_times_mean
#print axioms cdf_bound
#print axioms load_tendsto
#print axioms sqrt_deficit
#print axioms normalized_mean_tendsto
#print axioms proposed_scale_not_tight
#print axioms waiting_proposed_scale_not_tight
#print axioms no_fixed_scaled_half_mass
#print axioms no_fixed_waiting_scaled_half_mass

end Conjecture5501

