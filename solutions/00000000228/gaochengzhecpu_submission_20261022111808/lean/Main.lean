import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal BigOperators Classical
set_option maxHeartbeats 1500000
set_option maxRecDepth 2000

namespace Conjecture228

def step (b : Bool) (v : ℕ×ℕ) : ℕ×ℕ :=
  if b then (v.1,v.1+v.2) else (v.1+v.2,v.2)

/-- Simultaneous construction of Stern's adjacent pair. -/
def pair (n : ℕ) : ℕ×ℕ :=
  if n=0 then (0,1) else step (decide (n%2=0)) (pair (n/2))
termination_by n
decreasing_by
  exact Nat.div_lt_self (by omega) (by norm_num)

def stern (n : ℕ) : ℕ := (pair n).1

lemma pair_zero : pair 0=(0,1) := by rw [pair]; simp

lemma pair_step (n : ℕ) : pair n=step (decide (n%2=0)) (pair (n/2)) := by
  by_cases hn : n=0
  · subst n; simp [pair_zero, step]
  · rw [pair, if_neg hn]

lemma pair_even (n : ℕ) : pair (2*n)=((pair n).1,(pair n).1+(pair n).2) := by
  rw [pair_step]
  simp [step]

lemma pair_odd (n : ℕ) : pair (2*n+1)=((pair n).1+(pair n).2,(pair n).2) := by
  rw [pair_step]
  have hd : (2*n+1)/2=n := by omega
  simp [step, hd]

lemma pair_second (n : ℕ) : (pair n).2=stern (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hd : n=2*(n/2)+n%2 := by omega
    have hr : n%2=0 ∨ n%2=1 := by omega
    rcases hr with he|ho
    · have hn : n=2*(n/2) := by omega
      rw [hn, pair_even]
      unfold stern
      rw [pair_odd]
    · have hn : n=2*(n/2)+1 := by omega
      rw [hn, pair_odd]
      have hnext : 2*(n/2)+1+1=2*(n/2+1) := by omega
      unfold stern
      rw [hnext, pair_even]
      exact ih (n/2) (by omega)

theorem stern_zero : stern 0=0 := by simp [stern, pair_zero]
theorem stern_one : stern 1=1 := by
  have he := pair_odd 0
  simpa [stern, pair_zero] using congrArg Prod.fst he

theorem stern_even (n : ℕ) : stern (2*n)=stern n := by simp [stern, pair_even]
theorem stern_odd (n : ℕ) : stern (2*n+1)=stern n+stern (n+1) := by
  simp only [stern, pair_odd, Prod.fst]
  rw [pair_second]
  rfl

lemma triple_step_bound (B : ℕ) (v : ℕ×ℕ) (h1 : v.1≤B) (h2 : v.2≤B)
    (a b c : Bool) :
    (step a (step b (step c v))).1≤5*B ∧ (step a (step b (step c v))).2≤5*B := by
  cases a <;> cases b <;> cases c <;> simp only [step, Bool.false_eq_true, if_false, if_true]
  all_goals constructor <;> omega

lemma pair_three (n : ℕ) : pair n=
    step (decide (n%2=0)) (step (decide ((n/2)%2=0))
      (step (decide ((n/4)%2=0)) (pair (n/8)))) := by
  nth_rw 1 [pair_step n]
  nth_rw 1 [pair_step (n/2)]
  nth_rw 1 [pair_step (n/2/2)]
  simp only [Nat.div_div_eq_div_mul]

theorem pair_power_bound (m n : ℕ) (hn : n≤8^m) :
    (pair n).1≤5^m ∧ (pair n).2≤5^m := by
  induction m generalizing n with
  | zero =>
    norm_num at hn
    interval_cases n
    · norm_num [pair_zero]
    · have he := pair_odd 0
      norm_num [pair_zero] at he
      rw [he]
      norm_num
  | succ m ih =>
    have hdiv : n/8≤8^m := by
      rw [pow_succ] at hn
      omega
    have hb := ih (n/8) hdiv
    rw [pair_three]
    simpa only [pow_succ, Nat.mul_comm] using
      triple_step_bound (5^m) (pair (n/8)) hb.1 hb.2
        (decide (n%2=0)) (decide ((n/2)%2=0)) (decide ((n/4)%2=0))

theorem square_numerator_bound (m n : ℕ) (hn : n≤8^(m+1)) :
    stern (n^2)≤25^(m+1) := by
  have hs : n^2≤8^(2*(m+1)) := by
    calc
      _ ≤ (8^(m+1))^2 := Nat.pow_le_pow_left hn 2
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hb := (pair_power_bound (2*(m+1)) (n^2) hs).1
  change (pair (n^2)).1≤_
  convert hb using 1
  rw [pow_mul]
  norm_num

theorem stern_unique (f : ℕ→ℕ) (h0 : f 0=0) (h1 : f 1=1)
    (he : ∀ n, f (2*n)=f n) (ho : ∀ n, f (2*n+1)=f n+f (n+1)) : f=stern := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n=0
    · subst n; rw [h0, stern_zero]
    by_cases hn1 : n=1
    · subst n; rw [h1, stern_one]
    have hq : n/2<n := Nat.div_lt_self (by omega) (by norm_num)
    have hr : n%2=0 ∨ n%2=1 := by omega
    rcases hr with hmod|hmod
    · have hn : n=2*(n/2) := by omega
      calc
        f n = f (n/2) := by nth_rw 1 [hn]; rw [he]
        _ = stern (n/2) := ih _ hq
        _ = stern n := by nth_rw 2 [hn]; rw [stern_even]
    · have hn : n=2*(n/2)+1 := by omega
      calc
        f n = f (n/2)+f (n/2+1) := by nth_rw 1 [hn]; rw [ho]
        _ = stern (n/2)+stern (n/2+1) := by rw [ih _ hq, ih (n/2+1) (by omega)]
        _ = stern n := (stern_odd (n/2)).symm.trans (congrArg stern hn.symm)

lemma pair_second_pos (n : ℕ) : 0<(pair n).2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n; norm_num [pair_zero]
    · have hi := ih (n/2) (Nat.div_lt_self (by omega) (by norm_num))
      rw [pair_step]
      unfold step
      split_ifs <;> dsimp <;> omega

theorem stern_pos {n : ℕ} (hn : 0<n) : 0<stern n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hr : n%2=0 ∨ n%2=1 := by omega
    rcases hr with hmod|hmod
    · have he : n=2*(n/2) := by omega
      have hp : 0<n/2 := by omega
      have hi := ih (n/2) (Nat.div_lt_self hn (by norm_num)) hp
      calc
        0 < stern (n/2) := hi
        _ = stern n := by nth_rw 2 [he]; rw [stern_even]
    · have ho : n=2*(n/2)+1 := by omega
      unfold stern
      rw [ho, pair_odd]
      have hp := pair_second_pos (n/2)
      dsimp
      omega

def denominator (n : ℕ) : ℝ := (3:ℝ)^(Real.log n/Real.log 2)
def normalized (n : ℕ) : ℝ := (stern (n^2):ℝ)/denominator n

lemma denominator_pos (n : ℕ) : 0<denominator n := Real.rpow_pos_of_pos (by norm_num) _
lemma normalized_nonneg (n : ℕ) : 0≤normalized n :=
  div_nonneg (Nat.cast_nonneg _) (denominator_pos n).le
lemma normalized_pos {n : ℕ} (hn : 0<n) : 0<normalized n := by
  apply div_pos _ (denominator_pos n)
  exact_mod_cast stern_pos (Nat.pow_pos hn)

lemma log_eight : Real.log 8=3*Real.log 2 := by
  have he := Real.log_pow (2:ℝ) 3
  norm_num at he
  exact he

lemma denominator_lower (m n : ℕ) (hn : 8^m≤n) : (27:ℝ)^m≤denominator n := by
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hcast : (8:ℝ)^m≤n := by exact_mod_cast hn
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<8^m) hcast
  rw [Real.log_pow, log_eight] at hlog
  have he : (3*m:ℝ)≤Real.log n/Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    nlinarith
  unfold denominator
  calc
    (27:ℝ)^m = (3:ℝ)^(3*m:ℕ) := by rw [pow_mul]; norm_num
    _ = (3:ℝ)^((3:ℝ)*m) := by rw [← Real.rpow_natCast]; norm_cast
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) he

theorem normalized_block_bound (m n : ℕ) (hlo : 8^m≤n) (hhi : n≤8^(m+1)) :
    normalized n≤25*(25/27:ℝ)^m := by
  have ha : (stern (n^2):ℝ)≤(25:ℝ)^(m+1) := by
    exact_mod_cast square_numerator_bound m n hhi
  have hb := denominator_lower m n hlo
  unfold normalized
  calc
    _ ≤ (25:ℝ)^(m+1)/denominator n := div_le_div_of_nonneg_right ha (denominator_pos n).le
    _ ≤ (25:ℝ)^(m+1)/(27:ℝ)^m :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hb
    _ = _ := by rw [div_pow, pow_succ]; ring

lemma nat_log_eight_tendsto : Tendsto (fun n : ℕ => Nat.log 8 n) atTop atTop := by
  apply tendsto_atTop.mpr
  intro m
  filter_upwards [eventually_ge_atTop (8^m)] with n hn
  exact Nat.le_log_of_pow_le (by norm_num) hn

theorem normalized_tendsto_zero : Tendsto normalized atTop (𝓝 0) := by
  have hg : Tendsto (fun m : ℕ => (25/27:ℝ)^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb : Tendsto (fun n : ℕ => 25*(25/27:ℝ)^(Nat.log 8 n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hg.comp nat_log_eight_tendsto).const_mul 25
  apply squeeze_zero' (Eventually.of_forall normalized_nonneg) _ hb
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact normalized_block_bound (Nat.log 8 n) n
    (Nat.pow_log_le_self _ (by omega)) (Nat.lt_pow_succ_log_self (by norm_num) n).le

/-- The true empirical distribution of the first N+1 positive indices. -/
def empiricalPMF (N : ℕ) : PMF ℝ :=
  (PMF.uniformOfFintype (Fin (N+1))).map (fun i => normalized (i.val+1))
def empiricalLaw (N : ℕ) : Measure ℝ := (empiricalPMF N).toMeasure
instance (N : ℕ) : IsProbabilityMeasure (empiricalLaw N) :=
  inferInstanceAs (IsProbabilityMeasure (empiricalPMF N).toMeasure)

def badIndices (N : ℕ) (x : ℝ) : Finset (Fin (N+1)) :=
  Finset.univ.filter (fun i => x<normalized (i.val+1))
def tailProbability (N : ℕ) (x : ℝ) : ℝ := ((empiricalLaw N) (Ioi x)).toReal
def actualCDF (N : ℕ) (x : ℝ) : ℝ := ((empiricalLaw N) (Iic x)).toReal

theorem tail_count_formula (N : ℕ) (x : ℝ) :
    tailProbability N x=(badIndices N x).card/(N+1:ℝ) := by
  unfold tailProbability empiricalLaw empiricalPMF
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) measurableSet_Ioi,
    PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one]
  congr 1
  rw [Fintype.card_subtype]
  rfl

lemma bad_count_bound (K N : ℕ) (x : ℝ)
    (hk : ∀ n≥K, normalized n≤x) : (badIndices N x).card≤K := by
  have hc : (badIndices N x).card≤(Finset.range K).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin (N+1) => i.val)
    · intro i hi
      simp only [badIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hn : i.val+1<K := by
        by_contra hh
        exact not_lt_of_ge (hk _ (by omega)) hi
      exact Finset.mem_range.mpr (by omega)
    · intro i _ j _ hij
      exact Fin.ext hij
  simpa using hc

theorem empirical_tail_zero (x : ℝ) (hx : 0<x) :
    Tendsto (fun N => tailProbability N x) atTop (𝓝 0) := by
  have he := normalized_tendsto_zero.eventually (eventually_lt_nhds hx)
  obtain ⟨K, hK⟩ := eventually_atTop.mp he
  have hs : Tendsto (fun N : ℕ => (N+1:ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    have hc : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hc.eventually (eventually_ge_atTop b)] with N hN
    linarith
  have hb : Tendsto (fun N : ℕ => (K:ℝ)/(N+1:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero.comp hs).const_mul (K:ℝ)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ hb
  intro N
  change tailProbability N x≤(K:ℝ)/(N+1:ℝ)
  rw [tail_count_formula]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast bad_count_bound K N x (fun n hn => (hK n hn).le)

lemma cdf_complement (N : ℕ) (x : ℝ) : actualCDF N x=1-tailProbability N x := by
  have he := measureReal_compl (μ := empiricalLaw N) (s := Ioi x) measurableSet_Ioi
  simpa only [compl_Ioi, measureReal_def, measure_univ, ENNReal.toReal_one] using he

theorem empirical_positive_cdf (x : ℝ) (hx : 0<x) :
    Tendsto (fun N => actualCDF N x) atTop (𝓝 1) := by
  have he := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub
    (empirical_tail_zero x hx)
  simpa only [sub_zero, cdf_complement] using he

theorem empirical_nonpositive_cdf (N : ℕ) (x : ℝ) (hx : x≤0) : actualCDF N x=0 := by
  unfold actualCDF empiricalLaw empiricalPMF
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) measurableSet_Iic]
  have hs : (fun i : Fin (N+1) => normalized (i.val+1)) ⁻¹' Iic x=∅ := by
    ext i
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    have hp : 0<normalized (i.val+1) := normalized_pos (Nat.succ_pos _)
    linarith
  rw [hs, measure_empty, ENNReal.toReal_zero]

theorem actualCDF_eq_cdf (N : ℕ) (x : ℝ) : actualCDF N x=cdf (empiricalLaw N) x := by
  rw [cdf_eq_real]
  rfl

theorem empirical_cdf_dirac_limit (x : ℝ) (hx : x≠0) :
    Tendsto (fun N => actualCDF N x) atTop (𝓝 (cdf (Measure.dirac 0) x)) := by
  rcases lt_or_gt_of_ne hx with hneg|hpos
  · have he : cdf (Measure.dirac 0) x=0 := by
      rw [cdf_eq_real]
      simp [Measure.real, not_le.mpr hneg]
    rw [he]
    simpa only [empirical_nonpositive_cdf _ _ hneg.le] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · have he : cdf (Measure.dirac 0) x=1 := by
      rw [cdf_eq_real]
      simp [Measure.real, hpos.le]
    rw [he]
    exact empirical_positive_cdf x hpos

theorem no_continuous_cdf_limit (F : ℝ→ℝ) (hF : Continuous F) :
    ¬∀ x, Tendsto (fun N => actualCDF N x) atTop (𝓝 (F x)) := by
  intro h
  have hf0 : F 0=0 := by
    have hz : Tendsto (fun N => actualCDF N 0) atTop (𝓝 0) := by
      simpa only [empirical_nonpositive_cdf _ _ le_rfl] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (h 0) hz
  have hpos : ∀ x>0, F x=1 := fun x hx => tendsto_nhds_unique (h x) (empirical_positive_cdf x hx)
  have hi : Tendsto (fun n : ℕ => (1/(n+1:ℝ))) atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      have hc : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      filter_upwards [hc.eventually (eventually_ge_atTop b)] with n hn
      linarith
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hs
  have hl := hF.continuousAt.tendsto.comp hi
  have he : (fun n : ℕ => F (1/(n+1:ℝ)))=(fun _ => (1:ℝ)) := by
    ext n
    exact hpos _ (by positivity)
  change Tendsto (fun n : ℕ => F (1/(n+1:ℝ))) atTop (𝓝 (F 0)) at hl
  rw [he, hf0] at hl
  have hbad : (0:ℝ)=1 := tendsto_nhds_unique hl tendsto_const_nhds
  norm_num at hbad

#print axioms stern_zero
#print axioms stern_one
#print axioms stern_even
#print axioms stern_odd
#print axioms stern_unique
#print axioms stern_pos
#print axioms pair_power_bound
#print axioms square_numerator_bound
#print axioms denominator_lower
#print axioms normalized_block_bound
#print axioms normalized_tendsto_zero
#print axioms tail_count_formula
#print axioms empirical_tail_zero
#print axioms empirical_positive_cdf
#print axioms empirical_nonpositive_cdf
#print axioms actualCDF_eq_cdf
#print axioms empirical_cdf_dirac_limit
#print axioms no_continuous_cdf_limit

end Conjecture228
