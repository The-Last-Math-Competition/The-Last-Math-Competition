import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Semicontinuous
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BigOperators Classical

namespace Conjecture2801

/-- The actual extended logarithm divided by speed n+1; in particular log 0=-infinity. -/
def scaledLog (n : ℕ) (q : ℝ≥0∞) : EReal :=
  if q=0 then ⊥ else if q=⊤ then ⊤ else (Real.log q.toReal / (n+1) : ℝ)

@[simp] lemma scaledLog_zero (n : ℕ) : scaledLog n 0 = ⊥ := by simp [scaledLog]
@[simp] lemma scaledLog_one (n : ℕ) : scaledLog n 1 = 0 := by simp [scaledLog]

/-- Standard open-set lower and closed-set upper bounds for speed n+1. -/
def HasLDP {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : ℕ → Measure X) (I : X → EReal) : Prop :=
  (∀ G : Set X, IsOpen G →
    -(⨅ x ∈ G, I x) ≤ liminf (fun n => scaledLog n (μ n G)) atTop) ∧
  (∀ F : Set X, IsClosed F →
    limsup (fun n => scaledLog n (μ n F)) atTop ≤ -(⨅ x ∈ F, I x))

def pointRate {X : Type*} (a x : X) : EReal := if x=a then 0 else ⊤

lemma pointRate_nonneg {X : Type*} (a x : X) : 0 ≤ pointRate a x := by
  classical
  by_cases x=a <;> simp [pointRate, *]

lemma pointRate_inf {X : Type*} (a : X) (S : Set X) :
    (⨅ x ∈ S, pointRate a x) = if a∈S then (0 : EReal) else ⊤ := by
  classical
  by_cases ha : a∈S
  · rw [if_pos ha]
    apply le_antisymm
    · exact (iInf_le_of_le a (iInf_le_of_le ha le_rfl)).trans_eq (by simp [pointRate])
    · exact le_iInf fun x => le_iInf fun _ => pointRate_nonneg a x
  · rw [if_neg ha]
    apply le_antisymm le_top
    apply le_iInf
    intro x
    apply le_iInf
    intro hx
    have hxa : x≠a := fun h => ha (h ▸ hx)
    simp [pointRate, hxa]

theorem convergent_dirac_ldp {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (z : ℕ → X) (a : X) (hz : Tendsto z atTop (𝓝 a)) :
    HasLDP (fun n => Measure.dirac (z n)) (pointRate a) := by
  classical
  constructor
  · intro G hG
    rw [pointRate_inf]
    by_cases ha : a∈G
    · rw [if_pos ha]
      have he : ∀ᶠ n in atTop, scaledLog n (Measure.dirac (z n) G) = 0 := by
        filter_upwards [hz.eventually (hG.mem_nhds ha)] with n hn
        simp [Measure.dirac_apply_of_mem hn]
      rw [liminf_congr he, liminf_const]
      simp
    · simp [ha]
  · intro F hF
    rw [pointRate_inf]
    by_cases ha : a∈F
    · simp only [ha, if_true, neg_zero]
      apply limsup_le_of_le (by isBoundedDefault)
      apply Eventually.of_forall
      intro n
      by_cases hn : z n∈F <;> simp [Measure.dirac_apply, Set.indicator, hn]
    · rw [if_neg ha, EReal.neg_top]
      have he : ∀ᶠ n in atTop, scaledLog n (Measure.dirac (z n) F) = ⊥ := by
        filter_upwards [hz.eventually (hF.isOpen_compl.mem_nhds ha)] with n hn
        simp [Measure.dirac_apply, Set.indicator, hn]
      rw [limsup_congr he, limsup_const]

theorem pointRate_lowerSemicontinuous {X : Type*} [TopologicalSpace X] [T1Space X]
    (a : X) : LowerSemicontinuous (pointRate a) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : r=⊤
  · subst r
    simp
  by_cases hr0 : 0 ≤ r
  · have he : pointRate a ⁻¹' Iic r = {a} := by
      ext x
      by_cases hx : x=a <;> simp [pointRate, hx, hr0, hr]
    rw [he]
    exact isClosed_singleton
  · have he : pointRate a ⁻¹' Iic r = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun h => hr0 ((pointRate_nonneg a x).trans h)
    rw [he]
    exact isClosed_empty

theorem pointRate_good {X : Type*} [TopologicalSpace X] [T1Space X] (a : X) (r : ℝ) :
    IsCompact {x : X | pointRate a x ≤ (r : EReal)} := by
  classical
  by_cases hr : 0 ≤ r
  · have he : {x : X | pointRate a x ≤ (r : EReal)} = {a} := by
      ext x
      by_cases hx : x=a <;> simp [pointRate, hx, hr]
    rw [he]
    exact isCompact_singleton
  · have he : {x : X | pointRate a x ≤ (r : EReal)} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro h
      have : (0 : EReal) ≤ (r : EReal) := (pointRate_nonneg a x).trans h
      exact hr (by exact_mod_cast this)
    rw [he]
    exact isCompact_empty

def transition (s : Bool) : PMF Bool := PMF.pure (!s)

def P : Matrix Bool Bool ℝ := fun s t => if t = !s then 1 else 0

lemma transition_matrix (s t : Bool) : transition s t = ENNReal.ofReal (P s t) := by
  cases s <;> cases t <;> norm_num [transition, P, PMF.pure_apply]

theorem P_stochastic : (∀ s t, 0 ≤ P s t) ∧ (∀ s, ∑ t, P s t = 1) := by
  constructor
  · intro s t; cases s <;> cases t <;> norm_num [P]
  · intro s; cases s <;> norm_num [P, Fintype.sum_bool]

lemma P_square : P^2 = 1 := by
  ext s t
  cases s <;> cases t <;> norm_num [pow_two, Matrix.mul_apply, P, Fintype.sum_bool]

/-- Standard finite-chain irreducibility: every state reaches every state with positive
probability in a strictly positive number of actual matrix steps. -/
theorem P_irreducible : ∀ s t : Bool, ∃ n : ℕ, 0 < n ∧ 0 < (P^n) s t := by
  intro s t
  by_cases h : s=t
  · refine ⟨2, by norm_num, ?_⟩
    rw [P_square, h]
    simp
  · refine ⟨1, by norm_num, ?_⟩
    cases s <;> cases t <;> simp_all [P]

def state (n : ℕ) : Bool := decide (n % 2 = 1)

@[simp] lemma state_zero : state 0 = false := by decide

lemma state_succ (n : ℕ) : state (n+1) = !(state n) := by
  by_cases h : n%2=0
  · have hs : (n+1)%2=1 := by omega
    simp [state, h, hs]
  · have h' : n%2=1 := by omega
    have hs : (n+1)%2=0 := by omega
    simp [state, h', hs]

/-- The actual probability law on complete sample paths for initial state false. -/
def processLaw : PMF (ℕ → Bool) := PMF.pure state

def cylinder (n : ℕ) (w : ℕ → Bool) : Set (ℕ → Bool) :=
  {ω | ∀ k ≤ n, ω k = w k}

def pathProduct (n : ℕ) (w : ℕ → Bool) : ℝ≥0∞ :=
  (if w 0=false then 1 else 0) * ∏ k ∈ Finset.range n, transition (w k) (w (k+1))

lemma valid_path_unique {n : ℕ} {w : ℕ → Bool} (h0 : w 0=false)
    (hs : ∀ k<n, w (k+1) = !(w k)) : ∀ k≤n, w k = state k := by
  intro k
  induction k with
  | zero => simp [h0]
  | succ k ih =>
      intro hk
      rw [hs k (by omega), ih (by omega), state_succ]

/-- Exact finite-dimensional Markov factorization, including the initial law. -/
theorem process_path_probability (n : ℕ) (w : ℕ → Bool) :
    processLaw.toOuterMeasure (cylinder n w) = pathProduct n w := by
  classical
  rw [processLaw, PMF.toOuterMeasure_pure_apply]
  by_cases h0 : w 0=false
  · by_cases hs : ∀ k<n, w (k+1)=!(w k)
    · have hu := valid_path_unique h0 hs
      have hm : state ∈ cylinder n w := fun k hk => (hu k hk).symm
      rw [if_pos hm]
      simp only [pathProduct, if_pos h0, one_mul]
      symm
      apply Finset.prod_eq_one
      intro k hk
      simp [transition, PMF.pure_apply, hs k (Finset.mem_range.mp hk)]
    · obtain ⟨k, hkn, hk⟩ : ∃ k<n, w (k+1)≠!(w k) := by simpa using hs
      have hn : state ∉ cylinder n w := by
        intro hm
        have h1 := hm k (by omega)
        have h2 := hm (k+1) (by omega)
        exact hk (by rw [← h2, state_succ, h1])
      rw [if_neg hn]
      simp only [pathProduct, if_pos h0, one_mul]
      symm
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hkn)
      simp [transition, PMF.pure_apply, hk]
  · have hn : state ∉ cylinder n w := by
      intro hm
      apply h0
      simpa using (hm 0 (Nat.zero_le n)).symm
    simp [hn, pathProduct, h0]

theorem process_path_measure_probability (n : ℕ) (w : ℕ → Bool) :
    processLaw.toMeasure (cylinder n w) = pathProduct n w := by
  rw [← process_path_probability]
  simp [processLaw, PMF.toMeasure_pure, Measure.dirac_apply,
    PMF.toOuterMeasure_pure_apply, Set.indicator]

def countState (n : ℕ) (s : Bool) : ℕ :=
  ∑ k ∈ Finset.range n, if state k=s then 1 else 0

lemma count_true (n : ℕ) : countState n true = n/2 := by
  induction n with
  | zero => simp [countState]
  | succ n ih =>
      have he : countState (n+1) true = countState n true + if state n=true then 1 else 0 := by
        unfold countState
        rw [Finset.sum_range_succ]
      rw [he, ih]
      by_cases hn : n%2=1 <;> simp [state, hn] <;> omega

lemma count_total (n : ℕ) : countState n false + countState n true = n := by
  rw [countState, countState, ← Finset.sum_add_distrib]
  have he : ∀ k : ℕ, (if state k=false then 1 else 0) +
      (if state k=true then 1 else 0) = (1 : ℕ) := by intro k; cases state k <;> simp
  simp_rw [he]
  simp

abbrev E := Bool → ℝ

/-- The full actual empirical probability vector, counting all n+1 observed states. -/
def occupation (n : ℕ) : E := fun s => (countState (n+1) s : ℝ) / (n+1)

def stationary : E := fun _ => 1/2

lemma occupation_probability_vector (n : ℕ) :
    (∀ s, 0 ≤ occupation n s) ∧ ∑ s, occupation n s = 1 := by
  constructor
  · intro s
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · rw [Fintype.sum_bool]
    unfold occupation
    rw [← add_div]
    have hc : (countState (n+1) true : ℝ) + countState (n+1) false = n+1 := by
      exact_mod_cast (by simpa [add_comm] using count_total (n+1))
    rw [hc]
    exact div_self (by positivity)

lemma occupation_deviation (n : ℕ) (s : Bool) :
    |occupation n s - 1/2| ≤ 1/(n+1 : ℝ) := by
  have hc1 : 2 * countState (n+1) s ≤ (n+1)+1 := by
    have ht := count_true (n+1)
    have hsum := count_total (n+1)
    cases s <;> omega
  have hc2 : n+1 ≤ 2 * countState (n+1) s + 1 := by
    have ht := count_true (n+1)
    have hsum := count_total (n+1)
    cases s <;> omega
  have hr1 : 2 * (countState (n+1) s : ℝ) ≤ (n+1 : ℝ)+1 := by exact_mod_cast hc1
  have hr2 : (n+1 : ℝ) ≤ 2 * (countState (n+1) s : ℝ)+1 := by exact_mod_cast hc2
  have hn : 0 < (n+1 : ℝ) := by positivity
  have hm : occupation n s * (n+1) = (countState (n+1) s : ℝ) :=
    div_mul_cancel₀ _ hn.ne'
  apply abs_le.mpr
  constructor
  · rw [← neg_div]
    apply (div_le_iff₀ hn).mpr
    nlinarith
  · apply (le_div_iff₀ hn).mpr
    nlinarith

theorem occupation_tendsto : Tendsto occupation atTop (𝓝 stationary) := by
  apply tendsto_pi_nhds.mpr
  intro s
  have ht : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hcast.eventually (eventually_ge_atTop b)] with n hn
    linarith
  have hi : Tendsto (fun n : ℕ => 1/(n+1 : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp ht
  have hd : Tendsto (fun n => |occupation n s - 1/2|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) (fun n => occupation_deviation n s) hi
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hd)

def pathOccupation (n : ℕ) (ω : ℕ → Bool) : E := fun s =>
  ((∑ k ∈ Finset.range (n+1), if ω k=s then 1 else 0 : ℕ) : ℝ)/(n+1)

/-- The probability law of the genuine empirical vector is the process-law pushforward. -/
def empiricalLaw (n : ℕ) : Measure E := (processLaw.map (pathOccupation n)).toMeasure

lemma empiricalLaw_eq (n : ℕ) : empiricalLaw n = Measure.dirac (occupation n) := by
  simp only [empiricalLaw, processLaw, PMF.pure_map, PMF.toMeasure_pure]
  rfl

theorem empiricalLaw_probability (n : ℕ) : IsProbabilityMeasure (empiricalLaw n) := by
  unfold empiricalLaw
  infer_instance

def rate : E → EReal := pointRate stationary

theorem empirical_good_ldp : HasLDP empiricalLaw rate ∧ LowerSemicontinuous rate ∧
    (∀ r : ℝ, IsCompact {x | rate x ≤ (r : EReal)}) := by
  have he : empiricalLaw = fun n => Measure.dirac (occupation n) := funext empiricalLaw_eq
  rw [he]
  exact ⟨convergent_dirac_ldp occupation stationary occupation_tendsto,
    pointRate_lowerSemicontinuous stationary, pointRate_good stationary⟩

theorem unique_rate_zero (x : E) : rate x=0 ↔ x=stationary := by
  by_cases hx : x=stationary <;> simp [rate, pointRate, hx]

theorem stationary_invariant : (∑ s, stationary s = 1) ∧
    (∀ s, 0 ≤ stationary s) ∧ (∀ t, ∑ s, stationary s * P s t = stationary t) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [stationary, Fintype.sum_bool]
  · intro s; norm_num [stationary]
  · intro t; cases t <;> norm_num [stationary, P, Fintype.sum_bool]

theorem stationary_unique (w : E) (hw : ∑ s, w s = 1)
    (hP : ∀ t, ∑ s, w s * P s t = w t) : w=stationary := by
  have hf := hP false
  simp only [Fintype.sum_bool] at hw
  norm_num [P, Fintype.sum_bool] at hf
  funext s
  cases s <;> dsimp [stationary] <;> linarith

/-- An actual affine coordinate on the interior of the two-state probability simplex. -/
def probabilityLine (t : ℝ) : E := fun s => if s then 1/2+t else 1/2-t

lemma probabilityLine_valid {t : ℝ} (ht : |t|≤1/2) :
    (∀ s, 0 ≤ probabilityLine t s) ∧ ∑ s, probabilityLine t s = 1 := by
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  constructor
  · intro s; cases s <;> simp only [probabilityLine, Bool.false_eq_true, if_false, if_true] <;> linarith
  · norm_num [probabilityLine, Fintype.sum_bool]

lemma probabilityLine_eq (t : ℝ) : probabilityLine t=stationary ↔ t=0 := by
  constructor
  · intro h
    have he := congrFun h true
    dsimp [probabilityLine, stationary] at he
    linarith
  · rintro rfl
    funext s
    cases s <;> simp [probabilityLine, stationary]

theorem rate_infinite_in_every_simplex_neighborhood {δ : ℝ} (hδ : 0<δ) :
    ∃ t : ℝ, 0<t ∧ |t|<δ ∧ |t|<1/2 ∧
      (∀ s, 0≤probabilityLine t s) ∧ (∑ s, probabilityLine t s=1) ∧
      rate (probabilityLine t)=⊤ := by
  let t := min δ (1/2) / 2
  have ht : 0<t := div_pos (lt_min hδ (by norm_num)) (by norm_num)
  have htδ : t<δ := by dsimp [t]; have := min_le_left δ (1/2); linarith
  have ht2 : t<1/2 := by dsimp [t]; have := min_le_right δ (1/2); linarith
  have hv := probabilityLine_valid (t := t) (by rw [abs_of_pos ht]; exact ht2.le)
  refine ⟨t, ht, by rwa [abs_of_pos ht], by rwa [abs_of_pos ht], hv.1, hv.2, ?_⟩
  have hn : probabilityLine t ≠ stationary := fun h => ht.ne' ((probabilityLine_eq t).mp h)
  simp [rate, pointRate, hn]

/-- The actual rate has no real-valued germ even along the interior probability line.
Consequently no ordinary real first derivative or Hessian exists there. -/
theorem no_local_real_rate :
    ¬ ∃ δ : ℝ, 0<δ ∧ ∃ f : ℝ → ℝ,
      ∀ t : ℝ, |t|<δ → |t|<1/2 → rate (probabilityLine t) = (f t : EReal) := by
  rintro ⟨δ, hδ, f, hf⟩
  obtain ⟨t, _, htδ, ht2, _, _, ht⟩ := rate_infinite_in_every_simplex_neighborhood hδ
  have he := hf t htδ ht2
  rw [ht] at he
  exact EReal.coe_ne_top (f t) he.symm

#print axioms P_irreducible
#print axioms process_path_probability
#print axioms process_path_measure_probability
#print axioms empiricalLaw_probability
#print axioms occupation_probability_vector
#print axioms occupation_tendsto
#print axioms empirical_good_ldp
#print axioms unique_rate_zero
#print axioms stationary_unique
#print axioms rate_infinite_in_every_simplex_neighborhood
#print axioms no_local_real_rate

end Conjecture2801
