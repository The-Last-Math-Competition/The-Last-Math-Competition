import Conjecture1421.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.Ring.Pow

/-! Mixing times are minima of the actual finite-sum total variation distance.
The lemmas in this module take a profile identity that is proved from matrix powers in Powers. -/
noncomputable section
open Filter
open scoped Topology
namespace Conjecture1421

def mixingTime (n : ℕ) (ε : ℝ) : ℕ := sInf {t | worstTV n t ≤ ε}

/-- The usual quantified fixed-tolerance total-variation cutoff criterion. -/
def HasTVCutoff : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    Tendsto (fun n => (mixingTime n ε : ℝ) / (mixingTime n (1 - ε) : ℝ))
      atTop (𝓝 1)

def totalTime (n : ℕ) : ℝ := mixingTime n (1 / 4)
def window (n : ℕ) : ℝ := totalTime n - mixingTime n (3 / 4)
def windowRatio (n : ℕ) : ℝ := totalTime n / window n

lemma size_tendsto : Tendsto size atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  change Tendsto (fun n : ℕ => ((n + 4 : ℕ) : ℝ)) atTop atTop
  simpa using h

lemma group_order_tendsto :
    Tendsto (fun n => (Fintype.card (State n) : ℝ)) atTop atTop := by
  simpa [state_card, size] using size_tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)

section ProfileConsequences
variable (hprofile : ∀ n t, worstTV n t =
  if t = 0 then 1 - 1 / (2 * size n) else q n ^ t / 2)
include hprofile

lemma threshold_nonempty (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    {t : ℕ | worstTV n t ≤ ε}.Nonempty := by
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (show 0 < 2 * ε by positivity) (q_lt_one n)
  refine ⟨t + 1, ?_⟩
  change worstTV n (t + 1) ≤ ε
  rw [hprofile, if_neg (by omega)]
  have hpow : q n ^ (t + 1) ≤ q n ^ t := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (q_pos n).le t) (q_lt_one n).le
  linarith

lemma mixingTime_attained (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    worstTV n (mixingTime n ε) ≤ ε :=
  Nat.sInf_mem (threshold_nonempty hprofile n ε hε)

omit hprofile in
lemma mixingTime_minimal (n t : ℕ) (ε : ℝ) (ht : t < mixingTime n ε) :
    ε < worstTV n t := by
  exact lt_of_not_ge (Nat.not_mem_of_lt_sInf ht)

lemma initial_distance_gt_three_quarters (n : ℕ) : (3 / 4 : ℝ) < worstTV n 0 := by
  rw [hprofile, if_pos rfl]
  have hn := size_ge_four n
  have hi : 1 / (2 * size n) < (1 / 4 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * size n)).2
    linarith
  linarith

lemma mixingTime_three_quarters (n : ℕ) : mixingTime n (3 / 4) = 1 := by
  have hle : mixingTime n (3 / 4) ≤ 1 := by
    apply Nat.sInf_le
    rw [Set.mem_setOf_eq, hprofile, if_neg (by omega), pow_one]
    have := q_lt_one n
    linarith
  have hne : mixingTime n (3 / 4) ≠ 0 := by
    intro heq
    have h := mixingTime_attained hprofile n (3 / 4) (by norm_num)
    rw [heq] at h
    exact (not_le_of_gt (initial_distance_gt_three_quarters hprofile n)) h
  omega

lemma quarter_time_lower_bound (n : ℕ) : size n / 2 ≤ totalTime n := by
  have hm := mixingTime_attained hprofile n (1 / 4) (by norm_num)
  have ht : mixingTime n (1 / 4) ≠ 0 := by
    intro heq
    rw [heq] at hm
    have h0 := initial_distance_gt_three_quarters hprofile n
    linarith
  rw [hprofile, if_neg ht] at hm
  have hBern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / size n) by
    have hq := q_pos n
    dsimp [q] at hq
    linarith) (mixingTime n (1 / 4))
  have hBern' : 1 - (mixingTime n (1 / 4) : ℝ) / size n ≤
      q n ^ mixingTime n (1 / 4) := by
    simpa [q, sub_eq_add_neg, mul_div_assoc] using hBern
  have htdiv : (1 / 2 : ℝ) ≤ (mixingTime n (1 / 4) : ℝ) / size n := by linarith
  have := (le_div_iff₀ (size_pos n)).mp htdiv
  dsimp [totalTime]
  linarith

lemma totalTime_ge_two (n : ℕ) : 2 ≤ totalTime n := by
  have := quarter_time_lower_bound hprofile n
  have := size_ge_four n
  linarith

lemma totalTime_tendsto : Tendsto totalTime atTop atTop := by
  apply tendsto_atTop_mono (quarter_time_lower_bound hprofile)
  simpa [div_eq_mul_inv, mul_comm] using
    size_tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)

lemma window_eq (n : ℕ) : window n = totalTime n - 1 := by
  simp [window, mixingTime_three_quarters hprofile]

lemma window_pos (n : ℕ) : 0 < window n := by
  rw [window_eq hprofile]
  have := totalTime_ge_two hprofile n
  linarith

lemma windowRatio_eq (n : ℕ) : windowRatio n = 1 + (totalTime n - 1)⁻¹ := by
  have hne : totalTime n - 1 ≠ 0 := ne_of_gt (by
    have := totalTime_ge_two hprofile n
    linarith)
  rw [windowRatio, window_eq hprofile]
  field_simp

lemma windowRatio_le_two (n : ℕ) : windowRatio n ≤ 2 := by
  unfold windowRatio
  apply (div_le_iff₀ (window_pos hprofile n)).2
  rw [window_eq hprofile]
  have := totalTime_ge_two hprofile n
  linarith

lemma windowRatio_tendsto_one : Tendsto windowRatio atTop (𝓝 1) := by
  have hw : Tendsto (fun n => totalTime n - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (totalTime_tendsto hprofile).atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
  have h : Tendsto (fun n => (1 : ℝ) + (totalTime n - 1)⁻¹) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp hw)
  change Tendsto (fun n => windowRatio n) atTop (𝓝 1)
  simpa only [add_zero, ← windowRatio_eq hprofile] using h

lemma windowRatio_not_tendsto_atTop : ¬ Tendsto windowRatio atTop atTop :=
  not_tendsto_atTop_of_tendsto_nhds (windowRatio_tendsto_one hprofile)

lemma not_hasTVCutoff : ¬ HasTVCutoff := by
  intro h
  have hc := h (1 / 4) (by norm_num) (by norm_num)
  have ht : Tendsto totalTime atTop (𝓝 1) := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at hc
    simp_rw [mixingTime_three_quarters hprofile, Nat.cast_one, div_one] at hc
    exact hc
  exact not_tendsto_nhds_of_tendsto_atTop (totalTime_tendsto hprofile) 1 ht

end ProfileConsequences
end Conjecture1421
