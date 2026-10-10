import TLMC214.PartitionBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

namespace TLMC214

noncomputable def partitionLog (n : ℕ) : ℝ := Real.log (partitionCount n : ℝ)

lemma partitionLog_nonneg (n : ℕ) : 0 ≤ partitionLog n := by
  apply Real.log_nonneg
  exact_mod_cast partitionCount_pos n

lemma partitionLog_unbounded (C : ℝ) : ∃ n : ℕ, C < partitionLog n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp C)
  refine ⟨n, ?_⟩
  have hcount : Real.exp C < (partitionCount n : ℝ) :=
    hn.trans_le (by exact_mod_cast nat_le_partitionCount n)
  simpa only [partitionLog, Real.log_exp] using Real.log_lt_log (Real.exp_pos C) hcount

lemma partitionLog_bound {n k : ℕ} (hn : n ≤ k * k) :
    partitionLog n ≤ (2 * (k : ℝ) + 1) * Real.log ((n : ℝ) + 1) + Real.log ((k : ℝ) + 1) := by
  have hp : 0 < (partitionCount n : ℝ) := by exact_mod_cast partitionCount_pos n
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have hb : (partitionCount n : ℝ) ≤ ((n : ℝ) + 1) ^ (k + 1) *
      (((k : ℝ) + 1) * ((n : ℝ) + 1) ^ k) := by
    exact_mod_cast partition_count_bound hn
  have h := Real.log_le_log hp hb
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (ne_of_gt hk1) (by positivity), Real.log_pow, Real.log_pow] at h
  push_cast at h
  unfold partitionLog
  nlinarith

lemma partitionLog_square_bound (k : ℕ) :
    partitionLog (k * k) ≤ (4 * (k : ℝ) + 3) * Real.log ((k : ℝ) + 1) := by
  have h := partitionLog_bound (n := k * k) (k := k) le_rfl
  push_cast at h
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hl : Real.log ((k : ℝ) * k + 1) ≤ 2 * Real.log ((k : ℝ) + 1) := by
    have h' := Real.log_le_log (x := (k : ℝ) * k + 1) (y := ((k : ℝ) + 1) ^ 2)
      (by positivity) (by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h'
  nlinarith

lemma partitionLog_no_affine_lower (a : ℝ) (ha : 0 < a) (b : ℝ) :
    ∃ n : ℕ, partitionLog n < b + a * (n : ℝ) := by
  have he := Real.isLittleO_log_id_atTop.bound (show 0 < a / 28 by positivity)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp he
  obtain ⟨k, hk⟩ := exists_nat_gt (max (max M 1) (-2 * b / a))
  have hk1 : 1 < (k : ℝ) := (le_max_right M 1).trans_lt ((le_max_left _ _).trans_lt hk)
  have hkM : M < (k : ℝ) := (le_max_left M 1).trans_lt ((le_max_left _ _).trans_lt hk)
  have hkb : -2 * b / a < (k : ℝ) := (le_max_right _ _).trans_lt hk
  have hlog := hM ((k : ℝ) + 1) (by linarith)
  simp only [Real.norm_eq_abs, id_eq] at hlog
  rw [abs_of_nonneg (Real.log_nonneg (by linarith)), abs_of_pos (by linarith : 0 < (k : ℝ) + 1)] at hlog
  have hbound := partitionLog_square_bound k
  have hprod : (4 * (k : ℝ) + 3) * ((k : ℝ) + 1) ≤ 14 * ((k : ℝ) * k) := by
    nlinarith
  have hhalf : partitionLog (k * k) ≤ a / 2 * ((k : ℝ) * k) := by
    have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4 * (k : ℝ) + 3 by positivity)
    have hm' := mul_le_mul_of_nonneg_left hprod (show 0 ≤ a / 28 by positivity)
    nlinarith
  have hb : -2 * b < (k : ℝ) * a := (div_lt_iff₀ ha).mp hkb
  refine ⟨k * k, ?_⟩
  push_cast
  have hsq : (k : ℝ) ≤ (k : ℝ) * k := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (le_of_lt ha)
  nlinarith

end TLMC214
