import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

open Filter Topology
open scoped ENNReal

namespace TwoPointLDP

noncomputable def normalizedLog (p : ℝ≥0∞) (n : ℕ) : EReal :=
  ((1 / ((n : ℝ) + 1) : ℝ) : EReal) * ENNReal.log p

lemma normalizedLog_zero (n : ℕ) : normalizedLog 0 n = ⊥ := by
  unfold normalizedLog
  rw [ENNReal.log_zero, EReal.mul_bot_of_pos]
  exact_mod_cast (one_div_pos.mpr (by positivity : 0 < (n : ℝ) + 1))

lemma normalizedLog_tendsto_of_ne_zero {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    Tendsto (normalizedLog p) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * Real.log p.toReal)
      atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (Real.log p.toReal)
  have hc := EReal.tendsto_coe.mpr h
  unfold normalizedLog
  simpa only [ ENNReal.log_pos_real hp hp', ← EReal.coe_mul,
    EReal.coe_zero] using hc

lemma normalizedLog_tendsto_zero : Tendsto (normalizedLog 0) atTop (𝓝 ⊥) := by
  have h : normalizedLog 0 = fun _ : ℕ => (⊥ : EReal) :=
    funext normalizedLog_zero
  rw [h]
  exact tendsto_const_nhds

lemma normalizedLog_tendsto {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    Tendsto (normalizedLog p) atTop (𝓝 (if p = 0 then ⊥ else 0)) := by
  by_cases hp0 : p = 0
  · subst p
    simpa using normalizedLog_tendsto_zero
  · simpa [hp0] using normalizedLog_tendsto_of_ne_zero hp0 hp

end TwoPointLDP

#print axioms TwoPointLDP.normalizedLog_zero
#print axioms TwoPointLDP.normalizedLog_tendsto_of_ne_zero
#print axioms TwoPointLDP.normalizedLog_tendsto_zero
#print axioms TwoPointLDP.normalizedLog_tendsto
