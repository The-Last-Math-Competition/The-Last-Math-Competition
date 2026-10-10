import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators

namespace Conjecture1679

/-- Positions of each labeled agent at times 0,...,r. These arbitrary
permutations include every schedule obtainable by matching swaps. -/
abbrev Schedule (n r : ℕ) := Fin (r + 1) → Equiv.Perm (Fin (n + 1))

def AllMet {n r : ℕ} (s : Schedule n r) : Prop :=
  ∀ a b : Fin (n + 1), a ≠ b →
    ∃ t : Fin (r + 1), (SimpleGraph.pathGraph (n + 1)).Adj (s t a) (s t b)

def visiblePair {n r : ℕ} (s : Schedule n r)
    (z : Fin (r + 1) × Fin n × Bool) : Fin (n + 1) × Fin (n + 1) :=
  if z.2.2 then ((s z.1).symm z.2.1.castSucc, (s z.1).symm z.2.1.succ)
  else ((s z.1).symm z.2.1.succ, (s z.1).symm z.2.1.castSucc)

theorem adjacent_is_visible {n r : ℕ} (s : Schedule n r)
    (a b : Fin (n + 1)) (t : Fin (r + 1))
    (h : (SimpleGraph.pathGraph (n + 1)).Adj (s t a) (s t b)) :
    ∃ z : Fin (r + 1) × Fin n × Bool, visiblePair s z = (a, b) := by
  rw [SimpleGraph.pathGraph_adj] at h
  rcases h with h | h
  · let i : Fin n := ⟨(s t a).val, by have := (s t b).isLt; omega⟩
    have hi : i.castSucc = s t a := by apply Fin.ext; rfl
    have hj : i.succ = s t b := by apply Fin.ext; exact h
    exact ⟨(t, i, true), by simp [visiblePair, hi, hj]⟩
  · let i : Fin n := ⟨(s t b).val, by have := (s t a).isLt; omega⟩
    have hi : i.castSucc = s t b := by apply Fin.ext; rfl
    have hj : i.succ = s t a := by apply Fin.ext; exact h
    exact ⟨(t, i, false), by simp [visiblePair, hi, hj]⟩

/-- Every round exposes at most 2n ordered pairs on the actual path. -/
theorem counting_lower_bound {n r : ℕ} (hn : 0 < n) (s : Schedule n r)
    (h : AllMet s) : n + 1 ≤ 2 * (r + 1) := by
  classical
  have hsub : (Finset.univ : Finset (Fin (n + 1))).offDiag ⊆
      Finset.univ.image (visiblePair s) := by
    intro p hp
    have hp' : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    obtain ⟨t, ht⟩ := h p.1 p.2 hp'
    obtain ⟨z, hz⟩ := adjacent_is_visible s p.1 p.2 t ht
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, hz⟩
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  have hleft : (Finset.univ : Finset (Fin (n + 1))).offDiag.card = (n + 1) * n := by
    rw [Finset.offDiag_card]
    simp only [Finset.card_univ, Fintype.card_fin]
    calc
      (n + 1) * (n + 1) - (n + 1) =
          (n + 1) * (n + 1) - (n + 1) * 1 := by rw [Nat.mul_one]
      _ = (n + 1) * ((n + 1) - 1) := (Nat.mul_sub_left_distrib _ _ _).symm
      _ = (n + 1) * n := by simp
  rw [hleft] at hc
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hc
  have hc' : (n + 1) * n ≤ (2 * (r + 1)) * n := by nlinarith [hc]
  exact Nat.le_of_mul_le_mul_right hc' hn

theorem no_short_schedule {n r : ℕ} (hn : 4 ≤ n + 1)
    (hlog : 4096 < Real.log (n + 1 : ℝ))
    (hr : (r : ℝ) ≤ 1024 * (n + 1 : ℝ) / Real.log (n + 1 : ℝ))
    (s : Schedule n r) : ¬ AllMet s := by
  intro h
  have hcount := counting_lower_bound (by omega : 0 < n) s h
  have hcountR : (n + 1 : ℝ) ≤ 2 * (r + 1 : ℝ) := by exact_mod_cast hcount
  have hnR : (4 : ℝ) ≤ n + 1 := by exact_mod_cast hn
  have hp : 0 < Real.log (n + 1 : ℝ) := by linarith
  have hquot : 1024 * (n + 1 : ℝ) / Real.log (n + 1 : ℝ) < (n + 1 : ℝ) / 4 := by
    apply (div_lt_iff₀ hp).mpr
    nlinarith
  linarith

/-- The bad vertex count exists, with no numerical approximation to log. -/
theorem exists_bad_path :
    ∃ n : ℕ, 4 ≤ n + 1 ∧ 4096 < Real.log (n + 1 : ℝ) ∧
      ∀ r : ℕ, (r : ℝ) ≤ 1024 * (n + 1 : ℝ) / Real.log (n + 1 : ℝ) →
        ∀ s : Schedule n r, ¬ AllMet s := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp 4096 + 4)
  have hpos := Real.exp_pos (4096 : ℝ)
  have hsize : 4 ≤ n + 1 := by exact_mod_cast (by linarith : (4 : ℝ) ≤ n + 1)
  have hlog : 4096 < Real.log (n + 1 : ℝ) := by
    calc
      4096 = Real.log (Real.exp 4096) := (Real.log_exp _).symm
      _ < Real.log (n + 1 : ℝ) := Real.log_lt_log hpos (by linarith)
  exact ⟨n, hsize, hlog, fun r hr s => no_short_schedule hsize hlog hr s⟩

theorem paths_connected (n : ℕ) : (SimpleGraph.pathGraph (n + 1)).Connected :=
  SimpleGraph.pathGraph_connected n

#print axioms counting_lower_bound
#print axioms exists_bad_path

end Conjecture1679
