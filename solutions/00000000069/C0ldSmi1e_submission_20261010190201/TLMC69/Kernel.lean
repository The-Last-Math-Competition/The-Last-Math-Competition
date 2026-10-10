import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic

noncomputable section
open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology
namespace TLMC69

def Q : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 - 4 * X ^ 2
  | n + 2 => (2 - 4 * X ^ 2) * Q (n + 1) - Q n

lemma Q_even (n : ℕ) (x : ℝ) : (Q n).eval (-x) = (Q n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Q]
  | one => simp [Q]
  | more n h0 h1 => simp [Q, h0, h1]

lemma Q_zero (n : ℕ) : (Q n).eval 0 = 2 * n + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Q]
  | one => norm_num [Q]
  | more n h0 h1 => simp [Q, h0, h1]; ring

lemma quad_degree (a b : ℝ) : (C a - C b * (X : ℝ[X])^2).natDegree ≤ 2 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · exact natDegree_mul_le.trans (by simp)

lemma Q_degree (n : ℕ) : (Q n).natDegree ≤ 2 * n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Q]
  | one => simpa only [Q, map_ofNat, Nat.mul_one] using quad_degree 3 4
  | more n h0 h1 =>
    change ((2 - 4 * X ^ 2) * Q (n + 1) - Q n).natDegree ≤ 2 * (n + 2)
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      have hd : (2 - 4 * (X : ℝ[X]) ^ 2).natDegree ≤ 2 := by
        simpa only [map_ofNat] using quad_degree 2 4
      omega
    · omega

lemma Q_sin (n : ℕ) (t : ℝ) :
    (Q n).eval (Real.sin t) * Real.sin t = Real.sin ((2 * n + 1) * t) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Q]
  | one =>
    norm_num [Q]
    rw [Real.sin_three_mul]
    ring
  | more n h0 h1 =>
    simp only [Q, eval_sub, eval_mul, eval_ofNat, eval_pow, eval_X]
    have hs := Real.two_mul_sin_mul_cos ((2 * (n : ℝ) + 3) * t) (2*t)
    have hc := Real.cos_two_mul t
    push_cast at *
    have ht3 : (2 * (n : ℝ) + 3) * t - 2 * t = (2 * n + 1) * t := by ring
    have ht4 : (2 * (n : ℝ) + 3) * t + 2 * t = (2 * (n + 2) + 1) * t := by ring
    have ht5 : (2 * ((n : ℝ) + 1) + 1) * t = (2 * n + 3) * t := by ring
    rw [ht3, ht4, ← ht5, ← h0, ← h1] at hs
    have hc2 : Real.cos (2*t) = 1 - 2 * Real.sin t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    rw [hc2] at hs
    linear_combination hs

lemma abs_sin_nat_mul_le (n : ℕ) (t : ℝ) :
    |Real.sin (n * t)| ≤ n * |Real.sin t| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
    calc
      _ ≤ |Real.sin (n * t) * Real.cos t| + |Real.cos (n * t) * Real.sin t| := abs_add_le _ _
      _ ≤ |Real.sin (n * t)| + |Real.sin t| := by
        simp only [abs_mul]
        exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
          (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
      _ ≤ (n + 1) * |Real.sin t| := by nlinarith

lemma Q_mul_bound (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |x * (Q n).eval x| ≤ 1 := by
  have h := Q_sin n (Real.arcsin x)
  rw [Real.sin_arcsin hx.1 hx.2] at h
  rw [mul_comm, h]
  exact Real.abs_sin_le_one _

lemma Q_bound (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(Q n).eval x| ≤ 2 * n + 1 := by
  by_cases hz : x = 0
  · subst x
    rw [Q_zero, abs_of_nonneg (by positivity)]
  have h := abs_sin_nat_mul_le (2*n+1) (Real.arcsin x)
  have he := Q_sin n (Real.arcsin x)
  rw [Real.sin_arcsin hx.1 hx.2] at h he
  push_cast at h
  rw [← he, abs_mul] at h
  exact (mul_le_mul_right (abs_pos.mpr hz)).mp h

lemma arcsin_le_twice {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : Real.arcsin x ≤ 2*x := by
  have ha : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr hx.1
  have h := Real.mul_le_sin ha (Real.arcsin_le_pi_div_two x)
  rw [Real.sin_arcsin (by linarith [hx.1]) hx.2] at h
  have hp := Real.pi_lt_four
  have hp0 := Real.pi_pos
  have hh : (1/2 : ℝ) ≤ 2 / Real.pi := by rw [le_div_iff₀ hp0]; linarith
  nlinarith [mul_le_mul_of_nonneg_right hh ha]

lemma Q_lower (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / (4 * (2 * n + 1)))) :
    (2 * n + 1) / 2 ≤ (Q n).eval x := by
  have hn : (0 : ℝ) < 2*n+1 := by positivity
  have hn1 : (1 : ℝ) ≤ 2*n+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx1 : x ≤ 1 := by
    have : 1 / (4 * (2 * (n : ℝ) + 1)) ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (2*n+1))]; nlinarith
    exact hx.2.trans this
  by_cases hz : x = 0
  · subst x; rw [Q_zero]; linarith
  have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hz)
  have ha := arcsin_le_twice ⟨hx.1, hx1⟩
  have ha0 : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr hx.1
  have hax : x ≤ Real.arcsin x := by
    have := Real.sin_le ha0
    rwa [Real.sin_arcsin (by linarith) hx1] at this
  have hb : (2*n+1) * Real.arcsin x ≤ Real.pi/2 := by
    have hc := (le_div_iff₀ (by positivity : (0:ℝ) < 4*(2*n+1))).mp hx.2
    nlinarith [Real.pi_gt_three, mul_le_mul_of_nonneg_left ha hn.le]
  have hs := Real.mul_le_sin (mul_nonneg hn.le ha0) hb
  have he := Q_sin n (Real.arcsin x)
  rw [Real.sin_arcsin (by linarith) hx1] at he
  rw [← he] at hs
  have hf : (1/2 : ℝ) ≤ 2 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
  have hg := mul_le_mul_of_nonneg_right hf (mul_nonneg hn.le ha0)
  have hi := mul_le_mul_of_nonneg_left hax hn.le
  nlinarith

end TLMC69
