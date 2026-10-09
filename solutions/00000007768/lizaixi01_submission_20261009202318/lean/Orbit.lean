import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Function Polynomial

set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace TLMC7768

noncomputable section

def candidate : ℂ[X] := X ^ 2 - C 6
def quadratic (z : ℂ) : ℂ := z ^ 2 - 6
def filledJuliaSet (p : ℂ[X]) : Set ℂ :=
  {z | ∃ B : ℝ, ∀ n : ℕ, ‖(fun w => p.eval w)^[n] z‖ ≤ B}
def juliaSet (p : ℂ[X]) : Set ℂ := frontier (filledJuliaSet p)
def filled : Set ℂ := {z | ∃ B : ℝ, ∀ n : ℕ, ‖quadratic^[n] z‖ ≤ B}
def radiusFilled : Set ℂ := {z | ∀ n : ℕ, ‖quadratic^[n] z‖ ≤ 3}

theorem julia_closed (p : ℂ[X]) : IsClosed (juliaSet p) := isClosed_frontier

theorem candidate_eval : (fun z : ℂ => candidate.eval z) = quadratic := by
  funext z
  simp [candidate, quadratic]

theorem candidate_filled : filledJuliaSet candidate = filled := by
  simp only [filledJuliaSet, candidate_eval, filled]

theorem quadratic_continuous : Continuous quadratic :=
  (continuous_id.pow 2).sub continuous_const

theorem quadratic_re (z : ℂ) : (quadratic z).re = z.re ^ 2 - z.im ^ 2 - 6 := by
  simp [quadratic, pow_two, Complex.mul_re]

theorem quadratic_im (z : ℂ) : (quadratic z).im = 2 * z.re * z.im := by
  simp [quadratic, pow_two, Complex.mul_im]
  ring

theorem quadratic_norm_lower (z : ℂ) : ‖z‖ ^ 2 - 6 ≤ ‖quadratic z‖ := by
  have h := norm_sub_norm_le (z ^ 2) (6 : ℂ)
  simpa [quadratic, norm_pow] using h

theorem orbit_norm_growth (z : ℂ) (hz : 3 < ‖z‖) (n : ℕ) :
    ‖z‖ + (n : ℝ) * (‖z‖ - 3) ≤ ‖quadratic^[n] z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hr : ‖z‖ ≤ ‖quadratic^[n] z‖ := by nlinarith
    have hs : ‖quadratic^[n] z‖ + (‖z‖ - 3) ≤ ‖quadratic^[n] z‖ ^ 2 - 6 := by
      nlinarith [sq_nonneg (‖quadratic^[n] z‖ - 3)]
    have hf := quadratic_norm_lower (quadratic^[n] z)
    rw [Function.iterate_succ_apply']
    push_cast
    nlinarith

theorem norm_le_three_of_bounded (z : ℂ) (hz : z ∈ filled) : ‖z‖ ≤ 3 := by
  by_contra h
  have h3 : 3 < ‖z‖ := lt_of_not_ge h
  have hdelta : 0 < ‖z‖ - 3 := sub_pos.mpr h3
  rcases hz with ⟨B, hB⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((B - ‖z‖) / (‖z‖ - 3))
  have hm : B - ‖z‖ < (n : ℝ) * (‖z‖ - 3) := (div_lt_iff₀ hdelta).mp hn
  have hg := orbit_norm_growth z h3 n
  have hb := hB n
  linarith

theorem filled_iterate (z : ℂ) (hz : z ∈ filled) (m : ℕ) : quadratic^[m] z ∈ filled := by
  rcases hz with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro n
  simpa only [Function.iterate_add_apply] using hB (n + m)

theorem filled_eq_radius : filled = radiusFilled := by
  ext z
  constructor
  · intro hz n
    exact norm_le_three_of_bounded _ (filled_iterate z hz n)
  · intro hz
    exact ⟨3, hz⟩

theorem filled_closed : IsClosed filled := by
  rw [filled_eq_radius]
  have h : IsClosed (⋂ n : ℕ, {z : ℂ | ‖quadratic^[n] z‖ ≤ 3}) := by
    apply isClosed_iInter
    intro n
    exact isClosed_le (quadratic_continuous.iterate n).norm continuous_const
  simpa only [radiusFilled, Set.ofPred_forall] using h

theorem re_sq_lower (z : ℂ) (h : ‖quadratic z‖ ≤ 3) : 3 ≤ z.re ^ 2 - z.im ^ 2 := by
  have hr := Complex.abs_re_le_norm (quadratic z)
  have hneg : -(3 : ℝ) ≤ (quadratic z).re := by
    have := neg_abs_le ((quadratic z).re)
    linarith
  rw [quadratic_re] at hneg
  linarith

theorem im_expansion (z : ℂ) (h : ‖quadratic z‖ ≤ 3) :
    2 * |z.im| ≤ |(quadratic z).im| := by
  have hs := re_sq_lower z h
  have ha : 1 ≤ |z.re| := by
    have ha0 := abs_nonneg z.re
    have hi0 := sq_nonneg z.im
    have ha2 : |z.re| ^ 2 = z.re ^ 2 := sq_abs z.re
    nlinarith
  rw [quadratic_im, abs_mul, abs_mul]
  norm_num
  exact mul_le_mul_of_nonneg_right (by linarith : 2 ≤ 2 * |z.re|) (abs_nonneg _)

theorem orbit_im_growth (z : ℂ) (hz : z ∈ radiusFilled) (n : ℕ) :
    (2 : ℝ) ^ n * |z.im| ≤ |(quadratic^[n] z).im| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : 2 * |(quadratic^[n] z).im| ≤ |(quadratic^[n + 1] z).im| := by
      have hn : ‖quadratic (quadratic^[n] z)‖ ≤ 3 := by
        simpa only [Function.iterate_succ_apply'] using hz (n + 1)
      simpa only [Function.iterate_succ_apply'] using im_expansion (quadratic^[n] z) hn
    calc
      (2 : ℝ) ^ (n + 1) * |z.im| = 2 * (2 ^ n * |z.im|) := by rw [pow_succ]; ring
      _ ≤ 2 * |(quadratic^[n] z).im| := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ |(quadratic^[n + 1] z).im| := he

theorem filled_im_zero (z : ℂ) (hz : z ∈ filled) : z.im = 0 := by
  have hr : z ∈ radiusFilled := filled_eq_radius ▸ hz
  by_contra hne
  have hp : 0 < |z.im| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / |z.im|) (by norm_num : (1 : ℝ) < 2)
  have hm : 3 < (2 : ℝ)^n * |z.im| := (div_lt_iff₀ hp).mp hn
  have hg := orbit_im_growth z hr n
  have hb := (Complex.abs_im_le_norm (quadratic^[n] z)).trans (hr n)
  linarith

theorem filled_real : filled ⊆ Set.range Complex.ofReal := by
  intro z hz
  refine ⟨z.re, ?_⟩
  apply Complex.ext
  · simp
  · simpa using (filled_im_zero z hz).symm

theorem julia_real : juliaSet candidate ⊆ Set.range Complex.ofReal := by
  rw [juliaSet, candidate_filled]
  exact frontier_subset_closure.trans
    (closure_minimal filled_real Complex.isometry_ofReal.isClosedEmbedding.isClosed_range)

theorem three_mem_filled : (3 : ℂ) ∈ filled := by
  refine ⟨3, ?_⟩
  intro n
  have hn : quadratic^[n] (3 : ℂ) = 3 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      norm_num [quadratic]
  norm_num [hn]

theorem three_mem_julia : (3 : ℂ) ∈ juliaSet candidate := by
  rw [juliaSet, candidate_filled, frontier_eq_closure_inter_closure]
  constructor
  · exact subset_closure three_mem_filled
  · apply Metric.mem_closure_iff.mpr
    intro ε hε
    refine ⟨(3 : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · intro hz
      have him := filled_im_zero _ hz
      simp at him
      linarith
    · simp [dist_eq_norm, Complex.norm_real, abs_of_pos hε]
      linarith

end
end TLMC7768
