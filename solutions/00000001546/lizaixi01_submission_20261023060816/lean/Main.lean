import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Universal analytic obstruction to the two necessary growth clauses.
No geometric counting function is assigned a value or replaced by a model. -/
namespace TLMC1546
open Filter Asymptotics
open scoped Topology

noncomputable def sqrtLog (n : ℕ) : ℝ := Real.sqrt (Real.log (n:ℝ))
noncomputable def envelope (C : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)*Real.exp (C*sqrtLog n)

theorem real_exponent_bound (C x : ℝ) (hx : 1≤x) :
    C*Real.sqrt (Real.log x) ≤ Real.log x+C^2/4 := by
  have hs := Real.sq_sqrt (Real.log_nonneg hx)
  nlinarith [sq_nonneg (Real.sqrt (Real.log x)-C/2)]

theorem real_envelope_bound (C x : ℝ) (hx : 1≤x) :
    x*Real.exp (C*Real.sqrt (Real.log x)) ≤ Real.exp (C^2/4)*x^2 := by
  have hx0 : 0<x := lt_of_lt_of_le zero_lt_one hx
  calc
    x*Real.exp (C*Real.sqrt (Real.log x))
      ≤ x*Real.exp (Real.log x+C^2/4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (real_exponent_bound C x hx)) hx0.le
    _ = Real.exp (C^2/4)*x^2 := by rw [Real.exp_add,Real.exp_log hx0]; ring

theorem envelope_nonneg (C : ℝ) (n : ℕ) : 0≤envelope C n :=
  mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le

theorem envelope_bigO (C : ℝ) :
    IsBigO atTop (envelope C) (fun n : ℕ => (n:ℝ)^2) := by
  apply IsBigO.of_bound (Real.exp (C^2/4))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (envelope_nonneg C n),Real.norm_of_nonneg (sq_nonneg (n:ℝ))]
  exact real_envelope_bound C (n:ℝ) hn'

theorem exponent_bigO_implies_quadratic (h : ℕ → ℝ)
    (hh : IsBigO atTop h sqrtLog) :
    IsBigO atTop (fun n : ℕ => (n:ℝ)*Real.exp (h n)) (fun n : ℕ => (n:ℝ)^2) := by
  obtain ⟨C,hC⟩ := hh.bound
  apply IsBigO.of_bound (Real.exp (C^2/4))
  filter_upwards [hC,eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hn1
  have hexp : h n ≤ C*sqrtLog n := by
    apply (le_abs_self (h n)).trans
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),sqrtLog] using hn
  calc
    ‖(n:ℝ)*Real.exp (h n)‖ = (n:ℝ)*Real.exp (h n) :=
      Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le)
    _ ≤ (n:ℝ)*Real.exp (C*sqrtLog n) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (Nat.cast_nonneg n)
    _ ≤ Real.exp (C^2/4)*(n:ℝ)^2 := real_envelope_bound C (n:ℝ) hn1'
    _ = Real.exp (C^2/4)*‖(n:ℝ)^2‖ := by rw [Real.norm_of_nonneg (sq_nonneg _)]

theorem any_function_bounded_by_envelope (f : ℕ → ℝ) (C : ℝ)
    (hf : IsBigO atTop f (envelope C)) :
    IsBigO atTop f (fun n : ℕ => (n:ℝ)^2) := hf.trans (envelope_bigO C)

theorem count_bound_implies_quadratic (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ᶠ n : ℕ in atTop, 0≤f n ∧ f n≤envelope C n) :
    IsBigO atTop f (fun n : ℕ => (n:ℝ)^2) := by
  apply any_function_bounded_by_envelope f C
  apply IsBigO.of_bound 1
  filter_upwards [hf] with n hn
  simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg hn.1,
    abs_of_nonneg (envelope_nonneg C n)] using hn.2

theorem source_expression_implies_quadratic (f h : ℕ → ℝ)
    (heq : f =ᶠ[atTop] fun n : ℕ => (n:ℝ)*Real.exp (h n))
    (hh : IsBigO atTop h sqrtLog) :
    IsBigO atTop f (fun n : ℕ => (n:ℝ)^2) := by
  obtain ⟨C,hC⟩ := (exponent_bigO_implies_quadratic h hh).bound
  apply IsBigO.of_bound C
  filter_upwards [heq,hC] with n hn hb
  simpa only [hn] using hb

def NoPolynomialUpperBound (f : ℕ → ℝ) : Prop :=
  ¬ ∃ d : ℕ, IsBigO atTop f (fun n : ℕ => (n:ℝ)^d)

theorem source_clauses_incompatible (f : ℕ → ℝ) :
    ¬ ((∃ h : ℕ → ℝ, IsBigO atTop h sqrtLog ∧
        f =ᶠ[atTop] fun n : ℕ => (n:ℝ)*Real.exp (h n)) ∧ NoPolynomialUpperBound f) := by
  rintro ⟨⟨h,hh,heq⟩,hnopoly⟩
  exact hnopoly ⟨2,source_expression_implies_quadratic f h heq hh⟩

theorem envelope_clauses_incompatible (f : ℕ → ℝ) :
    ¬ ((∃ C : ℝ, IsBigO atTop f (envelope C)) ∧ NoPolynomialUpperBound f) := by
  rintro ⟨⟨C,hC⟩,hnopoly⟩
  exact hnopoly ⟨2,any_function_bounded_by_envelope f C hC⟩

theorem natural_count_clauses_incompatible (f : ℕ → ℕ) :
    ¬ ((∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (f n:ℝ)≤envelope C n) ∧
      NoPolynomialUpperBound (fun n => (f n:ℝ))) := by
  rintro ⟨⟨C,hC⟩,hnopoly⟩
  apply hnopoly
  refine ⟨2,count_bound_implies_quadratic (fun n => (f n:ℝ)) C ?_⟩
  filter_upwards [hC] with n hn
  exact ⟨Nat.cast_nonneg _,hn⟩

end TLMC1546
