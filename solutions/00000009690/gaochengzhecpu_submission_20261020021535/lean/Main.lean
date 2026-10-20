import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Conjecture9690
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section

def linearForm (a b : ℕ) : ℝ := a * Real.log 2 - b * Real.log 3

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
theorem log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
theorem log_two_lt_three : Real.log 2 < Real.log 3 :=
  Real.log_lt_log (by norm_num) (by norm_num)

/-- Nonvanishing is proved arithmetically, not assumed as a side condition. -/
theorem linearForm_ne_zero {a b : ℕ} (ha : 0 < a) : linearForm a b ≠ 0 := by
  intro h
  have hlog : Real.log ((2 : ℝ) ^ a) = Real.log ((3 : ℝ) ^ b) := by
    rw [Real.log_pow, Real.log_pow]
    dsimp [linearForm] at h
    linarith
  have hp : (2 : ℝ) ^ a = (3 : ℝ) ^ b :=
    Real.log_injOn_pos (by change 0 < (2 : ℝ)^a; positivity)
      (by change 0 < (3 : ℝ)^b; positivity) hlog
  have hpn : (2 : ℕ) ^ a = 3 ^ b := by exact_mod_cast hp
  have hdiv : 2 ∣ (3 : ℕ) ^ b := hpn ▸ dvd_pow_self 2 ha.ne'
  have hbad := Nat.prime_two.dvd_of_dvd_pow hdiv
  norm_num at hbad

/-- Fixed algebraic arguments 2,3; integer coefficients bounded by N+1. -/
theorem dirichlet_forms (N : ℕ) (hN : 0 < N) :
    ∃ a b : ℕ, 0 < a ∧ a ≤ N ∧ b ≤ N + 1 ∧
      0 < |linearForm a b| ∧ |linearForm a b| ≤ Real.log 3 / (N + 1 : ℝ) := by
  let ξ := Real.log 2 / Real.log 3
  have hξ : 0 < ξ := div_pos log_two_pos log_three_pos
  have hξ1 : ξ < 1 := (div_lt_one log_three_pos).mpr log_two_lt_three
  obtain ⟨a, ha, haN, happ⟩ := Real.exists_nat_abs_mul_sub_round_le ξ hN
  let j : ℤ := round ((a : ℝ) * ξ)
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hj0 : 0 ≤ j := by
    have hp : 0 ≤ (a : ℝ) * ξ := mul_nonneg (Nat.cast_nonneg a) hξ.le
    have hg := (abs_le.mp happ).2
    have he : (1 : ℝ) / (N + 1) < 1 := by
      apply (div_lt_one hN1).mpr
      have : (0 : ℝ) < N := by exact_mod_cast hN
      linarith
    have : (-1 : ℝ) < j := by
      change (a : ℝ) * ξ - (j : ℝ) ≤ 1 / (N + 1) at hg
      linarith
    have : (-1 : ℤ) < j := by exact_mod_cast this
    omega
  let b := j.toNat
  have hb : (b : ℝ) = j := by
    dsimp [b]
    exact_mod_cast (Int.toNat_of_nonneg hj0 : (j.toNat : ℤ) = j)
  have he1 : (1 : ℝ) / (N + 1) ≤ 1 := by
    apply (div_le_iff₀ hN1).mpr
    nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  have hbound : (b : ℝ) ≤ N + 1 := by
    have haa : (a : ℝ) ≤ N := by exact_mod_cast haN
    have hap := (abs_le.mp happ).1
    change -(1 / ((N : ℝ) + 1)) ≤ (a : ℝ) * ξ - (j : ℝ) at hap
    rw [← hb] at hap
    have : (a : ℝ) * ξ ≤ N :=
      (mul_le_of_le_one_right (Nat.cast_nonneg a) hξ1.le).trans haa
    linarith
  have hboundn : b ≤ N + 1 := by exact_mod_cast hbound
  refine ⟨a, b, ha, haN, hboundn, abs_pos.mpr (linearForm_ne_zero ha), ?_⟩
  have hrewrite : linearForm a b = ((a : ℝ) * ξ - j) * Real.log 3 := by
    dsimp [linearForm, ξ]
    rw [← hb]
    field_simp
    ring
  rw [hrewrite, abs_mul, abs_of_pos log_three_pos]
  calc
    _ ≤ (1 / (N + 1 : ℝ)) * Real.log 3 :=
      mul_le_mul_of_nonneg_right happ log_three_pos.le
    _ = Real.log 3 / (N + 1 : ℝ) := by ring

theorem logarithmic_error_limit :
    Tendsto (fun N : ℕ => Real.log 3 * (Real.log (N + 1 : ℝ)) ^ 2 / (N + 1))
      atTop (𝓝 0) := by
  have ha : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat 1).mpr (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp ha
  have ht : Tendsto (fun N : ℕ => (Real.log (N + 1 : ℝ)) ^ 2 / (N + 1))
      atTop (𝓝 0) := by simpa [Function.comp_def] using hh
  simpa only [mul_zero, ← mul_div_assoc] using ht.const_mul (Real.log 3)

/-- The standard height is the actual maximum, not a freely inflated bound. -/
def height (a b : ℕ) : ℕ := max 3 (max a b)

lemma finite_positive_bound {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 < f x) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, δ ≤ f x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨δ, hδ, hb⟩ := ih (fun y hy => hf y (Finset.mem_insert_of_mem hy))
    refine ⟨min δ (f x), lt_min hδ (hf x (Finset.mem_insert_self _ _)), ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · subst y; exact min_le_right _ _
    · exact (min_le_left _ _).trans (hb y h)

lemma small_forms_bound (H : ℕ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ a b : ℕ, 0 < a → a ≤ H → b ≤ H → δ ≤ |linearForm a b| := by
  let s := ((Finset.range (H+1)).product (Finset.range (H+1))).filter (fun p => 0 < p.1)
  have hs : ∀ p ∈ s, 0 < |linearForm p.1 p.2| := by
    intro p hp
    exact abs_pos.mpr (linearForm_ne_zero (Finset.mem_filter.mp hp).2)
  obtain ⟨δ, hδ, hb⟩ := finite_positive_bound s (fun p => |linearForm p.1 p.2|) hs
  refine ⟨δ, hδ, ?_⟩
  intro a b ha haH hbH
  apply hb (a,b)
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, ha⟩

theorem reciprocal_error_limit :
    Tendsto (fun N : ℕ => Real.log 3 / (N + 1 : ℝ)) atTop (𝓝 0) := by
  have ha : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat 1).mpr (tendsto_natCast_atTop_atTop (R := ℝ))
  exact ha.const_div_atTop (Real.log 3)

/-- Arbitrarily large actual coefficient heights violate every positive
constant in the conjectured estimate, already at epsilon=1. -/
theorem counterexample (C : ℝ) (hC : 0 < C) (H₀ : ℕ) :
    ∃ a b : ℕ, 0 < a ∧ H₀ ≤ height a b ∧ 0 < |linearForm a b| ∧
      |linearForm a b| < C / (Real.log (height a b)) ^ 2 := by
  obtain ⟨δ, hδ, hfinite⟩ := small_forms_bound H₀
  have hs : ∀ᶠ N : ℕ in atTop,
      Real.log 3 * (Real.log (N + 1 : ℝ)) ^ 2 / (N + 1) < C :=
    logarithmic_error_limit.eventually_lt_const hC
  have hd : ∀ᶠ N : ℕ in atTop, Real.log 3 / (N + 1 : ℝ) < δ :=
    reciprocal_error_limit.eventually_lt_const hδ
  obtain ⟨N, hN, hsmall, hdelta⟩ := ((eventually_ge_atTop 2).and (hs.and hd)).exists
  obtain ⟨a, b, ha, haN, hb, hnz, happrox⟩ := dirichlet_forms N (by omega)
  have haH : a ≤ height a b := (le_max_left a b).trans (le_max_right 3 _)
  have hbH : b ≤ height a b := (le_max_right a b).trans (le_max_right 3 _)
  have hH : H₀ ≤ height a b := by
    by_contra h
    have hlt : height a b < H₀ := Nat.lt_of_not_ge h
    exact (not_lt_of_ge (hfinite a b ha (haH.trans hlt.le) (hbH.trans hlt.le)))
      (happrox.trans_lt hdelta)
  refine ⟨a, b, ha, hH, hnz, ?_⟩
  have hheight : height a b ≤ N + 1 := by
    dsimp [height]
    omega
  have h3 : 3 ≤ height a b := le_max_left _ _
  have hlog : 0 < Real.log (height a b) := Real.log_pos (by exact_mod_cast (by omega : 1 < height a b))
  have hlogB : Real.log (height a b) ≤ Real.log (N + 1 : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < height a b)) (by exact_mod_cast hheight)
  have hsq : (Real.log (height a b)) ^ 2 ≤ (Real.log (N + 1 : ℝ)) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hlog.le hlogB
  apply (lt_div_iff₀ (pow_pos hlog 2)).mpr
  calc
    _ ≤ |linearForm a b| * (Real.log (N + 1 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
    _ ≤ (Real.log 3 / (N + 1 : ℝ)) * (Real.log (N + 1 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right happrox (sq_nonneg _)
    _ < C := by convert hsmall using 1; ring

/-- No positive constant and no cutoff on the actual maximum rescue epsilon=1. -/
theorem no_uniform_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, ∀ a b : ℕ,
      0 < a → H₀ ≤ height a b →
      C / (Real.log (height a b)) ^ 2 ≤ |linearForm a b| := by
  rintro ⟨C, hC, H₀, h⟩
  obtain ⟨a, b, ha, hH, _, hsmall⟩ := counterexample C hC H₀
  exact (not_lt_of_ge (h a b ha hH)) hsmall

#print axioms linearForm_ne_zero
#print axioms dirichlet_forms
#print axioms logarithmic_error_limit
#print axioms counterexample
#print axioms no_uniform_bound
end
end Conjecture9690
