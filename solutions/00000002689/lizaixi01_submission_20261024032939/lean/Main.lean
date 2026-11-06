import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

noncomputable section

open Filter Topology Finset

set_option backward.isDefEq.respectTransparency false

namespace TLMC2689

def f (x : ℚ) : ℚ := x ^ 2

def fPolynomial : Polynomial ℚ := Polynomial.X ^ 2

theorem polynomial_evaluates (x : ℚ) : fPolynomial.eval x = f x := by
  simp [fPolynomial, f]

theorem polynomial_degree : fPolynomial.natDegree = 2 := by
  simp [fPolynomial]

theorem iterate_eq (x : ℚ) (n : ℕ) : (f^[n]) x = x ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (f^[n + 1]) x = ((f^[n]) x) ^ 2 := by
        rw [Function.iterate_succ_apply', f]
      _ = (x ^ (2 ^ n)) ^ 2 := by rw [ih]
      _ = x ^ (2 ^ n * 2) := by rw [pow_mul]
      _ = x ^ (2 ^ (n + 1)) := by rw [pow_succ]

def forwardOrbit (x : ℚ) : Set ℚ := Set.range (fun n : ℕ => (f^[n]) x)

def IsPreperiodic (x : ℚ) : Prop := (forwardOrbit x).Finite

theorem orbit_two_strictMono : StrictMono (fun n : ℕ => (f^[n]) (2 : ℚ)) := by
  intro m n hmn
  simp only [iterate_eq]
  exact pow_lt_pow_right₀ (by norm_num) (pow_lt_pow_right₀ (by norm_num) hmn)

theorem two_not_preperiodic : ¬ IsPreperiodic 2 := by
  exact Set.infinite_range_of_injective orbit_two_strictMono.injective

theorem log_height_iterate (x : ℚ) (n : ℕ) :
    Height.logHeight₁ ((f^[n]) x) = (2 : ℝ) ^ n * Height.logHeight₁ x := by
  rw [iterate_eq, Height.logHeight₁_pow]
  norm_cast

theorem log_height_two : Height.logHeight₁ (2 : ℚ) = Real.log 2 := by
  simpa only [Nat.cast_ofNat] using Rat.logHeight₁_natCast 2

theorem mul_height_two : Height.mulHeight₁ (2 : ℚ) = 2 := by
  simpa only [Nat.cast_ofNat] using Rat.mulHeight₁_natCast 2

theorem mul_height_two_iterate (n : ℕ) :
    Height.mulHeight₁ ((f^[n]) (2 : ℚ)) = (2 : ℝ) ^ (2 ^ n) := by
  rw [iterate_eq, Height.mulHeight₁_pow, mul_height_two]

theorem log_height_two_iterate (n : ℕ) :
    Height.logHeight₁ ((f^[n]) (2 : ℚ)) = (2 : ℝ) ^ n * Real.log 2 := by
  rw [log_height_iterate, log_height_two]

def normalizedHeight (x : ℚ) (n : ℕ) : ℝ :=
  Height.logHeight₁ ((f^[n]) x) / (2 : ℝ) ^ n

theorem normalizedHeight_eq (x : ℚ) (n : ℕ) :
    normalizedHeight x n = Height.logHeight₁ x := by
  rw [normalizedHeight, log_height_iterate]
  field_simp

theorem canonical_height_limit (x : ℚ) :
    Tendsto (normalizedHeight x) atTop (𝓝 (Height.logHeight₁ x)) := by
  have heq : normalizedHeight x = fun _ => Height.logHeight₁ x :=
    funext (normalizedHeight_eq x)
  rw [heq]
  exact tendsto_const_nhds

def canonicalHeight (x : ℚ) : ℝ := limUnder atTop (normalizedHeight x)

theorem canonicalHeight_eq (x : ℚ) : canonicalHeight x = Height.logHeight₁ x :=
  (canonical_height_limit x).limUnder_eq

theorem canonicalHeight_two : canonicalHeight 2 = Real.log 2 := by
  rw [canonicalHeight_eq, log_height_two]

theorem canonicalHeight_two_pos : 0 < canonicalHeight 2 := by
  rw [canonicalHeight_two]
  exact Real.log_pos (by norm_num)

/-- Ordinary Cesaro mean of the actual logarithmic Weil heights. -/
def meanHeight (n : ℕ) : ℝ :=
  (∑ k ∈ range n, Height.logHeight₁ ((f^[k]) (2 : ℚ))) / n

theorem geometric_sum_two (n : ℕ) :
    (∑ k ∈ range n, (2 : ℝ) ^ k) = (2 : ℝ) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ]
    ring

theorem meanHeight_eq (n : ℕ) :
    meanHeight n = ((2 : ℝ) ^ n - 1) * Real.log 2 / n := by
  unfold meanHeight
  simp_rw [log_height_two_iterate]
  rw [← sum_mul, geometric_sum_two]

theorem pow_two_ge_linear (n : ℕ) : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    push_cast
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith

theorem sum_linear (n : ℕ) :
    (∑ k ∈ range n, ((k : ℝ) + 1)) = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem meanHeight_lower (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) + 1) / 2 * Real.log 2 ≤ meanHeight n := by
  have hsum : (n : ℝ) * (n + 1) / 2 ≤ (2 : ℝ) ^ n - 1 := by
    rw [← sum_linear, ← geometric_sum_two]
    exact sum_le_sum fun k _ => pow_two_ge_linear k
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [meanHeight_eq]
  apply (le_div_iff₀ (Nat.cast_pos.mpr hn)).2
  calc
    ((n : ℝ) + 1) / 2 * Real.log 2 * n =
        ((n : ℝ) * (n + 1) / 2) * Real.log 2 := by ring
    _ ≤ ((2 : ℝ) ^ n - 1) * Real.log 2 := mul_le_mul_of_nonneg_right hsum hlog.le

theorem meanHeight_tendsto_atTop : Tendsto meanHeight atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * b / Real.log 2)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnpos : 0 < n := by omega
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_left N 1) hn)
  have hmul : 2 * b < (N : ℝ) * Real.log 2 := (div_lt_iff₀ hlog).mp hN
  have hb : b ≤ ((n : ℝ) + 1) / 2 * Real.log 2 := by nlinarith
  exact hb.trans (meanHeight_lower n hnpos)

theorem meanHeight_no_finite_limit (L : ℝ) :
    ¬ Tendsto meanHeight atTop (𝓝 L) :=
  not_tendsto_nhds_of_tendsto_atTop meanHeight_tendsto_atTop L

/-- The same obstruction if naive height means the multiplicative height. -/
def meanMultiplicativeHeight (n : ℕ) : ℝ :=
  (∑ k ∈ range n, Height.mulHeight₁ ((f^[k]) (2 : ℚ))) / n

theorem meanHeight_le_multiplicative (n : ℕ) :
    meanHeight n ≤ meanMultiplicativeHeight n := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply sum_le_sum
  intro k _
  rw [Height.logHeight₁_eq_log_mulHeight₁]
  exact Real.log_le_self (Height.mulHeight₁_nonneg _)

theorem meanMultiplicativeHeight_tendsto_atTop :
    Tendsto meanMultiplicativeHeight atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1 meanHeight_tendsto_atTop) b] with n hn
  exact hn.trans (meanHeight_le_multiplicative n)

theorem meanMultiplicativeHeight_no_finite_limit (L : ℝ) :
    ¬ Tendsto meanMultiplicativeHeight atTop (𝓝 L) :=
  not_tendsto_nhds_of_tendsto_atTop meanMultiplicativeHeight_tendsto_atTop L

theorem counterexample :
    fPolynomial.natDegree = 2 ∧ ¬ IsPreperiodic 2 ∧
    canonicalHeight 2 = Real.log 2 ∧ 0 < canonicalHeight 2 ∧
    Tendsto meanHeight atTop atTop ∧
    Tendsto meanMultiplicativeHeight atTop atTop ∧
    (∀ L : ℝ, ¬ Tendsto meanHeight atTop (𝓝 L)) ∧
    (∀ L : ℝ, ¬ Tendsto meanMultiplicativeHeight atTop (𝓝 L)) :=
  ⟨polynomial_degree, two_not_preperiodic, canonicalHeight_two, canonicalHeight_two_pos,
    meanHeight_tendsto_atTop, meanMultiplicativeHeight_tendsto_atTop,
    meanHeight_no_finite_limit, meanMultiplicativeHeight_no_finite_limit⟩

end TLMC2689

