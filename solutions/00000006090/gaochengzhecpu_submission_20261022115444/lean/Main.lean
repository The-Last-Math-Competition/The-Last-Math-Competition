import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace Conjecture6090

open Filter Topology

def objective (x : ℝ) : ℝ := x ^ 2 / 2

theorem objective_derivative (x : ℝ) : HasDerivAt objective x x := by
  convert (hasDerivAt_id x).pow 2 |>.div_const 2 using 1
  simp [objective]

@[simp] theorem deriv_objective (x : ℝ) : deriv objective x = x :=
  (objective_derivative x).deriv

theorem objective_minimum (x : ℝ) : 0 ≤ objective x ∧ (objective x = 0 ↔ x = 0) := by
  constructor
  · exact div_nonneg (sq_nonneg x) (by norm_num)
  · simp [objective]

def iterate (step : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => iterate step n - step n * deriv objective (iterate step n)

def baseStep (_ : ℕ) : ℝ := 1 / 2

def changedStep (m n : ℕ) : ℝ :=
  if n = m then 1 / 4 else if n = m + 1 then 2 / 3 else 1 / 2

theorem steps_valid (m n : ℕ) :
    0 < baseStep n ∧ baseStep n < 1 ∧ 0 < changedStep m n ∧ changedStep m n < 1 := by
  unfold baseStep changedStep
  split_ifs <;> norm_num

theorem base_closed (n : ℕ) : iterate baseStep n = (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp [iterate]
  | succ n ih => simp [iterate, deriv_objective, ih, baseStep, pow_succ]; ring

theorem changed_closed (m n : ℕ) :
    iterate (changedStep m) n =
      if n = m + 1 then (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ n else (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
    simp only [iterate, deriv_objective, ih]
    by_cases h0 : n = m
    · have h1 : n ≠ m + 1 := by omega
      simp [changedStep, h0, h1, pow_succ]
      ring
    · by_cases h1 : n = m + 1
      · have h2 : n + 1 ≠ m + 1 := by omega
        simp [changedStep, h0, h1, h2, pow_succ]
        ring
      · have h2 : n + 1 ≠ m + 1 := by omega
        simp [changedStep, h0, h1, h2, pow_succ]
        ring

theorem prefix_equal (m n : ℕ) (hn : n ≤ m) :
    iterate (changedStep m) n = iterate baseStep n := by
  rw [changed_closed, base_closed, if_neg (by omega)]

theorem tail_equal (m n : ℕ) (hn : m + 2 ≤ n) :
    iterate (changedStep m) n = iterate baseStep n := by
  rw [changed_closed, base_closed, if_neg (by omega)]

def error (x : ℕ → ℝ) (n : ℕ) : ℝ := |x n - 0|

theorem error_gap (m : ℕ) :
    error (iterate (changedStep m)) (m + 1) - error (iterate baseStep) (m + 1) =
      (1 / 2 : ℝ) ^ (m + 2) := by
  have hp : 0 < (1 / 2 : ℝ) ^ (m + 1) := pow_pos (by norm_num) _
  simp only [error, sub_zero]
  rw [changed_closed, if_pos rfl, base_closed]
  rw [abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hp), abs_of_pos hp]
  rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
  ring

theorem error_differs (m : ℕ) :
    error (iterate (changedStep m)) (m + 1) ≠ error (iterate baseStep) (m + 1) := by
  have hp : 0 < (1 / 2 : ℝ) ^ (m + 1) := pow_pos (by norm_num) _
  simp only [error, sub_zero]
  rw [changed_closed, if_pos rfl, base_closed]
  rw [abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hp), abs_of_pos hp]
  nlinarith

theorem eventually_equal (m : ℕ) :
    iterate (changedStep m) =ᶠ[atTop] iterate baseStep :=
  eventually_atTop.2 ⟨m + 2, fun n hn => tail_equal m n hn⟩

theorem base_limit : Tendsto (iterate baseStep) atTop (𝓝 0) := by
  have hf : iterate baseStep = fun n => (1 / 2 : ℝ) ^ n := funext base_closed
  rw [hf]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem changed_limit (m : ℕ) : Tendsto (iterate (changedStep m)) atTop (𝓝 0) :=
  base_limit.congr' (eventually_equal m).symm

/-- Standard asymptotic successive-error ratio for convergence to zero. -/
def HasRate (x : ℕ → ℝ) (q : ℝ) : Prop :=
  Tendsto (fun n => error x (n + 1) / error x n) atTop (𝓝 q)

theorem base_ratio (n : ℕ) :
    error (iterate baseStep) (n + 1) / error (iterate baseStep) n = 1 / 2 := by
  have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) _
  simp only [error, sub_zero, base_closed]
  rw [abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)), abs_of_pos hp,
    pow_succ]
  field_simp

theorem base_rate : HasRate (iterate baseStep) (1 / 2) := by
  unfold HasRate
  simpa only [base_ratio] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop _)

theorem changed_rate (m : ℕ) : HasRate (iterate (changedStep m)) (1 / 2) := by
  unfold HasRate
  apply base_rate.congr'
  apply eventually_atTop.2
  refine ⟨m + 2, ?_⟩
  intro n hn
  simp only [error, tail_equal m n hn, tail_equal m (n + 1) (by omega)]

def GradientMethod (f : ℝ → ℝ) (step : ℕ → ℝ) (x : ℕ → ℝ) : Prop :=
  x 0 = 1 ∧ ∀ n, x (n + 1) = x n - step n * deriv f (x n)

theorem iterate_is_gradient (step : ℕ → ℝ) : GradientMethod objective step (iterate step) :=
  ⟨rfl, fun _ => rfl⟩

/-- The source existence claim, strengthened to a discrepancy at any chosen
finite time, followed by exact equality of the trajectories forever. -/
def SeparationClaim : Prop :=
  ∃ f : ℝ → ℝ,
    (∀ z, HasDerivAt f z z) ∧ (∀ z, 0 ≤ f z ∧ (f z = 0 ↔ z = 0)) ∧
    ∀ m : ℕ, ∃ (a b : ℕ → ℝ) (x y : ℕ → ℝ),
      GradientMethod f a x ∧ GradientMethod f b y ∧
      (∀ n, 0 < a n ∧ a n < 1 ∧ 0 < b n ∧ b n < 1) ∧
      Tendsto x atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
      HasRate x (1 / 2) ∧ HasRate y (1 / 2) ∧
      (∀ n, n ≤ m → x n = y n) ∧ error x (m + 1) ≠ error y (m + 1) ∧
      ∀ n, m + 2 ≤ n → x n = y n

theorem conjecture_6090_true : SeparationClaim := by
  refine ⟨objective, objective_derivative, objective_minimum, ?_⟩
  intro m
  refine ⟨baseStep, changedStep m, iterate baseStep, iterate (changedStep m),
    iterate_is_gradient _, iterate_is_gradient _, steps_valid m, base_limit,
    changed_limit m, base_rate, changed_rate m, ?_, (error_differs m).symm, ?_⟩
  · intro n hn
    exact (prefix_equal m n hn).symm
  · intro n hn
    exact (tail_equal m n hn).symm

#print axioms conjecture_6090_true
#print axioms objective_derivative
#print axioms changed_closed
#print axioms error_gap
#print axioms changed_rate

end Conjecture6090
