import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section
namespace MixedFreeMoment
-- Coordinates on the full two-letter Fock basis, with no truncation.
abbrev Coeff := List Bool → ℝ
def vacuum : Coeff := fun w => if w = [] then 1 else 0
def creation (i : Bool) (f : Coeff) : Coeff
  | [] => 0
  | b :: w => if b = i then f w else 0
def annihilation (i : Bool) (f : Coeff) : Coeff := fun w => f (i :: w)
def raw (f : Coeff) : Coeff := fun w =>
  creation false f w + annihilation false f w +
  creation true f w + annihilation true f w
def scaled (a : ℝ) (f : Coeff) : Coeff := fun w => a * raw f w
def power (T : Coeff → Coeff) : ℕ → Coeff
  | 0 => vacuum
  | n + 1 => T (power T n)
def moment (a : ℝ) (n : ℕ) : ℝ := power (scaled a) n []

theorem raw_scalar (c : ℝ) (f : Coeff) :
    raw (fun w => c * f w) = fun w => c * raw f w := by
  funext w
  cases w with
  | nil => simp [raw, creation, annihilation]; ring
  | cons b w => cases b <;> simp [raw, creation, annihilation] <;> ring

theorem power_scaled (a : ℝ) (n : ℕ) :
    power (scaled a) n = fun w => a ^ n * power raw n w := by
  induction n with
  | zero => simp [power]
  | succ n ih =>
    rw [power, ih]
    change (fun w => a * raw (fun w => a ^ n * power raw n w) w) = _
    rw [raw_scalar]
    funext w
    simp only [power, pow_succ]
    ring

theorem raw_second : power raw 2 [] = 2 := by
  norm_num [power, raw, creation, annihilation, vacuum, List.cons_ne_nil]
theorem raw_fourth : power raw 4 [] = 8 := by
  norm_num [power, raw, creation, annihilation, vacuum, List.cons_ne_nil]
theorem raw_sixth : power raw 6 [] = 40 := by
  norm_num [power, raw, creation, annihilation, vacuum, List.cons_ne_nil]

def coefficient : ℝ := 1 / (2 * Real.sqrt 2)
theorem coefficient_sq : coefficient ^ 2 = (1 / 8 : ℝ) := by
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  unfold coefficient
  field_simp
  nlinarith

theorem second_moment : moment coefficient 2 = (1 / 4 : ℝ) := by
  simp only [moment, power_scaled, raw_second, coefficient_sq]
  norm_num
theorem fourth_moment : moment coefficient 4 = (1 / 8 : ℝ) := by
  have h : coefficient ^ 4 = (1 / 64 : ℝ) := by
    nlinarith [coefficient_sq, sq_nonneg (coefficient ^ 2 - 1/8)]
  simp only [moment, power_scaled, raw_fourth, h]
  norm_num
theorem sixth_moment : moment coefficient 6 = (5 / 64 : ℝ) := by
  have h : coefficient ^ 6 = (1 / 512 : ℝ) := by
    calc
      coefficient ^ 6 = (coefficient ^ 2) ^ 3 := by ring
      _ = 1 / 512 := by rw [coefficient_sq]; norm_num
  simp only [moment, power_scaled, raw_sixth, h]
  norm_num
theorem negative_difference :
    moment coefficient 6 - moment coefficient 4 = -(3 / 64 : ℝ) ∧
    moment coefficient 6 - moment coefficient 4 < 0 := by
  rw [sixth_moment, fourth_moment]
  norm_num
#print axioms power_scaled
#print axioms raw_sixth
#print axioms coefficient_sq
#print axioms negative_difference
end MixedFreeMoment
