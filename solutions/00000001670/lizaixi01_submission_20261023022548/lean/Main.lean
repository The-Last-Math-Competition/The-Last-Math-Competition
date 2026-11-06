import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The explicit numerical necessary clauses in TLMC 00000001670.
No random-graph asymptotic or identification of a genuine DMS constant is assumed.
The functions below are Mathlib's real square root, inverse tangent, and pi. -/
namespace TLMC1670

noncomputable def closedForm : ℝ := (2 / Real.pi) * Real.arctan (Real.sqrt 2)

/-- A deliberately generous interpretation of rounding to the printed three decimals. -/
def Rounded0918 (P : ℝ) : Prop := |P - (459 / 500 : ℝ)| ≤ 1 / 2000

theorem sqrt_two_lt_sqrt_three : Real.sqrt 2 < Real.sqrt 3 := by
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem arctan_sqrt_two_lt : Real.arctan (Real.sqrt 2) < Real.pi / 3 := by
  calc
    Real.arctan (Real.sqrt 2) < Real.arctan (Real.sqrt 3) :=
      Real.arctan_strictMono sqrt_two_lt_sqrt_three
    _ = Real.pi / 3 := Real.arctan_sqrt_three

theorem closedForm_lt_two_thirds : closedForm < (2 / 3 : ℝ) := by
  have hpos : (0 : ℝ) < 2 / Real.pi := div_pos (by norm_num) Real.pi_pos
  calc
    closedForm < (2 / Real.pi) * (Real.pi / 3) :=
      mul_lt_mul_of_pos_left arctan_sqrt_two_lt hpos
    _ = (2 / 3 : ℝ) := by field_simp

theorem exact_decimal_gap : (1 / 4 : ℝ) < 459 / 500 - closedForm := by
  linarith [closedForm_lt_two_thirds]

theorem rounded_lower_bound (P : ℝ) (h : Rounded0918 P) : (367 / 400 : ℝ) ≤ P := by
  have hh := (abs_le.mp h).1
  linarith

theorem rounded_gap (P : ℝ) (h : Rounded0918 P) : (1 / 4 : ℝ) < P - closedForm := by
  have hlow := rounded_lower_bound P h
  linarith [closedForm_lt_two_thirds]

/-- The exact characterization printed in the source is impossible for every real P. -/
theorem no_exact_characterization (P : ℝ) :
    ¬ (P = (459 / 500 : ℝ) ∧ P = closedForm) := by
  rintro ⟨hdecimal, hform⟩
  linarith [exact_decimal_gap]

/-- Even the more permissive three-decimal rounding interpretation is impossible. -/
theorem no_rounded_characterization (P : ℝ) : ¬ (Rounded0918 P ∧ P = closedForm) := by
  rintro ⟨hround, hform⟩
  have := rounded_gap P hround
  linarith

theorem no_sequence_of_constants :
    ¬ ∃ P : ℕ → ℝ, P 3 = (459 / 500 : ℝ) ∧ P 3 = closedForm := by
  rintro ⟨P, h⟩
  exact no_exact_characterization (P 3) h

theorem no_rounded_sequence_of_constants :
    ¬ ∃ P : ℕ → ℝ, Rounded0918 (P 3) ∧ P 3 = closedForm := by
  rintro ⟨P, h⟩
  exact no_rounded_characterization (P 3) h

end TLMC1670
