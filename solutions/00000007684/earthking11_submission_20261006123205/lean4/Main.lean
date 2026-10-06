import Std

namespace Tlmc7684

abbrev Coefficients := Nat → Int

/-- Normalized coefficient equations for `f((1/2)z) = f(z)` together with
the boundary equation.  Since `(1/2)^n - 1` is nonzero for `n > 0`, the raw
coefficient equation is equivalent to `c n = 0` there. -/
def IsZeroEigenSolution (c : Coefficients) : Prop :=
  (∀ n, 0 < n → c n = 0) ∧ c 0 = 0

def zeroCoefficients : Coefficients := fun _ => 0

theorem zero_is_solution : IsZeroEigenSolution zeroCoefficients := by
  constructor <;> simp [zeroCoefficients]

theorem solution_coefficients_vanish (c : Coefficients)
    (hc : IsZeroEigenSolution c) (n : Nat) : c n = 0 := by
  rcases hc with ⟨hpos, hzero⟩
  cases n with
  | zero => exact hzero
  | succ n => exact hpos (n + 1) (by omega)

/-- The zero function is the unique analytic coefficient solution at
`lambda = 0` after imposing `f(1) = 0`. -/
theorem unique_zero_solution (c : Coefficients)
    (hc : IsZeroEigenSolution c) : c = zeroCoefficients := by
  funext n
  exact solution_coefficients_vanish c hc n

theorem no_nonzero_solution :
    ¬ ∃ c : Coefficients, IsZeroEigenSolution c ∧ c ≠ zeroCoefficients := by
  rintro ⟨c, hc, hne⟩
  exact hne (unique_zero_solution c hc)

end Tlmc7684
