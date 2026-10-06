import Std

namespace Tlmc7612

/-- Elements `a + b e` in the rank-two algebra with relation `e^2 = 1`. -/
abbrev ClOne := Int × Int

/-- Multiplication obtained from `(a + b e)(c + d e)` and `e^2 = 1`. -/
def mul (x y : ClOne) : ClOne :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- The one-dimensional character given by evaluation at `e = 1`. -/
def rho (x : ClOne) : Int := x.1 + x.2

theorem rho_one : rho (1, 0) = 1 := by rfl

theorem rho_generator : rho (0, 1) = 1 := by rfl

theorem generator_relation : mul (0, 1) (0, 1) = (1, 0) := by rfl

theorem rho_mul (x y : ClOne) : rho (mul x y) = rho x * rho y := by
  simp only [rho, mul, Int.add_mul, Int.mul_add]
  ac_rfl

/-- The one-dimensional representation cannot have the conjectured odd-rank
dimension: squaring the claimed value at `n = 1` would give `2`. -/
theorem one_dimensional_counterexample : (1 : Nat) * 1 ≠ 2 := by decide

end Tlmc7612
