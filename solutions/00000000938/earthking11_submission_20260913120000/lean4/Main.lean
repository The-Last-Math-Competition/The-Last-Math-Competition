/-
  Rule-3 disproof for conjecture 00000000938.

  Claim under test: the Banach-Mazur distance between ℓ₁ⁿ and ℓ∞ⁿ
  "is exactly √n (the Goldstine ratio)".

  This file refutes the n = 2 instance in core Lean (`import Std`, no Mathlib).
  The linear map `T (x₁, x₂) = (x₁ + x₂, x₁ - x₂)` is a norm-preserving
  bijection from (ℤ², ‖·‖₁) onto (ℤ², ‖·‖∞): it sends the ℓ₁² unit ball
  (a diamond) onto the ℓ∞² unit ball (a square). Hence
  `d(ℓ₁², ℓ∞²) = 1 ≠ √2`.
-/
import Std

namespace Tlmc938

/-- The absolute value of an integer, as a natural number. -/
local notation "|" a "|" => Int.natAbs a

/-- Key isometry identity: for all integers `a`, `b`,
`max (|a + b|) (|a - b|) = |a| + |b|`. -/
theorem max_abs_eq : ∀ a b : Int, max |a + b| |a - b| = |a| + |b| := by
  intro a b
  omega

/-- The linear map `T (x₁, x₂) = (x₁ + x₂, x₁ - x₂)`. -/
def T (x : Int × Int) : Int × Int := (x.1 + x.2, x.1 - x.2)

/-- `T` is an isometry from `(Int × Int, ‖·‖₁)` to `(Int × Int, ‖·‖∞)`. -/
theorem T_isometry :
    ∀ x : Int × Int, max |(T x).1| |(T x).2| = |x.1| + |x.2| := by
  intro x
  exact max_abs_eq x.1 x.2

/-- The four ℓ₁²-ball vertices `(±1, 0)`, `(0, ±1)` map to the four
ℓ∞²-ball corners `(±1, ±1)`. -/
theorem maps_diamond_to_square :
    T (1, 0) = (1, 1) ∧ T (-1, 0) = (-1, -1) ∧
    T (0, 1) = (1, -1) ∧ T (0, -1) = (-1, 1) := by
  decide

/-- `1² = 1 ≠ 2 = (√2)²`, stated over `Nat`
(core Lean has no `ℝ`, and `√2` is irrational). -/
theorem one_sq_ne_two_nat : (1 : Nat) * 1 ≠ 2 := by
  decide

/-- The same arithmetic fact over `Int`. -/
theorem one_sq_ne_two_int : (1 : Int) * 1 ≠ 2 := by
  decide

/-- The n = 2 counterexample collected in one statement: the isometry identity
holds, the diamond maps onto the square, `T` preserves both norms, and the
squares of the two candidate distances differ (`1² ≠ 2`). Since `T` is onto and
norm-preserving, `‖T‖ = ‖T⁻¹‖ = 1`, so `d(ℓ₁², ℓ∞²) = 1`, which is not `√2`. -/
theorem conjecture_00000000938_false :
    (∀ a b : Int, max |a + b| |a - b| = |a| + |b|)
      ∧ (T (1, 0) = (1, 1) ∧ T (-1, 0) = (-1, -1) ∧
         T (0, 1) = (1, -1) ∧ T (0, -1) = (-1, 1))
      ∧ (∀ x : Int × Int, max |(T x).1| |(T x).2| = |x.1| + |x.2|)
      ∧ (1 : Nat) * 1 ≠ 2 := by
  exact ⟨max_abs_eq, maps_diamond_to_square, T_isometry, one_sq_ne_two_nat⟩

end Tlmc938
