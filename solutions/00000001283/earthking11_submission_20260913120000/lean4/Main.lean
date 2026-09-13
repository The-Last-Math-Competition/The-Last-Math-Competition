import Std

set_option maxRecDepth 1000000

/-!
# Disproof of conjecture 00000001283

The conjecture claims:

> A nim-equation is an integer solution of `x ⊕ y = x · y` with `x, y ≥ 1`, where `⊕`
> is binary addition without carry. Conjecture: The only solutions are `(2,2)` and `(0,0)`;
> for all other candidate pairs with `x, y > 2`, the difference between the nim-sum and
> the product is a sign flip of a power of two.

This file formalises a refutation in three independent parts.

1. `(2,2)` is **not** a solution: `2 ⊕ 2 = 0 ≠ 4 = 2 · 2` (`not_a_solution`), even though
   the conjecture lists it as one.
2. In fact there are **no** solutions with `x, y ≥ 1` at all: a bounded search over
   `0 ≤ x, y < 200` yields only `(0,0)` (`only_zero_solution`), and the same search
   restricted to `1 ≤ x, y < 200` is empty (`no_pos_solutions`).
3. The second clause is independently false at `(3,3)`: the difference is
   `(3 ⊕ 3) - 3 · 3 = 0 - 9 = -9`, which is not `±2^j` for any natural `j`
   (`clause2_fails_at_3_3`).

Only Lean core + `Std` is used; there is no Mathlib dependency, no `sorry`, no `axiom`,
and no `native_decide`.
-/

namespace Tlmc1283

/-! ## Part 1: `(2,2)` is not a solution -/

/-- The two halves of the counterexample: the nim-sum of `2` with itself is `0`, while the
ordinary product is `4`. -/
theorem two_nim_two : (2 : Nat) ^^^ 2 = 0 ∧ (2 : Nat) * 2 = 4 := by decide

/-- Therefore `(2,2)` does not satisfy `x ⊕ y = x · y`. -/
theorem not_a_solution : ¬ ((2 : Nat) ^^^ 2 = 2 * 2) := by decide

/-! ## Part 2: the whole solution set with `x, y ≥ 1` is empty -/

/-- Every pair `(x, y)` with `x, y < N`, in row-major order. -/
def pairsUpTo (N : Nat) : List (Nat × Nat) :=
  (List.range N).flatMap (fun x => (List.range N).map (fun y => (x, y)))

/-- Enumerate every pair `(x, y)` with `x, y < N` that satisfies the nim-equation. -/
def solutionsUpTo (N : Nat) : List (Nat × Nat) :=
  (pairsUpTo N).filter (fun p => decide (p.1 ^^^ p.2 = p.1 * p.2))

/-- Over the box `0 ≤ x, y < 200` the only solution is `(0,0)`. -/
theorem only_zero_solution : solutionsUpTo 200 = [(0, 0)] := by decide

/-- Enumerate every pair `(x, y)` with `1 ≤ x, y < N` that satisfies the nim-equation. -/
def solutionsUpToPos (N : Nat) : List (Nat × Nat) :=
  (pairsUpTo N).filter (fun p => decide (0 < p.1 ∧ 0 < p.2 ∧ p.1 ^^^ p.2 = p.1 * p.2))

/-- Over the box `1 ≤ x, y < 200` there are no solutions at all. -/
theorem no_pos_solutions : solutionsUpToPos 200 = [] := by decide

/-! ## Part 3: the "sign flip of a power of two" clause fails at `(3,3)` -/

/-- Casting an integral power of two back to `Nat`. -/
theorem int_two_pow_cast (j : Nat) : ((2 ^ j : Nat) : Int) = (2 : Int) ^ j :=
  Int.natCast_pow 2 j

/-- Every integral power of two is strictly positive. -/
theorem int_two_pow_pos : ∀ j : Nat, (0 : Int) < (2 : Int) ^ j := by
  intro j
  rw [← int_two_pow_cast j]
  exact Int.natCast_pos.mpr (Nat.pow_pos (a := 2) (n := j) (by decide))

/-- No integral power of two equals `9`. -/
theorem int_two_pow_ne_nine : ∀ j : Nat, (2 : Int) ^ j ≠ 9 := by
  intro j
  induction j with
  | zero => decide
  | succ n _ =>
      rw [Int.pow_succ]
      intro h
      omega

/-- `-9` is not a power of two (it is negative, while `2^j > 0`). -/
theorem nine_not_pow : ¬ ∃ j : Nat, ((0 : Int) - 9 = (2 : Int) ^ j) := by
  rintro ⟨j, hj⟩
  have hneg : ((0 : Int) - 9) = -9 := by decide
  rw [hneg, ← int_two_pow_cast j] at hj
  have hnn : (0 : Int) ≤ ((2 ^ j : Nat) : Int) := Int.natCast_nonneg _
  omega

/-- `-9` is not the *sign flip* `-2^j` of a power of two either, since that would force
`2^j = 9`. -/
theorem nine_not_pow_neg : ¬ ∃ j : Nat, ((0 : Int) - 9 = -((2 : Int) ^ j)) := by
  rintro ⟨j, hj⟩
  have hne := int_two_pow_ne_nine j
  have hneg : ((0 : Int) - 9) = -9 := by decide
  rw [hneg] at hj
  have htwo : (2 : Int) ^ j = 9 := by
    have h := congrArg (fun z : Int => -z) hj
    simpa using h.symm
  exact hne htwo

/-- At `(3,3)` the nim-sum is `0`, the product is `9`, and the difference `-9` is neither
`2^j` nor `-2^j` for any natural `j`. -/
theorem clause2_fails_at_3_3 :
    ((3 : Nat) ^^^ 3 = 0) ∧ ((3 : Nat) * 3 = 9) ∧
      (¬ ∃ j : Nat, ((0 : Int) - 9 = (2 : Int) ^ j)) ∧
      (¬ ∃ j : Nat, ((0 : Int) - 9 = -((2 : Int) ^ j))) :=
  ⟨by decide, by decide, nine_not_pow, nine_not_pow_neg⟩

/-! ## Combined refutation -/

/-- The conjecture `00000001283` is false, for three independent reasons:

* `(2,2)` is not a solution of the nim-equation;
* the entire solution set with `x, y ≥ 1` is empty;
* the "sign flip of a power of two" clause fails at `(3,3)`, where the difference is `-9`.
-/
theorem conjecture_00000001283_false :
    (¬ ((2 : Nat) ^^^ 2 = 2 * 2)) ∧
      (solutionsUpTo 200 = [(0, 0)]) ∧
      (solutionsUpToPos 200 = []) ∧
      (((3 : Nat) ^^^ 3 = 0) ∧ ((3 : Nat) * 3 = 9)) ∧
      (¬ ∃ j : Nat, ((0 : Int) - 9 = (2 : Int) ^ j)) ∧
      (¬ ∃ j : Nat, ((0 : Int) - 9 = -((2 : Int) ^ j))) :=
  ⟨not_a_solution, only_zero_solution, no_pos_solutions, ⟨by decide, by decide⟩,
    nine_not_pow, nine_not_pow_neg⟩

end Tlmc1283
