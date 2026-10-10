import TLMC214.Growth
import TLMC214.Sequence

namespace TLMC214

/-- The conventional forward third difference of the logarithm of the number
of actual integer partitions. -/
noncomputable def thirdDifference (n : ℕ) : ℝ :=
  partitionLog (n + 3) - 3 * partitionLog (n + 2) +
    3 * partitionLog (n + 1) - partitionLog n

/-- The necessary eventual-negativity assertion in conjecture 00000000214. -/
def EventualNegativity : Prop := ∃ N : ℕ, ∀ n : ℕ, N ≤ n → thirdDifference n < 0

/-- Complete negation of the original necessary eventual assertion. -/
theorem disproof : ¬ EventualNegativity :=
  Sequence214.not_eventually_negative_third partitionLog partitionLog_nonneg
    partitionLog_unbounded partitionLog_no_affine_lower

/-- In fact strictly positive third differences occur arbitrarily far out. -/
theorem positive_arbitrarily_late (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ 0 < thirdDifference n := by
  have h := Sequence214.not_eventually_nonpos_third partitionLog partitionLog_nonneg
    partitionLog_unbounded partitionLog_no_affine_lower
  by_contra hn
  push_neg at hn
  apply h
  exact ⟨N, fun n hN => hn n hN⟩

/-- The standard backward convention gives the same eventual assertion after
shifting the index by three, and is therefore also disproved. -/
theorem backward_disproof :
    ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 3 ≤ n →
      partitionLog n - 3 * partitionLog (n - 1) +
        3 * partitionLog (n - 2) - partitionLog (n - 3) < 0 := by
  rintro ⟨N, hN⟩
  apply disproof
  refine ⟨N, fun n hn => ?_⟩
  have h := hN (n + 3) (by omega) (by omega)
  simpa only [thirdDifference, Nat.add_sub_cancel, show n + 3 - 1 = n + 2 by omega,
    show n + 3 - 2 = n + 1 by omega] using h

end TLMC214
