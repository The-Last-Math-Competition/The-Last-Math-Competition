import Std

namespace Tlmc4236

/-- The three nonnegative edge weights of the counterexample triangle. -/
def w01 : Nat := 1
def w02 : Nat := 1
def w12 : Nat := 3

/-- The unique simple cycle uses all three edges. -/
def optimalCycleWeight : Nat := w01 + w12 + w02

/-- Deleting the shortest-path tree `{01,02}` leaves only edge `12`. -/
def minimumResidualEdgeWeight : Nat := w12

/-- The direct tree paths from root `0` beat the two detours. -/
theorem chosen_tree_is_shortest :
    w01 < w02 + w12 ∧ w02 < w01 + w12 := by
  decide

theorem all_weights_nonnegative :
    0 ≤ w01 ∧ 0 ≤ w02 ∧ 0 ≤ w12 := by
  omega

theorem exact_weights :
    optimalCycleWeight = 5 ∧ minimumResidualEdgeWeight = 3 := by
  decide

theorem identity_fails :
    optimalCycleWeight ≠ minimumResidualEdgeWeight := by
  decide

def ResidualIdentity : Prop :=
  ∀ (a b c : Nat),
    a < b + c → b < a + c → a + c + b = c

/-- The universal nonnegative-weight identity is refuted by `(1,1,3)`. -/
theorem conjectured_universal_identity_false : ¬ ResidualIdentity := by
  intro h
  have bad := h w01 w02 w12 (by decide) (by decide)
  simp [w01, w02, w12] at bad

end Tlmc4236
