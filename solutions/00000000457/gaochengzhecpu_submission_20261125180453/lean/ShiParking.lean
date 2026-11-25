import Std

/-! The ordered symmetric difference of two parking words is a list of
exclusive cars. Each entry records its word and carries its label and
preference as payload. The common labels and their preferences are fixed. -/

namespace ShiParking

inductive Side where
  | first
  | second
  deriving DecidableEq

def Side.flip : Side → Side
  | .first => .second
  | .second => .first

def Side.step : Side → Int
  | .first => -1
  | .second => 1

theorem Side.flip_flip (side : Side) : side.flip.flip = side := by
  cases side <;> rfl

theorem Side.flip_step (side : Side) : side.flip.step = -side.step := by
  cases side <;> decide

theorem Side.step_le_one (side : Side) : side.step ≤ 1 := by
  cases side <;> decide

def surplus : List (Side × α) → Int
  | [] => 0
  | (side, _) :: rest => side.step + surplus rest

def cars (word : Side) : List (Side × α) → Nat
  | [] => 0
  | (side, _) :: rest => (if side = word then 1 else 0) + cars word rest

theorem surplus_eq_cars (entries : List (Side × α)) :
    surplus entries = (cars .second entries : Int) - (cars .first entries : Int) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨side, payload⟩ := entry
      cases side <;> simp [surplus, Side.step, cars] at * <;> omega

theorem cars_total (entries : List (Side × α)) :
    cars .first entries + cars .second entries = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨side, payload⟩ := entry
      cases side <;> simp [cars] <;> omega

/-- Exchange letters until the original running surplus first reaches the goal. -/
def reflect (goal balance : Int) : List (Side × α) → List (Side × α)
  | [] => []
  | (side, payload) :: rest =>
      if balance = goal then (side, payload) :: rest
      else (side.flip, payload) :: reflect goal (balance + side.step) rest

theorem reflect_payload (entries : List (Side × α)) (goal balance : Int) :
    (reflect goal balance entries).map Prod.snd = entries.map Prod.snd := by
  induction entries generalizing balance with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨side, payload⟩ := entry
      by_cases stop : balance = goal <;> simp [reflect, stop, ih]

theorem reflect_inverse (entries : List (Side × α)) (goal balance : Int) :
    reflect (-goal) (-balance) (reflect goal balance entries) = entries := by
  induction entries generalizing balance with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨side, payload⟩ := entry
      by_cases stop : balance = goal
      · simp [reflect, stop]
      · have inverseStop : -balance ≠ -goal := by omega
        have nextBalance : -balance + side.flip.step = -(balance + side.step) := by
          rw [Side.flip_step]
          omega
        simp only [reflect, stop, inverseStop, if_false, Side.flip_flip, nextBalance, ih]

theorem reflect_surplus (entries : List (Side × α)) (goal balance : Int)
    (below : balance ≤ goal) (reaches : goal ≤ balance + surplus entries) :
    surplus (reflect goal balance entries) = surplus entries - 2 * (goal - balance) := by
  induction entries generalizing balance with
  | nil =>
      change goal ≤ balance + 0 at reaches
      change 0 = 0 - 2 * (goal - balance)
      omega
  | cons entry rest ih =>
      obtain ⟨side, payload⟩ := entry
      by_cases stop : balance = goal
      · simp [reflect, stop]
      · have nextBelow : balance + side.step ≤ goal := by
          have stepBound := side.step_le_one
          omega
        have nextReaches : goal ≤ balance + side.step + surplus rest := by
          change goal ≤ balance + (side.step + surplus rest) at reaches
          omega
        simp only [reflect, stop, if_false, surplus, Side.flip_step,
          ih _ nextBelow nextReaches]
        omega

def exchange (entries : List (Side × α)) : List (Side × α) := reflect 1 0 entries

theorem exchange_balances (entries : List (Side × α))
    (imbalance : cars .second entries = cars .first entries + 2) :
    cars .second (exchange entries) = cars .first (exchange entries) := by
  have original := surplus_eq_cars entries
  have total : surplus entries = 2 := by omega
  have reached : 1 ≤ 0 + surplus entries := by omega
  have result := reflect_surplus entries 1 0 (by decide) reached
  have balanced := surplus_eq_cars (exchange entries)
  change surplus (exchange entries) = surplus entries - 2 * (1 - 0) at result
  omega

/-- The first positive crossing gives an injection to balanced exclusive words.
The preferred spot and label of each moved car remain attached to it. -/
theorem exchange_certificate (entries : List (Side × α))
    (imbalance : cars .second entries = cars .first entries + 2) :
    cars .second (exchange entries) = cars .first (exchange entries) ∧
    (exchange entries).map Prod.snd = entries.map Prod.snd ∧
    reflect (-1) 0 (exchange entries) = entries ∧
    exchange entries ≠ [] := by
  refine ⟨exchange_balances entries imbalance, reflect_payload entries 1 0, ?_, ?_⟩
  · simpa only [exchange, Int.neg_zero] using reflect_inverse entries 1 0
  · intro empty
    have labels := reflect_payload entries 1 0
    change (exchange entries).map Prod.snd = entries.map Prod.snd at labels
    have sameLength := congrArg List.length labels
    have originalLength : entries.length = 0 := by simpa [empty] using sameLength.symm
    have nil : entries = [] := List.length_eq_zero_iff.mp originalLength
    simp [nil, cars] at imbalance

/-- With the common labels restored, relative sizes `k - 1` and `k + 1`
become exactly `k` in both output parking words. -/
theorem exchange_parking_sizes (entries : List (Side × α)) (common k : Nat)
    (firstSize : common + cars .first entries + 1 = k)
    (secondSize : common + cars .second entries = k + 1) :
    common + cars .first (exchange entries) = k ∧
    common + cars .second (exchange entries) = k := by
  have imbalance : cars .second entries = cars .first entries + 2 := by omega
  obtain ⟨balanced, payload, _, _⟩ := exchange_certificate entries imbalance
  have lengthEquality : (exchange entries).length = entries.length := by
    simpa using congrArg List.length payload
  have totalBefore := cars_total entries
  have totalAfter := cars_total (exchange entries)
  constructor <;> omega

#print axioms exchange_certificate
#print axioms exchange_parking_sizes

end ShiParking
