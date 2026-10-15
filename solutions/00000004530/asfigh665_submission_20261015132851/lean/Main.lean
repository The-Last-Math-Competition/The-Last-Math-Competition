import Std

namespace Conjecture4530

/-- The undamped update of one signed scalar message. -/
def raw (x : Int) : Int := -x

/-- Twice the damping parameter.  The half-damped reset occurs every p steps. -/
def twiceDamping (p n : Nat) : Int :=
  if (n + 1) % p = 0 then 1 else 2

/-- A synchronous message-passing step at time n. -/
def step (p n : Nat) (x : Int) : Int :=
  if (n + 1) % p = 0 then 0 else -x

/-- Exact denominator-cleared convex damping, not a rounded update. -/
theorem damping_identity (p n : Nat) (x : Int) :
    2 * step p n x = (2 - twiceDamping p n) * x + twiceDamping p n * raw x := by
  simp only [step, twiceDamping, raw]
  split <;> omega

/-- All possible damping parameters are 1/2 and 1. -/
theorem damping_values (p n : Nat) :
    twiceDamping p n = 1 ∨ twiceDamping p n = 2 := by
  unfold twiceDamping
  split <;> simp_all

/-- A fixed message is unchanged by every scheduled update. -/
def Fixed (p : Nat) (x : Int) : Prop := ∀ n, step p n x = x

/-- Every individual update has exactly the fixed point 0. -/
theorem step_fixed_iff (p n : Nat) (x : Int) : step p n x = x ↔ x = 0 := by
  unfold step
  split <;> omega

theorem fixed_iff (p : Nat) (x : Int) : Fixed p x ↔ x = 0 := by
  constructor
  · intro h
    exact (step_fixed_iff p 0 x).mp (h 0)
  · intro h n
    exact (step_fixed_iff p n x).mpr h

def trajectory (p : Nat) (x : Int) : Nat → Int
  | 0 => x
  | n + 1 => step p n (trajectory p x n)

/-- After exactly p updates, the scheduled reset has occurred. -/
theorem reaches_zero (p : Nat) (hp : 0 < p) (x : Int) : trajectory p x p = 0 := by
  cases p with
  | zero => omega
  | succ k => simp [trajectory, step]

/-- Zero is preserved by every update. -/
theorem step_zero (p n : Nat) : step p n 0 = 0 := by
  simp [step]

/-- Finite termination is stronger than convergence. -/
theorem stays_zero (p : Nat) (hp : 0 < p) (x : Int) (k : Nat) :
    trajectory p x (p + k) = 0 := by
  induction k with
  | zero => simpa using reaches_zero p hp x
  | succ k ih =>
    simpa [Nat.add_succ, trajectory, ih] using step_zero p (p + k)

/-- Convergence in the integer-valued message space: eventual equality. -/
def Converges (a : Nat → Int) (z : Int) : Prop :=
  ∃ N, ∀ n, N ≤ n → a n = z

theorem convergence (p : Nat) (hp : 0 < p) (x : Int) :
    Converges (trajectory p x) 0 := by
  refine ⟨p, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact stays_zero p hp x k

/-- The explicit schedules are periodic with period p. -/
theorem damping_periodic (p n : Nat) :
    twiceDamping p (n + p) = twiceDamping p n := by
  simp [twiceDamping, Nat.add_assoc, Nat.add_comm, Nat.add_mod]

theorem first_reset (p : Nat) (hp : 0 < p) : twiceDamping p (p - 1) = 1 := by
  have h : p - 1 + 1 = p := by omega
  simp [twiceDamping, h]

theorem before_reset (p n : Nat) (hn : n + 1 < p) : twiceDamping p n = 2 := by
  have h : (n + 1) % p = n + 1 := Nat.mod_eq_of_lt hn
  simp [twiceDamping, h]

/-- Same initial message, different first iterates. -/
theorem separated : trajectory 1 1 1 = 0 ∧ trajectory 2 1 1 = -1 := by
  decide

theorem scalar_separation :
    ∃ p q : Nat, 0 < p ∧ 0 < q ∧
      (∀ x, Fixed p x ↔ Fixed q x) ∧
      (∀ x, Converges (trajectory p x) 0 ∧ Converges (trajectory q x) 0) ∧
      trajectory p 1 1 ≠ trajectory q 1 1 := by
  refine ⟨1, 2, by decide, by decide, ?_, ?_, ?_⟩
  · intro x
    rw [fixed_iff, fixed_iff]
  · intro x
    exact ⟨convergence 1 (by decide) x, convergence 2 (by decide) x⟩
  · decide

/-- Coordinates for the two integer messages (c+d,c-d) on a two-vertex edge.
The coordinate domain is precisely the pairs of messages with equal parity. -/
abbrev State := Int × Int

def messages (s : State) : Int × Int := (s.1 + s.2, s.1 - s.2)

theorem messages_injective (s t : State) (h : messages s = messages t) : s = t := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [messages] at h1 h2
  apply Prod.ext <;> omega

/-- The two vertices synchronously copy the neighbor's message, with damping. -/
def stateStep (p n : Nat) (s : State) : State := (s.1, step p n s.2)

/-- The physical messages obey the usual convex damping rule exactly. -/
theorem message_passing_identity (p n : Nat) (s : State) :
    2 * (messages (stateStep p n s)).1 =
      (2 - twiceDamping p n) * (messages s).1 +
      twiceDamping p n * (messages s).2 ∧
    2 * (messages (stateStep p n s)).2 =
      (2 - twiceDamping p n) * (messages s).2 +
      twiceDamping p n * (messages s).1 := by
  simp only [messages, stateStep, step, twiceDamping]
  split <;> omega

def StateFixed (p : Nat) (s : State) : Prop := ∀ n, stateStep p n s = s

theorem state_fixed_iff (p : Nat) (s : State) : StateFixed p s ↔ s.2 = 0 := by
  constructor
  · intro h
    have hd := congrArg Prod.snd (h 0)
    exact (step_fixed_iff p 0 s.2).mp hd
  · intro h n
    apply Prod.ext
    · rfl
    · exact (step_fixed_iff p n s.2).mpr h

/-- Exact synchronous iterations in coordinates. -/
def stateTrajectory (p : Nat) (s : State) (n : Nat) : State :=
  (s.1, trajectory p s.2 n)

theorem initial_state (p : Nat) (s : State) : stateTrajectory p s 0 = s := by
  rfl

theorem trajectory_recurrence (p n : Nat) (s : State) :
    stateTrajectory p s (n + 1) = stateStep p n (stateTrajectory p s n) := by
  rfl

/-- Every initial state reaches consensus in at most p synchronous updates. -/
theorem consensus (p : Nat) (hp : 0 < p) (s : State) (n : Nat) (hn : p ≤ n) :
    stateTrajectory p s n = (s.1, 0) ∧
    messages (stateTrajectory p s n) = (s.1, s.1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := stays_zero p hp s.2 k
  simp [stateTrajectory, h, messages]

/-- The fixed-point sets coincide, all trajectories converge, but the
trajectories from the same messages (1,-1) are different. -/
theorem conjecture4530 :
    ∃ p q : Nat, 0 < p ∧ 0 < q ∧
      (∀ s, StateFixed p s ↔ StateFixed q s) ∧
      (∀ s, ∃ N, ∀ n, N ≤ n →
        stateTrajectory p s n = (s.1, 0) ∧
        stateTrajectory q s n = (s.1, 0)) ∧
      messages (stateTrajectory p (0, 1) 1) ≠
        messages (stateTrajectory q (0, 1) 1) := by
  refine ⟨1, 2, by decide, by decide, ?_, ?_, ?_⟩
  · intro s
    rw [state_fixed_iff, state_fixed_iff]
  · intro s
    refine ⟨2, ?_⟩
    intro n hn
    exact ⟨(consensus 1 (by decide) s n (by omega)).1,
      (consensus 2 (by decide) s n hn).1⟩
  · decide

#print axioms conjecture4530
#print axioms message_passing_identity
#print axioms consensus
#print axioms damping_periodic
#print axioms first_reset
#print axioms before_reset

end Conjecture4530
