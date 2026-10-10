import Mathlib.Topology.Constructions

import Mathlib.Tactic

namespace ShiftCounterexample
instance : TopologicalSpace Bool := ⊥
abbrev Config := ℤ → Bool

def shift (x : Config) : Config := fun i => x (i + 1)
def reverseShift (x : Config) : Config := fun i => x (i - 1)

theorem shift_continuous : Continuous shift :=
  continuous_pi fun i => continuous_apply (i + 1)

theorem shift_surjective : Function.Surjective shift := by
  intro x
  refine ⟨reverseShift x, ?_⟩
  funext i
  simp [shift, reverseShift]

theorem shift_commutes : Function.Commute shift shift := fun _ => rfl

def localRule (b : Bool) : Bool := b

theorem localRule_permutative : Function.Bijective localRule := Function.bijective_id

theorem local_realization (x : Config) (i : ℤ) : shift x i = localRule (x (i + 1)) := rfl

theorem iterate_shift (n : ℕ) (x : Config) (i : ℤ) :
    (shift^[n]) x i = x (i + (n : ℤ)) := by
  induction n generalizing x i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', shift, ih]
    congr 1
    omega

def flipAt (x : Config) (j : ℤ) : Config := fun i => if i = j then !(x i) else x i

theorem flipped_difference (x : Config) (j i : ℤ) : flipAt x j i ≠ x i ↔ i = j := by
  by_cases h : i = j
  · subst i; cases hbit : x j <;> simp [flipAt, hbit]
  · simp [flipAt, h]

theorem damage_location (x : Config) (j i : ℤ) (n : ℕ) :
    (shift^[n]) (flipAt x j) i ≠ (shift^[n]) x i ↔ i = j - (n : ℤ) := by
  rw [iterate_shift, iterate_shift, flipped_difference]
  omega

-- Half-line directional front: initial agreement on [j,infinity)
-- moves to agreement on [j-n,infinity), and this boundary is sharp.
theorem halfline_agreement (x y : Config) (j : ℤ) (n : ℕ)
    (h : ∀ i, j ≤ i → x i = y i) :
    ∀ i, j - (n : ℤ) ≤ i → (shift^[n]) x i = (shift^[n]) y i := by
  intro i hi
  rw [iterate_shift, iterate_shift]
  exact h (i + (n : ℤ)) (by omega)

theorem front_sharp (x : Config) (j : ℤ) (n : ℕ) :
    (∀ i, j ≤ i → flipAt x (j - 1) i = x i) ∧
    (shift^[n]) (flipAt x (j - 1)) (j - 1 - (n : ℤ)) ≠
      (shift^[n]) x (j - 1 - (n : ℤ)) := by
  constructor
  · intro i hi
    simp [flipAt, show i ≠ j - 1 by omega]
  · exact (damage_location x (j - 1) (j - 1 - (n : ℤ)) n).2 rfl

theorem normalized_left_speed (n : ℕ) (hn : 0 < n) : (n : ℝ) / (n : ℝ) = 1 := by
  exact div_self (by exact_mod_cast (Nat.ne_of_gt hn))

theorem counterexample : Continuous shift ∧ Function.Surjective shift ∧
    Function.Commute shift shift ∧ Function.Bijective localRule ∧
    ∀ (x : Config) (j i : ℤ) (n : ℕ),
      ((shift^[n]) (flipAt x j) i ≠ (shift^[n]) x i ↔ i = j - (n : ℤ)) :=
  ⟨shift_continuous, shift_surjective, shift_commutes, localRule_permutative, damage_location⟩

#print axioms counterexample
#print axioms halfline_agreement
#print axioms front_sharp
#print axioms normalized_left_speed
end ShiftCounterexample
