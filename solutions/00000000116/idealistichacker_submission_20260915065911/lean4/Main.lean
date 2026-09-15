import Std

/-!
Conjecture 00000000116: a bijection of the natural numbers whose absolute
 displacement is always prime or zero. The identity already solves the stated
problem. We also give a nonidentity involution exchanging 1 and 3.
No Mathlib dependency is used.
-/

set_option autoImplicit false

namespace Conjecture00000000116

/-- A natural number at least two whose positive divisors are one or itself. -/
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, 0 < d → d ∣ p → d = 1 ∨ d = p

/-- Absolute difference, using both directions of truncated subtraction. -/
def absDiff (a b : Nat) : Nat := (a - b) + (b - a)

/-- Injectivity and surjectivity, without requiring a separate function library. -/
def IsBijection (f : Nat → Nat) : Prop :=
  (∀ a b : Nat, f a = f b → a = b) ∧
  (∀ b : Nat, ∃ a : Nat, f a = b)

/-- The disjunction is exactly membership in the set of primes union {0}. -/
def AllowedDisplacements (f : Nat → Nat) : Prop :=
  ∀ n : Nat, Prime (absDiff (f n) n) ∨ absDiff (f n) n = 0

/-- An elementary subtraction lemma, proved by induction to keep the
dependency audit empty even for the absolute-difference bridge. -/
private theorem sub_zero_of_le (a b : Nat) (h : a ≤ b) : a - b = 0 := by
  induction a generalizing b with
  | zero => exact Nat.zero_sub b
  | succ a ih =>
    cases b with
    | zero => exact False.elim (Nat.not_succ_le_zero a h)
    | succ b =>
      exact (Nat.succ_sub_succ_eq_sub a b).trans (ih b (Nat.le_of_succ_le_succ h))

/-- This is the usual piecewise definition of absolute difference. -/
theorem absDiff_piecewise (a b : Nat) :
    absDiff a b = if a ≤ b then b - a else a - b := by
  by_cases h : a ≤ b
  · unfold absDiff
    rw [if_pos h, sub_zero_of_le a b h, Nat.zero_add]
  · have hba : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge h)
    unfold absDiff
    rw [if_neg h, sub_zero_of_le b a hba, Nat.add_zero]

theorem absDiff_self (n : Nat) : absDiff n n = 0 := by
  exact congrArg (fun x : Nat => x + x) (Nat.sub_self n)

theorem prime_two : Prime 2 := by
  constructor
  · exact Nat.le_refl 2
  · intro d hd hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hle : d ≤ 2 := by
      cases k with
      | zero =>
        have hbad : 2 = 0 := hk
        contradiction
      | succ k =>
        calc
          d ≤ d * (k + 1) := Nat.le_mul_of_pos_right d (Nat.zero_lt_succ k)
          _ = 2 := hk.symm
    cases d with
    | zero => exact False.elim (Nat.lt_irrefl 0 hd)
    | succ d =>
      cases d with
      | zero => exact Or.inl rfl
      | succ d =>
        have hd0 : d ≤ 0 := Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hle)
        have heq : d = 0 := Nat.eq_zero_of_le_zero hd0
        subst d
        exact Or.inr rfl

/-- An independent, minimal proof: zero displacement is explicitly allowed. -/
theorem identity_solution :
    ∃ f : Nat → Nat, IsBijection f ∧ AllowedDisplacements f := by
  refine ⟨fun n => n, ?_, ?_⟩
  · exact ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩
  · intro n
    exact Or.inr (absDiff_self n)

/-- The only moved elements are 1 and 3. In particular, zero is fixed. -/
def swapOneThree (n : Nat) : Nat :=
  if n = 1 then 3 else if n = 3 then 1 else n

theorem swap_one : swapOneThree 1 = 3 := by rfl

theorem swap_three : swapOneThree 3 = 1 := by rfl

theorem swap_zero : swapOneThree 0 = 0 := by rfl

theorem swap_fixed (n : Nat) (h1 : n ≠ 1) (h3 : n ≠ 3) :
    swapOneThree n = n := by
  unfold swapOneThree
  rw [if_neg h1, if_neg h3]

theorem swap_involutive (n : Nat) :
    swapOneThree (swapOneThree n) = n := by
  by_cases h1 : n = 1
  · subst n
    rfl
  · by_cases h3 : n = 3
    · subst n
      rfl
    · rw [swap_fixed n h1 h3, swap_fixed n h1 h3]

theorem swap_bijection : IsBijection swapOneThree := by
  constructor
  · intro a b h
    calc
      a = swapOneThree (swapOneThree a) := (swap_involutive a).symm
      _ = swapOneThree (swapOneThree b) := congrArg swapOneThree h
      _ = b := swap_involutive b
  · intro b
    exact ⟨swapOneThree b, swap_involutive b⟩

theorem swap_allowed : AllowedDisplacements swapOneThree := by
  intro n
  by_cases h1 : n = 1
  · subst n
    exact Or.inl prime_two
  · by_cases h3 : n = 3
    · subst n
      exact Or.inl prime_two
    · rw [swap_fixed n h1 h3]
      exact Or.inr (absDiff_self n)

theorem swap_nonidentity : ∃ n : Nat, swapOneThree n ≠ n := by
  exact ⟨1, by decide⟩

theorem swap_positive (n : Nat) (hn : 0 < n) : 0 < swapOneThree n := by
  by_cases h1 : n = 1
  · subst n
    decide
  · by_cases h3 : n = 3
    · subst n
      decide
    · rw [swap_fixed n h1 h3]
      exact hn

/-- A nonidentity, self-inverse solution, including its exact pointwise formula. -/
theorem nonidentity_strengthening :
    ∃ f : Nat → Nat,
      IsBijection f ∧ AllowedDisplacements f ∧
      (∀ n : Nat, f (f n) = n) ∧
      f 1 = 3 ∧ f 3 = 1 ∧
      (∀ n : Nat, n ≠ 1 → n ≠ 3 → f n = n) ∧
      (∃ n : Nat, f n ≠ n) := by
  exact ⟨swapOneThree, swap_bijection, swap_allowed, swap_involutive,
    swap_one, swap_three, swap_fixed, swap_nonidentity⟩

/-- The original conjecture, with precisely its stated quantifiers and no
extra assumption. Its witness is the nonidentity transposition above. -/
theorem original_conjecture :
    ∃ f : Nat → Nat,
      IsBijection f ∧
      ∀ n : Nat, Prime (absDiff (f n) n) ∨ absDiff (f n) n = 0 := by
  exact ⟨swapOneThree, swap_bijection, swap_allowed⟩

/-- Covers the convention in which the natural numbers start at one. -/
abbrev PositiveNat := {n : Nat // 0 < n}

def positiveSwap (n : PositiveNat) : PositiveNat :=
  ⟨swapOneThree n.val, swap_positive n.val n.property⟩

theorem positiveSwap_involutive (n : PositiveNat) :
    positiveSwap (positiveSwap n) = n := by
  apply Subtype.ext
  exact swap_involutive n.val

/-- The same nonidentity construction is a bijection of the positive naturals. -/
theorem positive_naturals_solution :
    ∃ f : PositiveNat → PositiveNat,
      (∀ a b : PositiveNat, f a = f b → a = b) ∧
      (∀ b : PositiveNat, ∃ a : PositiveNat, f a = b) ∧
      (∀ n : PositiveNat,
        Prime (absDiff (f n).val n.val) ∨ absDiff (f n).val n.val = 0) ∧
      (∃ n : PositiveNat, f n ≠ n) := by
  refine ⟨positiveSwap, ?_, ?_, ?_, ?_⟩
  · intro a b h
    calc
      a = positiveSwap (positiveSwap a) := (positiveSwap_involutive a).symm
      _ = positiveSwap (positiveSwap b) := congrArg positiveSwap h
      _ = b := positiveSwap_involutive b
  · intro b
    exact ⟨positiveSwap b, positiveSwap_involutive b⟩
  · intro n
    exact swap_allowed n.val
  · refine ⟨⟨1, by decide⟩, ?_⟩
    intro h
    have hval : swapOneThree 1 = 1 := congrArg Subtype.val h
    have hne : swapOneThree 1 ≠ 1 := by decide
    exact hne hval

end Conjecture00000000116
