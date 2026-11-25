/-
  Conjecture 00000004764 — Basic Arithmetic, Power-of-Two Ratios, and Kreweras Obstructions
  Core Lean 4.19.0 (zero external dependencies)
-/

namespace BooleanFreeConv

/-- `IsSignedPowTwoRatio x y` asserts that `y / x` is an integer power of two `2^e` (`e ∈ ℤ`),
    written multiplicatively over `ℤ` as either `y = 2^k * x` (`e = k ≥ 0`) or
    `2^k * y = x` (`e = -k ≤ 0`). -/
def IsSignedPowTwoRatio (x y : Int) : Prop :=
  (∃ k : Nat, y = (2 : Int) ^ k * x) ∨ (∃ k : Nat, (2 : Int) ^ k * y = x)

/-- Stronger rational-exponent generalization: `y / x = 2^(p / q)` for some `p ∈ ℤ` and
    `q ∈ ℕ` with `q ≥ 1`, written as `y^q = 2^k * x^q` or `2^k * y^q = x^q`. -/
def IsRatPowTwoRatio (x y : Int) : Prop :=
  (∃ k q : Nat, 1 ≤ q ∧ y ^ q = (2 : Int) ^ k * x ^ q) ∨
  (∃ k q : Nat, 1 ≤ q ∧ (2 : Int) ^ k * y ^ q = x ^ q)

theorem int_pow_one (a : Int) : a ^ 1 = a := by
  rw [Int.pow_succ, Int.pow_zero, Int.one_mul]

theorem isRatPowTwoRatio_of_signed {x y : Int} (h : IsSignedPowTwoRatio x y) :
    IsRatPowTwoRatio x y := by
  cases h with
  | inl hpos =>
    rcases hpos with ⟨k, hk⟩
    exact Or.inl ⟨k, 1, Nat.le_refl 1, by rw [int_pow_one, int_pow_one, hk]⟩
  | inr hneg =>
    rcases hneg with ⟨k, hk⟩
    exact Or.inr ⟨k, 1, Nat.le_refl 1, by rw [int_pow_one, int_pow_one, hk]⟩

theorem int_pow2_pos (k : Nat) : (1 : Int) ≤ (2 : Int) ^ k := by
  induction k with
  | zero => decide
  | succ n ih =>
    rw [Int.pow_succ]
    omega

theorem int_pow2_mod_three_cases (k : Nat) :
    ((2 : Int) ^ k) % 3 = 1 ∨ ((2 : Int) ^ k) % 3 = 2 := by
  induction k with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [Int.pow_succ, Int.mul_emod]
    cases ih with
    | inl h1 => rw [h1]; exact Or.inr rfl
    | inr h2 => rw [h2]; exact Or.inl rfl

theorem mod_three_pow_cases {x : Int} (hx : x % 3 = 1 ∨ x % 3 = 2) (q : Nat) :
    (x ^ q) % 3 = 1 ∨ (x ^ q) % 3 = 2 := by
  induction q with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [Int.pow_succ, Int.mul_emod]
    cases ih with
    | inl h1 =>
      cases hx with
      | inl g1 => rw [h1, g1]; exact Or.inl rfl
      | inr g2 => rw [h1, g2]; exact Or.inr rfl
    | inr h2 =>
      cases hx with
      | inl g1 => rw [h2, g1]; exact Or.inr rfl
      | inr g2 => rw [h2, g2]; exact Or.inl rfl

theorem mod_three_pow_zero {y : Int} (hy : y % 3 = 0) {q : Nat} (hq : 1 ≤ q) :
    (y ^ q) % 3 = 0 := by
  cases q with
  | zero => omega
  | succ n =>
    rw [Int.pow_succ, Int.mul_emod, hy]
    simp

/-- 3-adic obstruction: if `3 ∣ y` while `3 ∤ x`, then `(x, y)` is not related by any
    rational (hence also no integer) power of two. -/
theorem not_isRatPowTwoRatio_of_mod_three {x y : Int}
    (hx : x % 3 = 1 ∨ x % 3 = 2) (hy : y % 3 = 0) :
    ¬ IsRatPowTwoRatio x y := by
  intro h
  rcases h with ⟨k, q, hq, heq⟩ | ⟨k, q, hq, heq⟩
  · have hy0 : (y ^ q) % 3 = 0 := mod_three_pow_zero hy hq
    have hrhs : (((2 : Int) ^ k * x ^ q) % 3) ≠ 0 := by
      rw [Int.mul_emod]
      cases int_pow2_mod_three_cases k with
      | inl hk1 =>
        cases mod_three_pow_cases hx q with
        | inl hq1 => rw [hk1, hq1]; decide
        | inr hq2 => rw [hk1, hq2]; decide
      | inr hk2 =>
        cases mod_three_pow_cases hx q with
        | inl hq1 => rw [hk2, hq1]; decide
        | inr hq2 => rw [hk2, hq2]; decide
    rw [heq] at hy0
    exact hrhs hy0
  · have hlhs : (((2 : Int) ^ k * y ^ q) % 3) = 0 := by
      rw [Int.mul_emod, mod_three_pow_zero hy hq]
      simp
    rw [heq] at hlhs
    cases mod_three_pow_cases hx q with
    | inl hq1 => omega
    | inr hq2 => omega

theorem not_isSignedPowTwoRatio_of_mod_three {x y : Int}
    (hx : x % 3 = 1 ∨ x % 3 = 2) (hy : y % 3 = 0) :
    ¬ IsSignedPowTwoRatio x y :=
  fun h => not_isRatPowTwoRatio_of_mod_three hx hy (isRatPowTwoRatio_of_signed h)

theorem int_pow2_mod_five_cases (k : Nat) :
    ((2 : Int) ^ k) % 5 = 1 ∨ ((2 : Int) ^ k) % 5 = 2 ∨
    ((2 : Int) ^ k) % 5 = 4 ∨ ((2 : Int) ^ k) % 5 = 3 := by
  induction k with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [Int.pow_succ, Int.mul_emod]
    rcases ih with h1 | h2 | h4 | h3
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h4]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [h3]; exact Or.inl rfl

theorem mod_five_pow_cases {x : Int}
    (hx : x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 4 ∨ x % 5 = 3) (q : Nat) :
    (x ^ q) % 5 = 1 ∨ (x ^ q) % 5 = 2 ∨ (x ^ q) % 5 = 4 ∨ (x ^ q) % 5 = 3 := by
  induction q with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [Int.pow_succ, Int.mul_emod]
    rcases ih with h1 | h2 | h4 | h3 <;> rcases hx with g1 | g2 | g4 | g3
    · rw [h1, g1]; exact Or.inl rfl
    · rw [h1, g2]; exact Or.inr (Or.inl rfl)
    · rw [h1, g4]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h1, g3]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [h2, g1]; exact Or.inr (Or.inl rfl)
    · rw [h2, g2]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h2, g4]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [h2, g3]; exact Or.inl rfl
    · rw [h4, g1]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h4, g2]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [h4, g4]; exact Or.inl rfl
    · rw [h4, g3]; exact Or.inr (Or.inl rfl)
    · rw [h3, g1]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [h3, g2]; exact Or.inl rfl
    · rw [h3, g4]; exact Or.inr (Or.inl rfl)
    · rw [h3, g3]; exact Or.inr (Or.inr (Or.inl rfl))

theorem mod_five_pow_zero {y : Int} (hy : y % 5 = 0) {q : Nat} (hq : 1 ≤ q) :
    (y ^ q) % 5 = 0 := by
  cases q with
  | zero => omega
  | succ n =>
    rw [Int.pow_succ, Int.mul_emod, hy]
    simp

/-- 5-adic obstruction: if `5 ∣ y` while `5 ∤ x`, then `(x, y)` is not related by any
    rational (hence also no integer) power of two. -/
theorem not_isRatPowTwoRatio_of_mod_five {x y : Int}
    (hx : x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 4 ∨ x % 5 = 3) (hy : y % 5 = 0) :
    ¬ IsRatPowTwoRatio x y := by
  intro h
  rcases h with ⟨k, q, hq, heq⟩ | ⟨k, q, hq, heq⟩
  · have hy0 : (y ^ q) % 5 = 0 := mod_five_pow_zero hy hq
    have hrhs : (((2 : Int) ^ k * x ^ q) % 5) ≠ 0 := by
      rw [Int.mul_emod]
      rcases int_pow2_mod_five_cases k with hk1 | hk2 | hk4 | hk3 <;>
        rcases mod_five_pow_cases hx q with hq1 | hq2 | hq4 | hq3 <;>
        first
        | (rw [hk1, hq1]; decide) | (rw [hk1, hq2]; decide)
        | (rw [hk1, hq4]; decide) | (rw [hk1, hq3]; decide)
        | (rw [hk2, hq1]; decide) | (rw [hk2, hq2]; decide)
        | (rw [hk2, hq4]; decide) | (rw [hk2, hq3]; decide)
        | (rw [hk4, hq1]; decide) | (rw [hk4, hq2]; decide)
        | (rw [hk4, hq4]; decide) | (rw [hk4, hq3]; decide)
        | (rw [hk3, hq1]; decide) | (rw [hk3, hq2]; decide)
        | (rw [hk3, hq4]; decide) | (rw [hk3, hq3]; decide)
    rw [heq] at hy0
    exact hrhs hy0
  · have hlhs : (((2 : Int) ^ k * y ^ q) % 5) = 0 := by
      rw [Int.mul_emod, mod_five_pow_zero hy hq]
      simp
    rw [heq] at hlhs
    rcases mod_five_pow_cases hx q with hq1 | hq2 | hq4 | hq3 <;> omega

theorem not_isSignedPowTwoRatio_of_mod_five {x y : Int}
    (hx : x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 4 ∨ x % 5 = 3) (hy : y % 5 = 0) :
    ¬ IsSignedPowTwoRatio x y :=
  fun h => not_isRatPowTwoRatio_of_mod_five hx hy (isRatPowTwoRatio_of_signed h)

theorem not_isSignedPowTwoRatio_zero_left {y : Int} (hy : y ≠ 0) :
    ¬ IsSignedPowTwoRatio 0 y := by
  intro h
  rcases h with ⟨k, hk⟩ | ⟨k, hk⟩
  · simp at hk
    exact hy hk
  · have hp : (1 : Int) ≤ (2 : Int) ^ k := int_pow2_pos k
    cases Int.mul_eq_zero.mp hk with
    | inl h2 => omega
    | inr hy0 => exact hy hy0

theorem not_isSignedPowTwoRatio_pos_neg {x y : Int} (hx : 0 < x) (hy : y < 0) :
    ¬ IsSignedPowTwoRatio x y := by
  intro h
  rcases h with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hp : (1 : Int) ≤ (2 : Int) ^ k := int_pow2_pos k
    have hnn : 0 ≤ (2 : Int) ^ k * x := Int.mul_nonneg (by omega) (by omega)
    omega
  · have hp : (1 : Int) ≤ (2 : Int) ^ k := int_pow2_pos k
    have hnp : (2 : Int) ^ k * y ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    omega

/-- Factorial on `Nat`, valued in `Int` for exact Kreweras / multinomial ratio identities. -/
def fact : Nat → Int
  | 0 => 1
  | n + 1 => (n + 1 : Int) * fact n

/-- Numerator `n!` of Kreweras' partition-type conversion ratio
    `N_NC(λ) / N_Int(λ) = n! / (k! * (n + 1 - k)!)` for a partition `λ ⊢ n` into `k` blocks. -/
def krewerasNum (n : Nat) : Int := fact n

/-- Denominator `k! * (n + 1 - k)!` of Kreweras' partition-type conversion ratio
    `N_NC(λ) / N_Int(λ)` for a partition `λ ⊢ n` into `k = ℓ(λ)` blocks. -/
def krewerasDen (n k : Nat) : Int := fact k * fact (n + 1 - k)

/-- Low-order Fermat-prime mirage at `n = 4`: for EVERY block count `k ∈ {1, 2, 3, 4}`,
    Kreweras' ratio `N_NC(λ) / N_Int(λ)` is an explicit power of two (`1, 2, 2, 1`). -/
theorem kreweras_order4_all_pow2 :
    IsSignedPowTwoRatio (krewerasDen 4 1) (krewerasNum 4) ∧
    IsSignedPowTwoRatio (krewerasDen 4 2) (krewerasNum 4) ∧
    IsSignedPowTwoRatio (krewerasDen 4 3) (krewerasNum 4) ∧
    IsSignedPowTwoRatio (krewerasDen 4 4) (krewerasNum 4) := by
  refine ⟨Or.inl ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩, Or.inl ⟨1, rfl⟩, Or.inl ⟨0, rfl⟩⟩

/-- Uncentered order `n = 3`, `k = 2` (`λ = (2, 1)`): `N_NC / N_Int = 6 / 4 = 3 / 2`,
    which is neither an integer nor any rational power of two. -/
theorem kreweras_order3_k2_not_pow2 :
    ¬ IsRatPowTwoRatio (krewerasDen 3 2) (krewerasNum 3) := by
  apply not_isRatPowTwoRatio_of_mod_three
  · exact Or.inl rfl
  · rfl

/-- Centered order `n = 5`, `k = 2` (`λ = (3, 2)`): `N_NC / N_Int = 120 / 48 = 5 / 2`,
    which is not any rational or integer power of two. -/
theorem kreweras_order5_k2_not_pow2 :
    ¬ IsRatPowTwoRatio (krewerasDen 5 2) (krewerasNum 5) := by
  apply not_isRatPowTwoRatio_of_mod_five
  · exact Or.inr (Or.inr (Or.inr rfl))
  · rfl

theorem int_mul_pow (a b : Int) : ∀ q : Nat, (a * b) ^ q = a ^ q * b ^ q
  | 0 => by simp
  | q + 1 => by
    rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, int_mul_pow a b q]
    have hcomm : a ^ q * b ^ q * (a * b) = a ^ q * a * (b ^ q * b) := by
      rw [Int.mul_assoc (a ^ q), ← Int.mul_assoc (b ^ q) a b,
          Int.mul_comm (b ^ q) a, Int.mul_assoc a (b ^ q) b, ← Int.mul_assoc]
    exact hcomm

theorem int_pow_ne_zero {c : Int} (hc : c ≠ 0) : ∀ q : Nat, c ^ q ≠ 0
  | 0 => by simp
  | q + 1 => by
    rw [Int.pow_succ]
    intro h
    cases Int.mul_eq_zero.mp h with
    | inl hq => exact int_pow_ne_zero hc q hq
    | inr hc0 => exact hc hc0

theorem int_mul_left_cancel_of_ne_zero {a x y : Int} (ha : a ≠ 0) (h : a * x = a * y) : x = y := by
  have hsub : a * (x - y) = 0 := by rw [Int.mul_sub, h, Int.sub_self]
  cases Int.mul_eq_zero.mp hsub with
  | inl h0 => exact absurd h0 ha
  | inr hxy => omega

/-- Common nonzero factors cancel from `IsRatPowTwoRatio (c * x) (c * y)`. -/
theorem isRatPowTwoRatio_cancel_left {c x y : Int} (hc : c ≠ 0)
    (h : IsRatPowTwoRatio (c * x) (c * y)) : IsRatPowTwoRatio x y := by
  rcases h with ⟨k, q, hq, heq⟩ | ⟨k, q, hq, heq⟩
  · rw [int_mul_pow, int_mul_pow] at heq
    have heq' : c ^ q * y ^ q = c ^ q * ((2 : Int) ^ k * x ^ q) := by
      rw [heq, ← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ k) (c ^ q), Int.mul_assoc]
    exact Or.inl ⟨k, q, hq, int_mul_left_cancel_of_ne_zero (int_pow_ne_zero hc q) heq'⟩
  · rw [int_mul_pow, int_mul_pow] at heq
    have heq' : c ^ q * ((2 : Int) ^ k * y ^ q) = c ^ q * x ^ q := by
      rw [← heq, ← Int.mul_assoc, Int.mul_comm (c ^ q) ((2 : Int) ^ k), Int.mul_assoc]
    exact Or.inr ⟨k, q, hq, int_mul_left_cancel_of_ne_zero (int_pow_ne_zero hc q) heq'⟩

/-- Symmetric centered order `n = 6`, `k = 2` (`λ = (4, 2)`): `N_NC / N_Int = 720 / 240 = 3`,
    and `k = 3` (`λ = (2, 2, 2)`): `N_NC / N_Int = 720 / 144 = 5`; neither is a power of two. -/
theorem kreweras_order6_even_not_pow2 :
    ¬ IsRatPowTwoRatio (krewerasDen 6 2) (krewerasNum 6) ∧
    ¬ IsRatPowTwoRatio (krewerasDen 6 3) (krewerasNum 6) := by
  constructor
  · intro h
    have heq : krewerasDen 6 2 = 240 * 1 ∧ krewerasNum 6 = 240 * 3 := ⟨rfl, rfl⟩
    rw [heq.1, heq.2] at h
    have hcancel : IsRatPowTwoRatio 1 3 :=
      isRatPowTwoRatio_cancel_left (c := 240) (by decide) h
    exact not_isRatPowTwoRatio_of_mod_three (Or.inl rfl) rfl hcancel
  · exact not_isRatPowTwoRatio_of_mod_five (Or.inr (Or.inr (Or.inl rfl))) rfl

end BooleanFreeConv
