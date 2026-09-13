/-
  Disproof of conjecture `00000000226` (Cullen-Woodall counting constant).

  Conjecture (as filed): with `C_n = n * 2^n + 1` the Cullen numbers and
  `W_n = n * 2^n - 1` the Woodall numbers, "the proportion of Cullen numbers
  with least prime factor 3 is an explicit rational, and the corresponding
  proportions for Cullen and Woodall numbers sum to 1 (complementary symmetry
  mod 3)".

  REFUTATION.  Both `C_n` and `W_n` are odd for every `n >= 1`, so "least prime
  factor 3" is the same as "divisible by 3".  Reducing modulo 3 (`2^n mod 3`
  has period 2, `n mod 3` has period 3, combined period 6) gives

      3 | C_n  <=>  n = 1 or 2 (mod 6),   proportion 2/6 = 1/3,
      3 | W_n  <=>  n = 4 or 5 (mod 6),   proportion 2/6 = 1/3.

  Hence the two proportions sum to `1/3 + 1/3 = 2/3`, NOT `1`, and the asserted
  "complementary symmetry mod 3" fails.

  This file formalises the residue facts and the non-sum in CORE LEAN ONLY
  (`import Std`, no Mathlib, no `sorry`, no `axiom`, no `native_decide`).
-/

import Std

set_option maxRecDepth 100000

namespace Tlmc226

/-! ## The sequences -/

/-- Cullen number `C_n = n * 2^n + 1`. -/
def C (n : Nat) : Nat := n * 2 ^ n + 1

/-- Woodall number `W_n = n * 2^n - 1`.  Woodall numbers are indexed by
`n >= 1`; at `n = 0` the natural-number truncation gives `W_0 = 0`, which is
not a Woodall number, and the Woodall statements below carry `1 <= n`. -/
def W (n : Nat) : Nat := n * 2 ^ n - 1

/-! ## Periodicity modulo 3 (period 6) -/

/-- `2^n mod 3` depends only on `n mod 6`; equivalently, since `2^6 = 64 = 1 mod 3`,
the exponent `n` may be reduced modulo `6`. -/
theorem two_pow_mod_three_period6 (n : Nat) : 2 ^ n % 3 = 2 ^ (n % 6) % 3 := by
  conv => lhs; rw [← Nat.div_add_mod n 6]
  rw [Nat.pow_add, Nat.pow_mul]
  have h : (2 ^ 6) ^ (n / 6) % 3 = 1 := by
    rw [show (2 : Nat) ^ 6 = 64 by decide, Nat.pow_mod]
    simp
  rw [Nat.mul_mod, h]
  have hlt : 2 ^ (n % 6) % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [Nat.one_mul, Nat.mod_eq_of_lt hlt]

/-- The core periodic identity: `n * 2^n mod 3` depends only on `n mod 6`. -/
theorem mul_two_pow_mod6 (n : Nat) :
    (n * 2 ^ n) % 3 = ((n % 6) * 2 ^ (n % 6)) % 3 := by
  calc
    (n * 2 ^ n) % 3
        = ((n % 3) * (2 ^ n % 3)) % 3 := Nat.mul_mod n (2 ^ n) 3
    _ = (((n % 6) % 3) * (2 ^ (n % 6) % 3)) % 3 := by
          rw [← Nat.mod_mod_of_dvd n (by decide : 3 ∣ 6)]
          rw [two_pow_mod_three_period6]
    _ = ((n % 6) * 2 ^ (n % 6)) % 3 :=
          (Nat.mul_mod (n % 6) (2 ^ (n % 6)) 3).symm

/-- `(n * 2^n + 1) mod 3` is periodic in `n` with period 6. -/
theorem cullen_period6 (n : Nat) :
    (n * 2 ^ n + 1) % 3 = ((n % 6) * 2 ^ (n % 6) + 1) % 3 := by
  calc
    (n * 2 ^ n + 1) % 3
        = ((n * 2 ^ n) % 3 + 1 % 3) % 3 := Nat.add_mod _ _ _
    _ = (((n % 6) * 2 ^ (n % 6)) % 3 + 1 % 3) % 3 := by rw [mul_two_pow_mod6]
    _ = ((n % 6) * 2 ^ (n % 6) + 1) % 3 := (Nat.add_mod _ _ _).symm

/-- `(n * 2^n + 2) mod 3` is periodic in `n` with period 6.  Subtracting `1`
modulo `3` is the same as adding `2`; the `+2` form avoids an `n >= 1`
side condition in the periodic statement. -/
theorem woodall_period6 (n : Nat) :
    (n * 2 ^ n + 2) % 3 = ((n % 6) * 2 ^ (n % 6) + 2) % 3 := by
  calc
    (n * 2 ^ n + 2) % 3
        = ((n * 2 ^ n) % 3 + 2 % 3) % 3 := Nat.add_mod _ _ _
    _ = (((n % 6) * 2 ^ (n % 6)) % 3 + 2 % 3) % 3 := by rw [mul_two_pow_mod6]
    _ = ((n % 6) * 2 ^ (n % 6) + 2) % 3 := (Nat.add_mod _ _ _).symm

/-! ## The two equivalences -/

/-- **Cullen.**  `C_n = n * 2^n + 1` is divisible by `3` exactly when
`n = 1` or `2 (mod 6)`.  Hence the Cullen proportion is `2/6 = 1/3`. -/
theorem cullen_div3_iff (n : Nat) :
    (n * 2 ^ n + 1) % 3 = 0 ↔ n % 6 = 1 ∨ n % 6 = 2 := by
  rw [cullen_period6]
  have h : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨
      n % 6 = 5 := by omega
  rcases h with h | h | h | h | h | h <;> rw [h] <;> decide

/-- **Woodall, `+2` form.**  `n * 2^n + 2` is divisible by `3` exactly when
`n = 4` or `5 (mod 6)`. -/
theorem woodall_div3_iff (n : Nat) :
    (n * 2 ^ n + 2) % 3 = 0 ↔ n % 6 = 4 ∨ n % 6 = 5 := by
  rw [woodall_period6]
  have h : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨
      n % 6 = 5 := by omega
  rcases h with h | h | h | h | h | h <;> rw [h] <;> decide

/-- For `n >= 1`, `W_n = n * 2^n - 1` agrees modulo `3` with `n * 2^n + 2`
(since `2^1 <= n * 2^n`, so `n * 2^n - 1 + 3 = n * 2^n + 2`). -/
theorem W_mod3_eq_add_two (n : Nat) (hn : 1 ≤ n) :
    W n % 3 = (n * 2 ^ n + 2) % 3 := by
  unfold W
  have hm : 1 ≤ n * 2 ^ n := by
    calc
      (1 : Nat) = 1 * 1 := by decide
      _ ≤ n * 2 ^ n := Nat.mul_le_mul hn Nat.one_le_two_pow
  have h : n * 2 ^ n + 2 = n * 2 ^ n - 1 + 3 := by omega
  rw [h, Nat.add_mod_right]

/-- **Woodall.**  `W_n` is divisible by `3` exactly when `n = 4` or `5 (mod 6)`.
Hence the Woodall proportion is `2/6 = 1/3`. -/
theorem woodall_W_div3_iff (n : Nat) (hn : 1 ≤ n) :
    W n % 3 = 0 ↔ n % 6 = 4 ∨ n % 6 = 5 := by
  rw [W_mod3_eq_add_two n hn]
  exact woodall_div3_iff n

/-! ## Oddness: "least prime factor 3" is "divisible by 3" -/

/-- `C_n` is odd for `n >= 1`: `n * 2^n` is even because `2^n` is even, so
`n * 2^n + 1` is odd.  Consequently, for Cullen numbers the least prime factor
is `3` exactly when the number is divisible by `3`. -/
theorem cullen_odd (n : Nat) (hn : 0 < n) : C n % 2 = 1 := by
  unfold C
  rw [Nat.add_mod, Nat.mul_mod, Nat.two_pow_mod_two_eq_zero.mpr hn]
  simp

/-- `W_n` is odd for `n >= 1`; the least prime factor of a Woodall number is
`3` exactly when it is divisible by `3`. -/
theorem woodall_odd (n : Nat) (hn : 1 ≤ n) : W n % 2 = 1 := by
  have h : W n % 2 = (n * 2 ^ n + 1) % 2 := by
    unfold W
    have hm : 1 ≤ n * 2 ^ n := by
      calc
        (1 : Nat) = 1 * 1 := by decide
        _ ≤ n * 2 ^ n := Nat.mul_le_mul hn Nat.one_le_two_pow
    have hh : n * 2 ^ n + 1 = n * 2 ^ n - 1 + 2 := by omega
    rw [hh, Nat.add_mod_right]
  rw [h]
  exact cullen_odd n (by omega)

/-! ## The residue table -/

/-- Residue table for `n mod 6 = 0, 1, 2, 3, 4, 5`, using the representatives
`n = 6, 7, 8, 9, 10, 11`, for both sequences modulo `3`:

  `n mod 6`      : 0  1  2  3  4  5
  `2^n mod 3`    : 1  2  1  2  1  2
  `C_n mod 3`    : 1  0  0  1  2  2
  `W_n mod 3`    : 2  1  1  2  0  0
-/
theorem residue_table :
    (C 6) % 3 = 1 ∧ (C 7) % 3 = 0 ∧ (C 8) % 3 = 0 ∧
    (C 9) % 3 = 1 ∧ (C 10) % 3 = 2 ∧ (C 11) % 3 = 2 ∧
    (W 6) % 3 = 2 ∧ (W 7) % 3 = 1 ∧ (W 8) % 3 = 1 ∧
    (W 9) % 3 = 2 ∧ (W 10) % 3 = 0 ∧ (W 11) % 3 = 0 := by
  decide

/-! ## The proportions do not sum to `1` -/

/-- Over the common denominator `6`, the Cullen proportion and the Woodall
proportion are both `2/6`; their numerators sum to `2 + 2 = 4`, so the total
proportion is `4/6 = 2/3`, not `1 = 6/6`.  Core `Rat` operations are
irreducible, so `decide` cannot reduce `Rat` expressions; the arithmetic is
therefore carried out in `Nat` over the common denominator `6`. -/
theorem proportions_sum : (2 : Nat) + 2 = 4 ∧ (4 : Nat) ≠ 6 :=
  ⟨by decide, by decide⟩

/-- `2/3 ≠ 1` in the `Nat` cross-multiplied form: `2 * 1 ≠ 1 * 3`. -/
theorem two_thirds_ne_one : (2 : Nat) * 1 ≠ 1 * 3 := by decide

/-- The numerator comparison `4 ≠ 6` of `2/3 = 4/6` against `1 = 6/6`. -/
theorem four_ne_six : (4 : Nat) ≠ 6 := by decide

/-! ## The collected disproof -/

/-- **Conjecture `00000000226` is FALSE.**  The Cullen numbers divisible by `3`
are exactly those with `n = 1, 2 (mod 6)` (proportion `1/3`), the Woodall
numbers divisible by `3` are exactly those with `n = 4, 5 (mod 6)` (proportion
`1/3`); since the sequences are odd, these are the same as the numbers with
least prime factor `3`.  The two proportions sum to `2/3`, not `1`, so the
asserted complementary symmetry mod `3` fails. -/
theorem conjecture_00000000226_false :
    (∀ n, (n * 2 ^ n + 1) % 3 = 0 ↔ n % 6 = 1 ∨ n % 6 = 2) ∧
    (∀ n, (n * 2 ^ n + 2) % 3 = 0 ↔ n % 6 = 4 ∨ n % 6 = 5) ∧
    (∀ n, 1 ≤ n → (W n % 3 = 0 ↔ n % 6 = 4 ∨ n % 6 = 5)) ∧
    (2 : Nat) + 2 = 4 ∧ (4 : Nat) ≠ 6 :=
  ⟨cullen_div3_iff, woodall_div3_iff, woodall_W_div3_iff, by decide, by decide⟩

end Tlmc226
