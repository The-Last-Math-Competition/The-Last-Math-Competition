import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic.NormNum

namespace ModThree7686

def EventuallyPeriodicMod3 : Prop :=
  ∃ T : Nat, 0 < T ∧ ∃ N : Nat,
    ∀ n : Nat, N ≤ n →
      Nat.centralBinom (n + T) % 3 = Nat.centralBinom n % 3

theorem centralBinom_lucas_mod_three (n : Nat) :
    Nat.centralBinom n % 3 =
      ((2 * n % 3).choose (n % 3) * (2 * n / 3).choose (n / 3)) % 3 := by
  let : Fact (Nat.Prime 3) := { out := by decide }
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := 3) (n := 2 * n) (k := n)

theorem centralBinom_three_mul_mod_three (m : Nat) :
    Nat.centralBinom (3 * m) % 3 = Nat.centralBinom m % 3 := by
  rw [centralBinom_lucas_mod_three,
    show 2 * (3 * m) % 3 = 0 by omega,
    show 3 * m % 3 = 0 by omega,
    show 2 * (3 * m) / 3 = 2 * m by omega,
    show 3 * m / 3 = m by omega,
    Nat.choose_zero_right, one_mul]
  rfl

theorem centralBinom_three_mul_add_one_mod_three (m : Nat) :
    Nat.centralBinom (3 * m + 1) % 3 = (2 * Nat.centralBinom m) % 3 := by
  rw [centralBinom_lucas_mod_three,
    show 2 * (3 * m + 1) % 3 = 2 by omega,
    show (3 * m + 1) % 3 = 1 by omega,
    show 2 * (3 * m + 1) / 3 = 2 * m by omega,
    show (3 * m + 1) / 3 = m by omega,
    show (2 : Nat).choose 1 = 2 by decide]
  rfl

theorem centralBinom_three_mul_add_two_mod_three (m : Nat) :
    Nat.centralBinom (3 * m + 2) % 3 = 0 := by
  rw [centralBinom_lucas_mod_three,
    show 2 * (3 * m + 2) % 3 = 1 by omega,
    show (3 * m + 2) % 3 = 2 by omega,
    show (1 : Nat).choose 2 = 0 by decide,
    zero_mul, Nat.zero_mod]

theorem centralBinom_mod_three_zero_of_div (n : Nat)
    (h : Nat.centralBinom (n / 3) % 3 = 0) :
    Nat.centralBinom n % 3 = 0 := by
  have hd := Nat.div_add_mod n 3
  have hr := Nat.mod_lt n (by decide : 0 < 3)
  have hc : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hc with h0 | h1 | h2
  · have hn : n = 3 * (n / 3) := by omega
    have he := centralBinom_three_mul_mod_three (n / 3)
    rw [← hn] at he
    exact he.trans h
  · have hn : n = 3 * (n / 3) + 1 := by omega
    have he := centralBinom_three_mul_add_one_mod_three (n / 3)
    rw [← hn] at he
    simpa [Nat.mul_mod, h] using he
  · have hn : n = 3 * (n / 3) + 2 := by omega
    have he := centralBinom_three_mul_add_two_mod_three (n / 3)
    rw [← hn] at he
    exact he

theorem centralBinom_three_pow_mod_three (m : Nat) :
    Nat.centralBinom (3 ^ m) % 3 = 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [pow_succ, Nat.mul_comm (3 ^ m) 3, centralBinom_three_mul_mod_three, ih]

theorem centralBinom_mod_three_zero_block (m : Nat) :
    ∀ n : Nat, 2 * 3 ^ m ≤ n → n < 3 ^ (m + 1) →
      Nat.centralBinom n % 3 = 0 := by
  induction m with
  | zero =>
    intro n hlo hhi
    have hn : n = 2 := by norm_num at hlo hhi; omega
    subst n
    decide
  | succ m ih =>
    intro n hlo hhi
    apply centralBinom_mod_three_zero_of_div
    apply ih (n / 3)
    · rw [pow_succ] at hlo
      omega
    · rw [pow_succ] at hhi
      omega

-- A zero block ending immediately before a power of three defeats any fixed period.
theorem centralBinom_mod_three_period_obstruction (T N : Nat) (hT : 0 < T) :
    ∃ n : Nat, N ≤ n ∧
      Nat.centralBinom (n + T) % 3 ≠ Nat.centralBinom n % 3 := by
  let m := max T N
  have hb : m < 3 ^ m := Nat.lt_pow_self (by decide)
  have hTm : T ≤ m := le_max_left T N
  have hNm : N ≤ m := le_max_right T N
  have hTp : T ≤ 3 ^ m := by omega
  have hNp : N ≤ 3 ^ m := by omega
  let n := 3 ^ (m + 1) - T
  have hp : 3 ^ (m + 1) = 3 ^ m * 3 := pow_succ 3 m
  have hlo : 2 * 3 ^ m ≤ n := by dsimp [n]; omega
  have hhi : n < 3 ^ (m + 1) := by dsimp [n]; omega
  have hn : N ≤ n := by omega
  have he : n + T = 3 ^ (m + 1) := by dsimp [n]; omega
  refine ⟨n, hn, ?_⟩
  rw [he, centralBinom_three_pow_mod_three,
    centralBinom_mod_three_zero_block m n hlo hhi]
  decide

theorem centralBinom_mod_three_not_eventually_periodic :
    ¬ EventuallyPeriodicMod3 := by
  rintro ⟨T, hT, N, hper⟩
  obtain ⟨n, hn, hne⟩ := centralBinom_mod_three_period_obstruction T N hT
  exact hne (hper n hn)

end ModThree7686
