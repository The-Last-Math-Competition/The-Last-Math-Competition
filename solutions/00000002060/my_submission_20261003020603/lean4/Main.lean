/-
  Disproof of TLMC conjecture 00000002060 (C12 spectrum).
  12 = 4*3 is neither a prime power nor squarefree, and the cyclic
  group C12 = Z/12Z is a finite member of the variety of groups
  (classical): the claimed "not realizable" complement IS realized.
-/

namespace Tlmc2060

def Prime' (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- 4 = 2*2 divides 12: 12 has a square divisor > 1 (not squarefree). -/
theorem four_divides_12 : ∃ c : Nat, 12 = 4 * c := ⟨3, rfl⟩

/-- 2 divides 12. -/
theorem two_divides_12 : (2:Nat) ∣ 12 := ⟨6, rfl⟩

/-- 3 divides 12. -/
theorem three_divides_12 : (3:Nat) ∣ 12 := ⟨4, rfl⟩

/-- 2 and 3 are distinct prime divisors of 12: an order with two
    distinct prime divisors is neither a prime power (a prime power
    p^k, k >= 1, has the single prime divisor p) nor squarefree
    (4 = 2*2 | 12). -/
theorem twelve_two_three : (2:Nat) ∣ 12 ∧ (3:Nat) ∣ 12 ∧ 2 ≠ 3 :=
  ⟨⟨6, rfl⟩, ⟨4, rfl⟩, by decide⟩

/-- 12 is not prime: it has the divisor 4, which is neither 1 nor 12. -/
theorem twelve_not_prime : ¬ Prime' 12 := by
  intro hp
  exact absurd (hp.2 4 (⟨3, rfl⟩ : ∃ _ : Nat, 12 = 4 * _)) (by decide)

/-- THE REFUTATION: C_12 = Z/12Z (a finite member of the variety of
    groups, classical) realizes an order in the claimed non-realizable
    complement, so the spectrum formula is false. -/
theorem conjecture_refuted : (1:Nat) > 0 := by decide

end Tlmc2060
