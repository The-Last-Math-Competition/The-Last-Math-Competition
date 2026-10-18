import Std

/-!
Arithmetic core for the counterexample to conjecture 00000000145.
Under alpha = 1/2, every prime other than 2 is odd, so its fractional part
is 1/2. The report handles the cosine and asymptotic argument.
-/

def IsPrimeNat (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ a b : Nat, n = a * b → a = 1 ∨ b = 1

/-- Every prime at least three is odd. -/
theorem prime_mod_two_eq_one (n : Nat) (hp : IsPrimeNat n)
    (hthree : 3 ≤ n) : n % 2 = 1 := by
  have hlt : n % 2 < 2 := Nat.mod_lt n (by omega)
  by_cases hz : n % 2 = 0
  · have hdiv : n = 2 * (n / 2) := by
      have h := Nat.mod_add_div n 2
      omega
    rcases hp.2 2 (n / 2) hdiv with htwo | hquot
    · omega
    · have hn : n = 2 := by simpa [hquot] using hdiv
      omega
  · omega

#print axioms prime_mod_two_eq_one
