import Std
import Init.Omega

namespace Counterexample08

/-- The counterexample polynomial from the submission. -/
def f (n : Nat) : Nat := n * n + n + 2

/-- The polynomial is quadratic with integer coefficients: its leading
coefficient is 1, its linear coefficient is 1, and its constant is 2. -/
def IsQuadraticIntegerPolynomial : Prop :=
  ∃ a b c : Int, a ≠ 0 ∧ ∀ n : Int, a * n * n + b * n + c = n * n + n + 2

/-- The discriminant of `X^2 + X + 2` is `-7`, so it has no repeated root. -/
def discriminant : Int := (1 : Int) * 1 - 4 * 1 * 2

def HasNoRepeatedRoot : Prop := discriminant ≠ 0

/-- The prime predicate used in this elementary formalization. -/
def Prime (n : Nat) : Prop :=
  1 < n ∧ ¬ ∃ d : Fin n, 1 < d.val ∧ d.val ∣ n

instance (n : Nat) : Decidable (Prime n) := by
  unfold Prime
  infer_instance

/-- Prime values up to `x`, counting positive inputs `n ≤ x`. -/
def primeValueCount (x : Nat) : Nat :=
  (List.range x).countP (fun n => decide (Prime (f (n + 1))))

/-- Every product of two consecutive integers is even. -/
theorem consecutive_product_even (n : Nat) :
    (n * (n + 1)) % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [Nat.mul_mod, Nat.add_mod, h]
  · have hn : (n + 1) % 2 = 0 := by omega
    simp [Nat.mul_mod, h, hn]

/-- The counterexample polynomial is always even. -/
theorem f_even (n : Nat) : f n % 2 = 0 := by
  unfold f
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · simp [Nat.add_mod, Nat.mul_mod, hn]
  · simp [Nat.add_mod, Nat.mul_mod, hn]

/-- For every positive input, the value of the polynomial is at least 4. -/
theorem f_ge_four {n : Nat} (hn : 1 ≤ n) : 4 ≤ f n := by
  unfold f
  have hnpos : 0 < n := by omega
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have h : 4 ≤ n * n + n + 2 := by omega
  exact h

/-- For every positive input, `f n` is not prime: it is even and greater than 2. -/
theorem f_not_prime {n : Nat} (hn : 1 ≤ n) : ¬ Prime (f n) := by
  intro hp
  have hge : 4 ≤ f n := f_ge_four hn
  have hdiv : 2 ∣ f n := by
    exact Nat.dvd_of_mod_eq_zero (f_even n)
  rcases hdiv with ⟨k, hk⟩
  have htwo : 2 < f n := by omega
  have hproper : 1 < (2 : Nat) ∧ (2 : Nat) < f n ∧ 2 ∣ f n := by
    exact ⟨by decide, htwo, ⟨k, hk⟩⟩
  exact hp.2 ⟨⟨2, by omega⟩, hproper.1, hproper.2.2⟩

/-- The explicit polynomial is quadratic with integer coefficients. -/
theorem f_is_quadratic_integer_polynomial : IsQuadraticIntegerPolynomial := by
  refine ⟨1, 1, 2, by decide, ?_⟩
  intro n
  simp

/-- Its discriminant is nonzero. -/
theorem f_has_no_repeated_root : HasNoRepeatedRoot := by
  unfold HasNoRepeatedRoot discriminant
  decide

/-- No positive input gives a prime value. -/
theorem no_positive_prime_values :
    ∀ n : Nat, 1 ≤ n → ¬ Prime (f n) := by
  intro n hn
  exact f_not_prime hn

/-- The prime-value count is identically zero for every positive cutoff. -/
theorem prime_value_count_zero {x : Nat} (_hx : 1 ≤ x) : primeValueCount x = 0 := by
  unfold primeValueCount
  apply List.countP_eq_zero.mpr
  intro n hn
  have hnlt : n < x := List.mem_range.mp hn
  have hnp : ¬ Prime (f (n + 1)) := f_not_prime (by omega)
  change ¬decide (Prime (f (n + 1))) = true
  simpa using hnp

end Counterexample08
