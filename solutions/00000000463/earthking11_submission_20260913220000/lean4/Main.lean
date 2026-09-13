/-
  Disproof of conjecture `00000000463`.

  Conjecture (as filed):
    Definition: τ(Kₙ) = n^{n-2}.
    Conjecture: #{n ≤ N : n^{n-2} is squarefree} ~ c·N/√(log N).

  The conjecture is FALSE.  For every n ≥ 4, choose any prime p | n.  Then
  v_p(n^{n-2}) = (n-2)·v_p(n) ≥ 2·1 = 2, so p² | n^{n-2} and n^{n-2} is not
  squarefree.  Only n ∈ {2,3} can contribute (plus n = 1 under the convention
  1^{1-2} = 1^0 = 1, which is squarefree), so the count is bounded by 3 while
  c·N/√(log N) → ∞.  The asserted asymptotic is false.

  Core Lean only (`import Std`), no Mathlib, no `sorry`.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc463

/-! ## Primality and squarefreeness -/

/-- Bounded trial-division primality test.  `primeB n = true` iff `n ≥ 2` and
no `d` with `2 ≤ d < n` divides `n`.  The search is bounded by `n`. -/
def primeB (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all fun d => decide (d < 2 ∨ n % d ≠ 0)

/-- Primality as a `Prop`: `p ≥ 2` and the only divisors of `p` are `1` and
`p`.  (`Nat.Prime` is not available in `import Std`, so it is defined here.) -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- `n` is squarefree when no prime square divides it. -/
def Squarefree (n : Nat) : Prop := ∀ p : Nat, Prime p → ¬ (p * p ∣ n)

/-- The concrete small primes, checked by the bounded test. -/
theorem primeB_two : primeB 2 = true := by decide
theorem primeB_three : primeB 3 = true := by decide
theorem primeB_four : primeB 4 = false := by decide
theorem primeB_five : primeB 5 = true := by decide

/-! ## Every `n ≥ 2` has a prime divisor -/

/-- Every `n ≥ 2` has a prime divisor.  Proof by strong induction: if `n` is
prime use `p = n`; otherwise `n` has a divisor `d` with `2 ≤ d < n`, to which
the induction hypothesis applies. -/
theorem exists_prime_dvd : ∀ n : Nat, 2 ≤ n → ∃ p : Nat, Prime p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hp : Prime n
    · exact ⟨n, hp, Nat.dvd_refl n⟩
    · have hnot : ¬ (∀ d : Nat, d ∣ n → d = 1 ∨ d = n) :=
        fun hall => hp ⟨hn, hall⟩
      obtain ⟨d, hd⟩ := Classical.not_forall.mp hnot
      obtain ⟨hdvd, hdne⟩ := Classical.not_imp.mp hd
      have hd1 : d ≠ 1 := fun h => hdne (Or.inl h)
      have hdn : d ≠ n := fun h => hdne (Or.inr h)
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hd2 : 2 ≤ d := by omega
      have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
      have hdlt : d < n := by omega
      obtain ⟨p, hpp, hpd⟩ := ih d hdlt hd2
      exact ⟨p, hpp, Nat.dvd_trans hpd hdvd⟩

/-! ## The key divisibility step -/

/-- If `p ∣ n` and `2 ≤ n - 2` then `p * p ∣ n ^ (n - 2)`.  Indeed
`p * p ∣ n * n = n ^ 2` and `n ^ 2 ∣ n ^ (n - 2)`. -/
theorem sq_dvd_pow_of_dvd {p n : Nat} (h : p ∣ n) (h2 : 2 ≤ n - 2) :
    p * p ∣ n ^ (n - 2) := by
  have hpp : p * p ∣ n * n := Nat.mul_dvd_mul h h
  have hpp2 : p * p ∣ n ^ 2 := by
    simpa [Nat.pow_two] using hpp
  have hpow : n ^ 2 ∣ n ^ (n - 2) := Nat.pow_dvd_pow n h2
  exact Nat.dvd_trans hpp2 hpow

/-- **Main theorem.** For every `n ≥ 4`, `n ^ (n - 2)` is not squarefree: any
prime divisor `p` of `n` satisfies `p² ∣ n ^ (n - 2)`. -/
theorem not_squarefree_pow (n : Nat) (h : 4 ≤ n) : ¬ Squarefree (n ^ (n - 2)) := by
  intro hs
  have hn2 : 2 ≤ n := by omega
  obtain ⟨p, hp, hpd⟩ := exists_prime_dvd n hn2
  have hlt : 2 ≤ n - 2 := by omega
  exact hs p hp (sq_dvd_pow_of_dvd hpd hlt)

/-! ## The squarefree small cases -/

/-- `1` is squarefree. -/
theorem squarefree_one : Squarefree 1 := by
  intro p hp hdiv
  have hle : p * p ≤ 1 := Nat.le_of_dvd (by omega) hdiv
  have h4 : 4 ≤ p * p := by
    have := Nat.mul_le_mul hp.1 hp.1
    omega
  omega

/-- `3` is squarefree. -/
theorem squarefree_three : Squarefree 3 := by
  intro p hp hdiv
  have hle : p * p ≤ 3 := Nat.le_of_dvd (by omega) hdiv
  have h4 : 4 ≤ p * p := by
    have := Nat.mul_le_mul hp.1 hp.1
    omega
  omega

/-- `2 ^ (2 - 2) = 2 ^ 0 = 1` is squarefree. -/
theorem squarefree_two_pow : Squarefree (2 ^ (2 - 2)) := squarefree_one

/-- `3 ^ (3 - 2) = 3 ^ 1 = 3` is squarefree. -/
theorem squarefree_three_pow : Squarefree (3 ^ (3 - 2)) := squarefree_three

/-- Every `n ≤ 3` has `n ^ (n - 2)` squarefree (with `Nat` truncating
subtraction, `0 ^ 0 = 1 ^ 0 = 2 ^ 0 = 1` and `3 ^ 1 = 3`). -/
theorem squarefree_of_le_three {n : Nat} (h : n ≤ 3) : Squarefree (n ^ (n - 2)) := by
  have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn with h0 | h1 | h2 | h3
  · subst h0; exact squarefree_one
  · subst h1; exact squarefree_one
  · subst h2; exact squarefree_one
  · subst h3; exact squarefree_three

/-- Conversely, a squarefree value forces `n ≤ 3`. -/
theorem sqfree_pow_le_three {n : Nat} (h : Squarefree (n ^ (n - 2))) : n ≤ 3 := by
  apply Classical.byContradiction
  intro hle
  exact not_squarefree_pow n (by omega) h

/-- **Characterisation.** For `n ≥ 1`, `n ^ (n - 2)` is squarefree exactly for
`n ∈ {1, 2, 3}`. -/
theorem sqfree_pow_iff_le_three {n : Nat} (_hn : 1 ≤ n) :
    Squarefree (n ^ (n - 2)) ↔ n ≤ 3 :=
  ⟨sqfree_pow_le_three, squarefree_of_le_three⟩

/-! ## The count is bounded -/

/-- The number of candidate indices `n ∈ {1, …, N}` that can have
`n ^ (n - 2)` squarefree, i.e. those with `n ≤ 3`.  This is the conjecture's
count, by the characterisation `sqfree_pow_iff_le_three`. -/
def sqfreeCount : Nat → Nat
  | 0 => 0
  | n + 1 => sqfreeCount n + (if n + 1 ≤ 3 then 1 else 0)

/-- Closed form: `sqfreeCount N = min N 3`. -/
theorem sqfreeCount_eq_min : ∀ N : Nat, sqfreeCount N = min N 3
  | 0 => rfl
  | N + 1 => by
      rw [sqfreeCount, sqfreeCount_eq_min N]
      by_cases h : N + 1 ≤ 3
      · rw [if_pos h, Nat.min_eq_left h, Nat.min_eq_left (by omega : N ≤ 3)]
      · rw [if_neg h, Nat.min_eq_right (by omega : 3 ≤ N),
          Nat.min_eq_right (by omega : 3 ≤ N + 1)]

/-- **The count is bounded by 3** for every `N`; it can never grow like
`c·N/√(log N)`, which tends to infinity for `c > 0`. -/
theorem sqfreeCount_le_three (N : Nat) : sqfreeCount N ≤ 3 := by
  rw [sqfreeCount_eq_min]
  exact Nat.min_le_right N 3

/-- Explicit table of the count at powers of ten. -/
theorem sqfreeCount_10 : sqfreeCount 10 = 3 := by rw [sqfreeCount_eq_min]; rfl
theorem sqfreeCount_100 : sqfreeCount 100 = 3 := by rw [sqfreeCount_eq_min]; rfl
theorem sqfreeCount_1000 : sqfreeCount 1000 = 3 := by rw [sqfreeCount_eq_min]; rfl
theorem sqfreeCount_1000000 : sqfreeCount 1000000 = 3 := by rw [sqfreeCount_eq_min]; rfl

/-- **The conjecture fails.**  Its left-hand side is bounded by `3` for all
`N`, so it cannot be asymptotic to `c·N/√(log N)`.  Stated as: the count is at
most `3` for every `N`. -/
theorem conjecture_00000000463_false (N : Nat) : sqfreeCount N ≤ 3 :=
  sqfreeCount_le_three N

end Tlmc463
