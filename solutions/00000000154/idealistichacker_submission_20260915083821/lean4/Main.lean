import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Nat.Prime.Basic
/-!
# Formal research prototype for TLMC conjecture 00000000154

The project uses Mathlib's `numDerangements` recurrence together with the
proved bridge `card_derangements_fin_eq_numDerangements`.  The advertised
result is about the cardinality of the actual subtype of fixed-point-free
permutations of `Fin (2 * k)`, not merely a separately defined sequence.
-/
namespace TLMC154

open Equiv Fintype
open derangements

/-- Every derangement number with an index of the form `n + 2` is positive. -/
theorem numDerangements_pos_add_two (n : ℕ) : 0 < numDerangements (n + 2) := by
  induction n with
  | zero => norm_num [numDerangements_add_two]
  | succ n ih =>
      rw [show Nat.succ n + 2 = (n + 1) + 2 by omega, numDerangements_add_two]
      exact Nat.mul_pos (by omega) (Nat.add_pos_right _ ih)

/--
For each `m`, the even derangement number `D_(2 * (m + 2))` is composite.

Here `m + 2` explicitly represents the `k ≥ 2` branch of the final theorem:
the recurrence supplies a factor greater than one and its remaining factor is
also greater than one.
-/
theorem numDerangements_even_ge_two_not_prime (m : ℕ) :
    ¬ Nat.Prime (numDerangements (2 * (m + 2))) := by
  rw [show 2 * (m + 2) = (2 * m + 2) + 2 by omega, numDerangements_add_two]
  apply Nat.not_prime_mul
  · omega
  · have hleft : 0 < numDerangements (2 * m + 2) :=
      numDerangements_pos_add_two (2 * m)
    have hright : 0 < numDerangements ((2 * m + 2) + 1) := by
      rw [show 2 * m + 2 + 1 = (2 * m + 1) + 2 by omega]
      exact numDerangements_pos_add_two (2 * m + 1)
    omega

/-- No even-indexed derangement number is prime.

The proof separates the exceptional indices `k = 0` and `k = 1`, whose
numbers are both `1`, from `k = m + 2`, where the recurrence gives a nontrivial
product.
-/
theorem numDerangements_even_not_prime :
    ∀ k : ℕ, ¬ Nat.Prime (numDerangements (2 * k)) := by
  intro k
  cases k with
  | zero => simpa using Nat.not_prime_one
  | succ k =>
      cases k with
      | zero => simpa [numDerangements_add_two] using Nat.not_prime_one
      | succ m =>
          have hindex : 2 * Nat.succ (Nat.succ m) = 2 * (m + 2) := by omega
          rw [hindex]
          exact numDerangements_even_ge_two_not_prime m

/--
Formal negation of the prime-value claim on all even finite sets.

`derangements (Fin (2 * k))` is Mathlib's type of actual fixed-point-free
permutations.  The cardinality bridge below identifies it with the recurrence
used in `numDerangements_even_not_prime`.
-/
theorem fin_even_derangements_card_not_prime :
    ∀ k : ℕ, ¬ Nat.Prime (Fintype.card (derangements (Fin (2 * k)))) := by
  intro k
  rw [card_derangements_fin_eq_numDerangements]
  exact numDerangements_even_not_prime k


/--
Direct all-even-index form of the disproof: every even finite type `Fin n` has
a non-prime number of fixed-point-free permutations.
-/
theorem fin_all_even_derangements_card_not_prime :
    ∀ n : ℕ, Even n →
      ¬ Nat.Prime (Fintype.card (derangements (Fin n))) := by
  intro n h_even
  rcases h_even with ⟨k, hk⟩
  rw [hk, show k + k = 2 * k by omega]
  exact fin_even_derangements_card_not_prime k

/-- The precise index set asserted to be infinite by the source conjecture. -/
def evenPrimeDerangementIndices : Set ℕ :=
  {n | Even n ∧ Nat.Prime (Fintype.card (derangements (Fin n)))}

/-- The source conjecture's even-prime derangement index set is empty. -/
theorem evenPrimeDerangementIndices_eq_empty :
    evenPrimeDerangementIndices = ∅ := by
  ext n
  simp only [evenPrimeDerangementIndices, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false]
  intro h
  exact (fin_all_even_derangements_card_not_prime n h.1) h.2

/-- In particular, the source conjecture's index set is not infinite. -/
theorem evenPrimeDerangementIndices_not_infinite :
    ¬ Set.Infinite evenPrimeDerangementIndices := by
  rw [evenPrimeDerangementIndices_eq_empty]
  simp

end TLMC154
