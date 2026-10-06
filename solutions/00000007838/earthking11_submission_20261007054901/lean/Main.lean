import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Order

namespace Tlmc7838

/-- The set denoted by `{0, 2, 4, ...}` when the ellipsis ranges over all
nonnegative even integers. -/
def evenNumbers : Set ℕ := {n | ∃ k : ℕ, n = 2 * k}

/-- The defining finite-gap condition of a numerical semigroup. -/
def NumericalSemigroup (s : Set ℕ) : Prop :=
  0 ∈ s ∧ (∀ ⦃a b : ℕ⦄, a ∈ s → b ∈ s → a + b ∈ s) ∧ sᶜ.Finite

/-- Every Weierstrass semigroup is, in particular, a numerical semigroup. -/
def WeierstrassSemigroup (s : Set ℕ) : Prop := NumericalSemigroup s

theorem oddNumbers_infinite : {n : ℕ | ∃ k : ℕ, n = 2 * k + 1}.Infinite := by
  have hrange : (Set.range (fun k : ℕ => 2 * k + 1)).Infinite :=
    Set.infinite_range_of_injective (by
      intro a b h
      have h' : 2 * a = 2 * b := Nat.add_right_cancel h
      omega)
  apply hrange.mono
  rintro x ⟨k, rfl⟩
  exact ⟨k, rfl⟩

theorem oddNumbers_subset_evenNumbers_compl :
    {n : ℕ | ∃ k : ℕ, n = 2 * k + 1} ⊆ evenNumbersᶜ := by
  intro n hn
  rcases hn with ⟨k, rfl⟩
  intro heven
  rcases heven with ⟨j, hj⟩
  omega

theorem evenNumbers_compl_infinite : evenNumbersᶜ.Infinite :=
  oddNumbers_infinite.mono oddNumbers_subset_evenNumbers_compl

theorem evenNumbers_not_numericalSemigroup : ¬ NumericalSemigroup evenNumbers := by
  rintro ⟨_, _, hfiniteGaps⟩
  exact evenNumbers_compl_infinite hfiniteGaps

/-- The literal object clause in the conjecture would require the displayed
even-number set to be a Weierstrass semigroup. -/
theorem no_literal_hyperelliptic_star_semigroup :
    ¬ ∃ h : Set ℕ, WeierstrassSemigroup h ∧ h = evenNumbers := by
  rintro ⟨h, hh, rfl⟩
  exact evenNumbers_not_numericalSemigroup hh

/-- Thus the conjecture's asserted Weierstrass-semigroup example cannot exist
under the standard literal interpretation of its displayed set. -/
theorem literal_example_clause_false :
    ¬ ∃ h : Set ℕ, NumericalSemigroup h ∧ h = evenNumbers :=
  no_literal_hyperelliptic_star_semigroup

#print axioms evenNumbers_compl_infinite
#print axioms no_literal_hyperelliptic_star_semigroup
#print axioms literal_example_clause_false

end Tlmc7838
