import Std

namespace Tlmc4340

/-- The moment data forced by central symmetry. -/
structure SymmetricMoments where
  moment : Nat → Int
  odd_zero : ∀ k, moment (2 * k + 1) = 0

def OddMomentsDiffer (mu nu : SymmetricMoments) : Prop :=
  ∃ k, mu.moment (2 * k + 1) ≠ nu.moment (2 * k + 1)

theorem odd_moments_agree (mu nu : SymmetricMoments) (k : Nat) :
    mu.moment (2 * k + 1) = nu.moment (2 * k + 1) := by
  rw [mu.odd_zero k, nu.odd_zero k]

theorem no_odd_moment_separation :
    ¬ ∃ mu nu : SymmetricMoments, OddMomentsDiffer mu nu := by
  rintro ⟨mu, nu, k, hne⟩
  exact hne (odd_moments_agree mu nu k)

/-- The first odd moment of a finite paired support `(+a,-a)` cancels. -/
def pairedFirstMoment (support : List Int) : Int :=
  (support.map (fun a => a + (-a))).sum

theorem paired_first_moment_zero (support : List Int) :
    pairedFirstMoment support = 0 := by
  induction support with
  | nil => rfl
  | cons a rest ih =>
      change (a + (-a)) + pairedFirstMoment rest = 0
      rw [ih]
      omega

end Tlmc4340
