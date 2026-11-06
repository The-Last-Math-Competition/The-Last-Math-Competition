import Mathlib.Data.Nat.Prime.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.NormNum

/-! A logical obstruction to the two printed necessary numerical clauses.
No value is assigned to an actual Euler-system rank, and no Euler-system or
higher-K-group construction is replaced by an artificial definition. -/
namespace TLMC4307

/-- An optional additional restricted range; the contradiction already lies
inside it. The source does not need to assert this extra restriction. -/
def Allowed (k p : ℕ) : Prop :=
  0<k ∧ p.Prime ∧ 2<p ∧ k≤p-2

theorem legal_witness : Allowed 3 5 ∧ Nat.Coprime 3 (5-1) := by
  unfold Allowed
  decide

variable {R : Type*} [Semiring R] [CharZero R]

theorem pointwise_obstruction (r : R) :
    ¬ (r=((2*3-1:ℕ):R) ∧ (Nat.Coprime 3 (5-1) → r=1)) := by
  rintro ⟨hgeneral,hspecial⟩
  have hs := hspecial legal_witness.2
  norm_num at hgeneral
  have h51 : (5:R) ≠ 1 := by norm_num
  exact h51 (hgeneral.symm.trans hs)

def GeneralNumericalClause (rank : ℕ → ℕ → R) : Prop :=
  ∀ k p, Allowed k p → rank k p=((2*k-1:ℕ):R)

def CoprimeNumericalClause (rank : ℕ → ℕ → R) : Prop :=
  ∀ k p, Allowed k p → Nat.Coprime k (p-1) → rank k p=1

theorem no_candidate_rank_function (rank : ℕ → ℕ → R) :
    ¬ (GeneralNumericalClause rank ∧ CoprimeNumericalClause rank) := by
  rintro ⟨hg,hc⟩
  exact pointwise_obstruction (rank 3 5)
    ⟨hg 3 5 legal_witness.1,hc 3 5 legal_witness.1⟩

theorem no_rank_function_exists :
    ¬ ∃ rank : ℕ → ℕ → R,
      GeneralNumericalClause rank ∧ CoprimeNumericalClause rank := by
  rintro ⟨rank,h⟩
  exact no_candidate_rank_function rank h

theorem unrestricted_formulas_impossible (rank : ℕ → ℕ → R) :
    ¬ ((∀ k p, 0<k → p.Prime → rank k p=((2*k-1:ℕ):R)) ∧
      (∀ k p, 0<k → p.Prime → Nat.Coprime k (p-1) → rank k p=1)) := by
  rintro ⟨hg,hc⟩
  apply no_candidate_rank_function rank
  exact ⟨fun k p h => hg k p h.1 h.2.1,
    fun k p h hcp => hc k p h.1 h.2.1 hcp⟩

theorem fixed_odd_prime_impossible (rank : ℕ → R) :
    ¬ ((∀ k, 0<k → k≤5-2 → rank k=((2*k-1:ℕ):R)) ∧
      (∀ k, 0<k → k≤5-2 → Nat.Coprime k (5-1) → rank k=1)) := by
  rintro ⟨hg,hc⟩
  exact pointwise_obstruction (rank 3)
    ⟨hg 3 (by decide) (by decide),hc 3 (by decide) (by decide)⟩

theorem no_natural_rank_function :
    ¬ ∃ rank : ℕ → ℕ → ℕ,
      GeneralNumericalClause rank ∧ CoprimeNumericalClause rank :=
  no_rank_function_exists

theorem no_integer_rank_function :
    ¬ ∃ rank : ℕ → ℕ → ℤ,
      GeneralNumericalClause rank ∧ CoprimeNumericalClause rank :=
  no_rank_function_exists

theorem no_cardinal_rank_function :
    ¬ ∃ rank : ℕ → ℕ → Cardinal,
      GeneralNumericalClause rank ∧ CoprimeNumericalClause rank :=
  no_rank_function_exists

end TLMC4307
