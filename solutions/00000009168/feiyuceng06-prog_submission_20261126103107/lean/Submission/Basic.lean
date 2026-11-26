import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.ModelTheory.Semantics

namespace Conjecture9168

open FirstOrder Language

/-- The positive sizes of finite structures satisfying a first-order sentence. -/
def faginSpectrum {L : Language} (φ : L.Sentence) : Set ℕ :=
  {n | ∃ (M : Type) (_ : Fintype M) (_ : Nonempty M) (_ : L.Structure M),
    M ⊨ φ ∧ Fintype.card M = n}

/-- Conjoin “at least n elements” with “fewer than n + 1 elements.” -/
def exactCard (L : Language) (n : ℕ) : L.Sentence :=
  Sentence.cardGe L n ⊓ (Sentence.cardGe L (n + 1)).not

theorem realize_exactCard_iff {L : Language} (n : ℕ) (M : Type*)
    [Fintype M] [L.Structure M] :
    M ⊨ exactCard L n ↔ Fintype.card M = n := by
  simp only [exactCard, Sentence.realize_inf, Sentence.realize_not,
    Sentence.realize_cardGe, Cardinal.mk_fintype, Nat.cast_le]
  omega

/-- This sentence uses equality and has no nonlogical symbols. -/
def exactlySix : Language.empty.Sentence :=
  exactCard Language.empty 6

theorem spectrum_exactlySix : faginSpectrum exactlySix = {6} := by
  ext n
  change (∃ (M : Type) (_ : Fintype M) (_ : Nonempty M)
    (_ : Language.empty.Structure M), M ⊨ exactlySix ∧ Fintype.card M = n) ↔ n ∈ ({6} : Set ℕ)
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨M, hfinite, _, hstructure, hmodel, hcard⟩
    exact hcard.symm.trans ((realize_exactCard_iff 6 M).mp hmodel)
  · rintro rfl
    let _ : Language.empty.Structure (Fin 6) := Language.emptyStructure
    exact ⟨Fin 6, inferInstance, inferInstance, inferInstance,
      (realize_exactCard_iff 6 (Fin 6)).mpr (Fintype.card_fin 6), Fintype.card_fin 6⟩

theorem six_not_prime_power : ¬ IsPrimePow (6 : ℕ) := by
  intro h
  obtain ⟨p, _, unique⟩ := isPrimePow_iff_unique_prime_dvd.mp h
  have two_eq_p : 2 = p := unique 2 ⟨Nat.prime_two, by decide⟩
  have three_eq_p : 3 = p := unique 3 ⟨Nat.prime_three, by decide⟩
  exact (by decide : (2 : ℕ) ≠ 3) (two_eq_p.trans three_eq_p.symm)

/-- The prime-power restriction on spectra fails even for the empty language. -/
theorem conjecture_false :
    ¬ ∀ (L : Language.{0, 0}) (φ : L.Sentence), faginSpectrum φ ⊆ {n | IsPrimePow n} := by
  intro h
  have six_in_spectrum : 6 ∈ faginSpectrum exactlySix := by
    simp [spectrum_exactlySix]
  exact six_not_prime_power (h Language.empty exactlySix six_in_spectrum)

#print axioms conjecture_false

end Conjecture9168
