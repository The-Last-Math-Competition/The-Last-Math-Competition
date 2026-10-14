import Conjecture2899.Geometry
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find

namespace Conjecture2899

theorem kakeya_card_exists (F : Type*) [Field F] [Fintype F] (d : ℕ) :
    ∃ n : ℕ, ∃ K : Finset (Ambient F d), IsKakeya K ∧ K.card = n := by
  classical
  refine ⟨(Finset.univ : Finset (Ambient F d)).card, Finset.univ, ?_, rfl⟩
  intro v _hv
  exact ⟨0, fun t => Finset.mem_univ _⟩

noncomputable def minimumKakeyaSize (F : Type*) [Field F] [Fintype F]
    (d : ℕ) : ℕ := by
  classical
  exact Nat.find (kakeya_card_exists F d)

theorem minimum_attained (F : Type*) [Field F] [Fintype F] (d : ℕ) :
    ∃ K : Finset (Ambient F d), IsKakeya K ∧ K.card = minimumKakeyaSize F d := by
  classical
  exact Nat.find_spec (kakeya_card_exists F d)

theorem minimum_le_card {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (K : Finset (Ambient F d)) (hK : IsKakeya K) :
    minimumKakeyaSize F d ≤ K.card := by
  classical
  exact Nat.find_min' (kakeya_card_exists F d) ⟨K, hK, rfl⟩

def ProposedEventualLowerBound (d : ℕ) : Prop :=
  ∃ c : ℝ, ∃ Q : ℕ, ∀ (F : Type) [Field F] [Fintype F],
    Q ≤ Fintype.card F →
      (Fintype.card F : ℝ)^d * (1 - c / (Fintype.card F : ℝ)) ≤
        (minimumKakeyaSize F d : ℝ)

end Conjecture2899
