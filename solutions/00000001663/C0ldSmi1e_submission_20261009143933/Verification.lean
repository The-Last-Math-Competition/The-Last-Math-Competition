import Conjecture1663

namespace Verification1663
open Conjecture1663

/-- Recheck the exact quantified conjunction without the proposition abbreviations. -/
theorem exact_original_negation : ¬
    ((∀ (n : ℕ), 2 ≤ n → ∀ G H : SimpleGraph (Fin (n + 1)),
      deck G = deck H → Nonempty (G ≃g H)) ∧
     (∀ (n : ℕ), 2 ≤ n → ∀ G H : SimpleGraph (Fin (n + 1)),
      deck G = deck H → 2 ≤ editDistance G H)) := originalClaim_false

/-- Recheck the witness at the smallest admitted order, without any extra hypotheses. -/
theorem minimum_order_witness :
    deck (⊥ : Graph 3) = deck (⊥ : Graph 3) ∧
      editDistance (⊥ : Graph 3) (⊥ : Graph 3) = 0 :=
  ⟨rfl, editDistance_self _⟩

end Verification1663

#print axioms Conjecture1663.originalClaim_false
#print axioms Conjecture1663.editDistance_eq_zero_iff
#print axioms Conjecture1663.deck_iso
#print axioms Verification1663.exact_original_negation
