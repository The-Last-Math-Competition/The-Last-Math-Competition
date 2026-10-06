import Std

namespace Tlmc5244

/-- The two incompatible component-count clauses in the filed conjecture. -/
def FiledClaim (components : Nat → Nat) : Prop :=
  (∀ g, 2 ≤ g → components g = 1) ∧ components 2 = 2

theorem genus_two_from_universal (components : Nat → Nat)
    (h : ∀ g, 2 ≤ g → components g = 1) :
    components 2 = 1 :=
  h 2 (by decide)

theorem filed_claim_false (components : Nat → Nat) :
    ¬ FiledClaim components := by
  rintro ⟨hall, htwo⟩
  have hone : components 2 = 1 := genus_two_from_universal components hall
  omega

theorem no_component_count_satisfies_claim :
    ¬ ∃ components : Nat → Nat, FiledClaim components := by
  rintro ⟨components, h⟩
  exact filed_claim_false components h

end Tlmc5244
