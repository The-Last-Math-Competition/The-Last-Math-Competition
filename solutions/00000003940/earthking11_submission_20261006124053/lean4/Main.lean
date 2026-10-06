import Std

namespace Tlmc3940

/-- A family of numerical quantities is invariant under `Iso`. -/
def RespectsIso {D : Type} (Iso : D → D → Prop)
    (inv : Nat → D → Nat) : Prop :=
  ∀ A B, Iso A B → ∀ n, inv n A = inv n B

/-- The separation requested by the conjecture. -/
def AllDiffer {D : Type} (inv : Nat → D → Nat) (A B : D) : Prop :=
  ∀ n, inv n A ≠ inv n B

/-- Isomorphic objects cannot be separated by genuine invariants. -/
theorem no_invariant_separation {D : Type} (Iso : D → D → Prop)
    (inv : Nat → D → Nat) (hInv : RespectsIso Iso inv) :
    ¬ ∃ A B, Iso A B ∧ AllDiffer inv A B := by
  rintro ⟨A, B, hIso, hDiff⟩
  exact hDiff 0 (hInv A B hIso 0)

/-! A concrete truncation model: lists with equality as isomorphism. -/

def truncValue (n : Nat) (xs : List Nat) : Nat := (xs.take n).sum

theorem truncValue_respects_equality :
    RespectsIso (fun A B : List Nat => A = B) truncValue := by
  intro A B hAB n
  cases hAB
  rfl

theorem concrete_separation_impossible :
    ¬ ∃ A B : List Nat,
      A = B ∧ ∀ n, truncValue n A ≠ truncValue n B :=
  no_invariant_separation _ _ truncValue_respects_equality

end Tlmc3940
