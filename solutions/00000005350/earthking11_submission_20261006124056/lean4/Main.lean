import Std

namespace Tlmc5350

def TwoMoves {B : Type} (Move : B → B → Prop) (a b : B) : Prop :=
  ∃ middle, Move a middle ∧ Move middle b

theorem two_moves_preserve_closure {B K : Type} (Move : B → B → Prop)
    (closure : B → K)
    (preserves : ∀ a b, Move a b → closure a = closure b)
    {a b : B} (h : TwoMoves Move a b) :
    closure a = closure b := by
  rcases h with ⟨middle, ham, hmb⟩
  exact (preserves a middle ham).trans (preserves middle b hmb)

theorem no_two_move_closure_separation {B K : Type}
    (Move : B → B → Prop) (closure : B → K)
    (preserves : ∀ a b, Move a b → closure a = closure b) :
    ¬ ∃ a b, TwoMoves Move a b ∧ closure a ≠ closure b := by
  rintro ⟨a, b, hmoves, hdiff⟩
  exact hdiff (two_moves_preserve_closure Move closure preserves hmoves)

/-! A finite executable instance. -/
def toyMove (a b : Nat) : Prop := a = b
def toyClosure (a : Nat) : Nat := a % 2

theorem toy_move_preserves :
    ∀ a b, toyMove a b → toyClosure a = toyClosure b := by
  intro a b h
  cases h
  rfl

theorem toy_separation_impossible :
    ¬ ∃ a b, TwoMoves toyMove a b ∧ toyClosure a ≠ toyClosure b :=
  no_two_move_closure_separation toyMove toyClosure toy_move_preserves

end Tlmc5350
