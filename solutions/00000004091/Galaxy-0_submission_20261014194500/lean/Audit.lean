import Conjecture4091.Basic

namespace IndependentReview4091

open TLMC4091

-- Check that the dimension certificates really distinguish these spaces.
theorem square_not_zero_dimensional : ¬ HasFirstBetti square 0 := by
  rintro ⟨basis, _, spanning⟩
  have cyc : IsCycle square (fun _ => 1) := by
    apply (square_cycle_iff _).mpr
    intro e
    rfl
  obtain ⟨a, equality, _⟩ := spanning _ cyc
  have at_edge := congrFun equality 0
  change (0 : Rat) = 1 at at_edge
  exact (by decide : (0 : Rat) ≠ 1) at_edge

-- The underlying oriented graph representations have the advertised data.
example : segment.vertices = 2 ∧ segment.edges = 1 := by decide
example : square.vertices = 4 ∧ square.edges = 4 := by decide
example : ∀ e : Fin 4, square.source e = e := by decide
example : square.target 0 = 1 ∧ square.target 1 = 2 ∧
    square.target 2 = 3 ∧ square.target 3 = 0 := by decide

-- Expanded audit of all public authored theorems.
#print axioms TLMC4091.segment_cycle_iff
#print axioms TLMC4091.square_cycle_iff
#print axioms TLMC4091.segment_firstBetti
#print axioms TLMC4091.square_firstBetti
#print axioms TLMC4091.no_fewer_than_two
#print axioms TLMC4091.segment_chromatic
#print axioms TLMC4091.square_chromatic
#print axioms TLMC4091.conjecture_00000004091_false
#print axioms square_not_zero_dimensional

end IndependentReview4091
