import Subdivision
import Mathlib.Topology.Homotopy.Equiv

namespace P4110Disproof
open P4110 P4110Geometry P4110Subdivision
noncomputable section

def orderedSubdivisionHomotopyEquiv {G H : GraphPresentation} {k : ℕ}
    (h : Subdivision G H k) (n : ℕ) :
    ContinuousMap.HomotopyEquiv (OrderedConfig n G.realization) (OrderedConfig n H.realization) :=
  (orderedSubdivisionHomeomorph h n).toHomotopyEquiv

def unorderedSubdivisionHomotopyEquiv {G H : GraphPresentation} {k : ℕ}
    (h : Subdivision G H k) (n : ℕ) :
    ContinuousMap.HomotopyEquiv (UnorderedConfig n G.realization) (UnorderedConfig n H.realization) :=
  (unorderedSubdivisionHomeomorph h n).toHomotopyEquiv

/-- Properness requires at least one actual edge insertion. -/
def ProperSubdivision (G H : GraphPresentation) : Prop :=
  ∃ k : ℕ, 0 < k ∧ Subdivision G H k

theorem ordered_subdivision_invariance (G H : GraphPresentation)
    (h : ProperSubdivision G H) (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv (OrderedConfig n G.realization)
      (OrderedConfig n H.realization)) := by
  rcases h with ⟨k,_,h⟩
  exact ⟨orderedSubdivisionHomotopyEquiv h n⟩

theorem unordered_subdivision_invariance (G H : GraphPresentation)
    (h : ProperSubdivision G H) (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv (UnorderedConfig n G.realization)
      (UnorderedConfig n H.realization)) := by
  rcases h with ⟨k,_,h⟩
  exact ⟨unorderedSubdivisionHomotopyEquiv h n⟩

/-- The necessary n=2 separation clause of the original existential cannot occur. -/
theorem no_ordered_subdivision_separation :
    ¬ ∃ G H : GraphPresentation, ProperSubdivision G H ∧
      ¬ Nonempty (ContinuousMap.HomotopyEquiv (OrderedConfig 2 G.realization)
        (OrderedConfig 2 H.realization)) := by
  rintro ⟨G,H,h,hne⟩
  exact hne (ordered_subdivision_invariance G H h 2)

/-- The same contradiction holds under the unordered configuration convention. -/
theorem no_unordered_subdivision_separation :
    ¬ ∃ G H : GraphPresentation, ProperSubdivision G H ∧
      ¬ Nonempty (ContinuousMap.HomotopyEquiv (UnorderedConfig 2 G.realization)
        (UnorderedConfig 2 H.realization)) := by
  rintro ⟨G,H,h,hne⟩
  exact hne (unordered_subdivision_invariance G H h 2)

#print axioms ordered_subdivision_invariance
#print axioms unordered_subdivision_invariance
#print axioms no_ordered_subdivision_separation
#print axioms no_unordered_subdivision_separation
end
end P4110Disproof
