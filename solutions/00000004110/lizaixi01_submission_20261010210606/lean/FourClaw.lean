import PathReplacement

namespace P4110FourClaw
open P4110Geometry P4110Subdivision P4110Disproof P4110Paths P4110
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Actual K1,4: vertex 0 is the center, vertices 1..4 the distinct leaves;
edge i joins the center to leaf i+1. -/
abbrev fourClaw : GraphPresentation where
  Vertex := Fin 5
  Edge := Fin 4
  vertexTopology := inferInstance
  vertexDiscrete := inferInstance
  vertexFinite := inferInstance
  edgeFinite := inferInstance
  cell := {source := fun _ => 0, target := Fin.succ}

@[simp] theorem fourClaw_source (e : Fin 4) : fourClaw.cell.source e = 0 := rfl
@[simp] theorem fourClaw_target (e : Fin 4) : fourClaw.cell.target e = e.succ := rfl
theorem fourClaw_leaves_distinct : Function.Injective fourClaw.cell.target :=
  Fin.succ_injective _
theorem fourClaw_center_ne_leaf (e : Fin 4) :
    fourClaw.cell.source e ≠ fourClaw.cell.target e := by
  intro h
  have hh := congrArg Fin.val h
  dsimp [fourClaw,Fin.succ] at hh
  omega

abbrev arm0 (k : Fin 4 → ℕ) := fourClaw.replaceEdge (0 : Fin 4) (k 0)
abbrev arm1 (k : Fin 4 → ℕ) := (arm0 k).replaceEdge (.inl (1 : Fin 4)) (k 1)
abbrev arm2 (k : Fin 4 → ℕ) := (arm1 k).replaceEdge (.inl (.inl (2 : Fin 4))) (k 2)
/-- Independently replace each of the four spokes by a nonempty finite path.
All added vertices and edges are fresh, because every replacement uses disjoint sums. -/
abbrev fourClawPaths (k : Fin 4 → ℕ) :=
  (arm2 k).replaceEdge (.inl (.inl (.inl (3 : Fin 4)))) (k 3)

theorem fourClawPaths_subdivision (k : Fin 4 → ℕ) :
    Subdivision fourClaw (fourClawPaths k) (k 0+k 1+k 2+k 3) := by
  exact Subdivision.trans (Subdivision.trans (Subdivision.trans
    (path_replacement_is_subdivision fourClaw (0 : Fin 4) (k 0))
    (path_replacement_is_subdivision (arm0 k) (.inl (1 : Fin 4)) (k 1)))
    (path_replacement_is_subdivision (arm1 k) (.inl (.inl (2 : Fin 4))) (k 2)))
    (path_replacement_is_subdivision (arm2 k) (.inl (.inl (.inl (3 : Fin 4)))) (k 3))

/-- Ordinary subdivision of the undirected four-claw: four independent nonempty
finite paths, with arbitrary labels and orientations. The witness is actual
vertex/edge bijections preserving the unordered endpoint pairs of the explicit
path-replacement graph. No topological-equivalence hypothesis occurs. -/
def OrdinaryFourClawSubdivision (H : GraphPresentation) : Prop :=
  ∃ k : Fin 4 → ℕ, Nonempty (UndirectedPresentationIso (fourClawPaths k) H)

theorem ordinary_four_claw_subdivision_covered (H : GraphPresentation)
    (h : OrdinaryFourClawSubdivision H) :
    ∃ m, Subdivision fourClaw H m := by
  rcases h with ⟨k,⟨hi⟩⟩
  exact ⟨k 0+k 1+k 2+k 3,
    by simpa using (Subdivision.trans (fourClawPaths_subdivision k)
      (presentation_identity_subdivision hi))⟩

theorem ordinary_four_claw_ordered_invariance (H : GraphPresentation)
    (h : OrdinaryFourClawSubdivision H) (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv (OrderedConfig n fourClaw.realization)
      (OrderedConfig n H.realization)) := by
  rcases ordinary_four_claw_subdivision_covered H h with ⟨m,h⟩
  exact ⟨orderedSubdivisionHomotopyEquiv h n⟩

theorem ordinary_four_claw_unordered_invariance (H : GraphPresentation)
    (h : OrdinaryFourClawSubdivision H) (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv (UnorderedConfig n fourClaw.realization)
      (UnorderedConfig n H.realization)) := by
  rcases ordinary_four_claw_subdivision_covered H h with ⟨m,h⟩
  exact ⟨unorderedSubdivisionHomotopyEquiv h n⟩

theorem no_ordinary_four_claw_ordered_separation :
    ¬ ∃ H : GraphPresentation, OrdinaryFourClawSubdivision H ∧
      ¬ Nonempty (ContinuousMap.HomotopyEquiv (OrderedConfig 2 fourClaw.realization)
        (OrderedConfig 2 H.realization)) := by
  rintro ⟨H,h,hne⟩
  exact hne (ordinary_four_claw_ordered_invariance H h 2)

theorem no_ordinary_four_claw_unordered_separation :
    ¬ ∃ H : GraphPresentation, OrdinaryFourClawSubdivision H ∧
      ¬ Nonempty (ContinuousMap.HomotopyEquiv (UnorderedConfig 2 fourClaw.realization)
        (UnorderedConfig 2 H.realization)) := by
  rintro ⟨H,h,hne⟩
  exact hne (ordinary_four_claw_unordered_invariance H h 2)

#print axioms ordinary_four_claw_subdivision_covered
#print axioms no_ordinary_four_claw_ordered_separation
#print axioms no_ordinary_four_claw_unordered_separation
end
end P4110FourClaw
