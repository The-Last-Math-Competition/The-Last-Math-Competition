import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Clopen
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Finiteness

/-! The standard Wirtinger virtual group on an actual crossing-free plane circle.
Arcs are genuine connected components after removing crossing preimages.
Relators are indexed by genuine classical crossings, which are proved absent.
We use only the crossing-free subclass, not an unproved invariance theorem. -/
namespace TLMC684

structure CrossingFreeDiagram where
  projection : Circle → ℂ
  continuous_projection : Continuous projection
  injective_projection : Function.Injective projection

def roundDiagram : CrossingFreeDiagram :=
  ⟨fun z => z, continuous_subtype_val, Circle.coe_injective⟩

def DoublePoints (d : CrossingFreeDiagram) : Set Circle :=
  {x | ∃ y, y ≠ x ∧ d.projection y = d.projection x}

theorem doublePoints_empty (d : CrossingFreeDiagram) : DoublePoints d = ∅ := by
  ext x
  simp only [DoublePoints, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨y, hy, heq⟩
  exact hy (d.injective_projection heq)

theorem every_underpoint_choice_empty (d : CrossingFreeDiagram) (U : Set Circle)
    (hU : U ⊆ DoublePoints d) : U = ∅ := by
  ext x
  constructor
  · intro hx
    have h := hU hx
    simp only [doublePoints_empty, Set.mem_empty_iff_false] at h
  · intro hx
    exact False.elim hx

abbrev ArcSpace (d : CrossingFreeDiagram) := {x : Circle // x ∉ DoublePoints d}

def arcSpaceHomeomorph (d : CrossingFreeDiagram) : ArcSpace d ≃ₜ Circle where
  toFun := Subtype.val
  invFun x := ⟨x, by simp [doublePoints_empty]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

instance arcSpace_connected (d : CrossingFreeDiagram) : ConnectedSpace (ArcSpace d) :=
  (arcSpaceHomeomorph d).symm.surjective.connectedSpace
    (arcSpaceHomeomorph d).symm.continuous

abbrev Arc (d : CrossingFreeDiagram) := ConnectedComponents (ArcSpace d)

noncomputable instance uniqueArc (d : CrossingFreeDiagram) : Unique (Arc d) :=
  { default := ConnectedComponents.mk ((arcSpaceHomeomorph d).symm 1)
    uniq := fun _ => Subsingleton.elim _ _ }

/-- Actual ordered pairs of distinct circle points with the same planar projection. -/
abbrev ClassicalCrossing (d : CrossingFreeDiagram) :=
  {xy : Circle × Circle // xy.1 ≠ xy.2 ∧ d.projection xy.1 = d.projection xy.2}

theorem crossings_empty (d : CrossingFreeDiagram) : IsEmpty (ClassicalCrossing d) :=
  ⟨fun c => c.property.1 (d.injective_projection c.property.2)⟩

/-- No relation can be contributed by the proved-empty actual crossing set. -/
def crossingRelator (d : CrossingFreeDiagram) (c : ClassicalCrossing d) :
    FreeGroup (Arc d) := (crossings_empty d).elim c

def Relators (d : CrossingFreeDiagram) : Set (FreeGroup (Arc d)) :=
  Set.range (crossingRelator d)

theorem all_crossing_relation_rules_empty (d : CrossingFreeDiagram)
    (F : ClassicalCrossing d → FreeGroup (Arc d)) : Set.range F = ∅ := by
  ext r
  simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, _⟩
  exact (crossings_empty d).elim c

theorem relators_empty (d : CrossingFreeDiagram) : Relators d = ∅ := by
  ext r
  simp only [Relators, Set.mem_range, Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, _⟩
  exact (crossings_empty d).elim c

def DiagramGroup (d : CrossingFreeDiagram) := PresentedGroup (Relators d)
  deriving Group

theorem presentation_mk_injective (d : CrossingFreeDiagram) :
    Function.Injective (PresentedGroup.mk (Relators d)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  simp [MonoidHom.mem_ker, PresentedGroup.mk_eq_one_iff, relators_empty]

noncomputable def groupFreeEquiv (d : CrossingFreeDiagram) :
    DiagramGroup d ≃* FreeGroup (Arc d) :=
  (MulEquiv.ofBijective (PresentedGroup.mk (Relators d))
    ⟨presentation_mk_injective d, PresentedGroup.mk_surjective _⟩).symm

noncomputable def groupIntegerEquiv (d : CrossingFreeDiagram) :
    DiagramGroup d ≃* Multiplicative ℤ :=
  (groupFreeEquiv d).trans FreeGroup.mulEquivIntOfUnique

theorem group_finitely_generated (d : CrossingFreeDiagram) : Group.FG (DiagramGroup d) :=
  Group.fg_of_surjective (f := (groupFreeEquiv d).symm.toMonoidHom)
    (groupFreeEquiv d).symm.surjective

theorem group_infinite (d : CrossingFreeDiagram) : Infinite (DiagramGroup d) :=
  Infinite.of_injective (groupIntegerEquiv d).symm (groupIntegerEquiv d).symm.injective

/-- A genuine embedding into real three-space, written C x R, with this planar diagram. -/
def ClassicalRealization (d : CrossingFreeDiagram) : Prop :=
  ∃ k : Circle → ℂ × ℝ, Topology.IsEmbedding k ∧
    (∀ z, (k z).1 = d.projection z) ∧ ∀ z, (k z).2 = 0

theorem actual_classical_realization (d : CrossingFreeDiagram) : ClassicalRealization d := by
  let k : Circle → ℂ × ℝ := fun z => (d.projection z, 0)
  have hc : Continuous k := d.continuous_projection.prodMk continuous_const
  have hi : Function.Injective k := by
    intro x y h
    exact d.injective_projection (congrArg Prod.fst h)
  exact ⟨k, (hc.isClosedEmbedding hi).isEmbedding, fun _ => rfl, fun _ => rfl⟩

theorem round_realization_formula (z : Circle) :
    ‖(z : ℂ)‖ = 1 ∧ ((z : ℂ), (0 : ℝ)).1 = roundDiagram.projection z :=
  ⟨Circle.norm_coe z, rfl⟩

/-- The necessary forward implication already fails on an actual classical circle. -/
theorem no_classical_realization_implication_false :
    ¬ (∀ d : CrossingFreeDiagram,
      Group.FG (DiagramGroup d) ∧ Infinite (DiagramGroup d) →
        ¬ ClassicalRealization d) := by
  intro h
  exact h roundDiagram
    ⟨group_finitely_generated roundDiagram, group_infinite roundDiagram⟩
    (actual_classical_realization roundDiagram)

/-- Restriction of the proposed iff to actual crossing-free classical diagrams. -/
theorem nonclassical_criterion_false :
    ¬ (∀ d : CrossingFreeDiagram,
      (Group.FG (DiagramGroup d) ∧ Infinite (DiagramGroup d)) ↔
        ¬ ClassicalRealization d) := by
  intro h
  exact (h roundDiagram).mp
    ⟨group_finitely_generated roundDiagram, group_infinite roundDiagram⟩
    (actual_classical_realization roundDiagram)

end TLMC684
