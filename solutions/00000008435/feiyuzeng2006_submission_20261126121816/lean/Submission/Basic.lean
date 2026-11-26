import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ZMod.Basic

namespace Submission00000008435

/-- A finite incidence structure with indexed blocks. Indexing retains
multiplicities when taking intersections. -/
structure IncidenceDesign (Point Block : Type) where
  points : Finset Point
  blockIds : Finset Block
  block : Block → Finset Point

namespace IncidenceDesign

variable {Point Block : Type} [DecidableEq Point] [DecidableEq Block]

/-- The indices of blocks that contain the given subset. -/
def containing (D : IncidenceDesign Point Block) (U : Finset Point) : Finset Block :=
  D.blockIds.filter fun i => U ⊆ D.block i

/-- A finite (t)-design with block size (k) and index (lambda). -/
def IsTDesign (D : IncidenceDesign Point Block) (t k lam : ℕ) : Prop :=
  t ≤ k ∧ k < D.points.card ∧ 0 < lam ∧
  (∀ i ∈ D.blockIds, D.block i ⊆ D.points ∧ (D.block i).card = k) ∧
  (∀ U ∈ D.points.powersetCard t, (D.containing U).card = lam)

omit [DecidableEq Block] in
theorem IsTDesign.coverage {D : IncidenceDesign Point Block} {t k lam : ℕ}
    (h : D.IsTDesign t k lam) {U : Finset Point} (hU : U ⊆ D.points)
    (hcard : U.card = t) : (D.containing U).card = lam :=
  h.2.2.2.2 U (Finset.mem_powersetCard.mpr ⟨hU, hcard⟩)

/-- Distinct block indices denote distinct subsets. -/
def IsSimple (D : IncidenceDesign Point Block) : Prop :=
  ∀ i ∈ D.blockIds, ∀ j ∈ D.blockIds, D.block i = D.block j → i = j

def IsSymmetricBIBD (D : IncidenceDesign Point Block) (k lam : ℕ) : Prop :=
  D.IsTDesign 2 k lam ∧ D.IsSimple ∧ D.blockIds.card = D.points.card

/-- Derivation at block (A) restricts the other blocks to (A). -/
def deriveAtBlock (D : IncidenceDesign Point Block) (a : Block) :
    IncidenceDesign Point Block where
  points := D.block a
  blockIds := D.blockIds.erase a
  block i := D.block i ∩ D.block a

theorem containing_deriveAtBlock (D : IncidenceDesign Point Block)
    (a : Block) {U : Finset Point} (hU : U ⊆ D.block a) :
    (D.deriveAtBlock a).containing U = (D.containing U).erase a := by
  ext i
  change i ∈ (D.blockIds.erase a).filter (fun j => U ⊆ D.block j ∩ D.block a) ↔
    i ∈ (D.blockIds.filter (fun j => U ⊆ D.block j)).erase a
  constructor
  · intro hi
    obtain ⟨hi, hu⟩ := Finset.mem_filter.mp hi
    obtain ⟨hne, hi⟩ := Finset.mem_erase.mp hi
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr
      ⟨hi, hu.trans Finset.inter_subset_left⟩⟩
  · intro hi
    obtain ⟨hne, hi⟩ := Finset.mem_erase.mp hi
    obtain ⟨hi, hu⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hi⟩, Finset.subset_inter hu hU⟩

/-- Derivation at point (p) retains blocks through (p) and erases (p). -/
def deriveAtPoint (D : IncidenceDesign Point Block) (p : Point) :
    IncidenceDesign Point Block where
  points := D.points.erase p
  blockIds := D.blockIds.filter fun i => p ∈ D.block i
  block i := (D.block i).erase p

end IncidenceDesign

/-- Necessary design index in the asserted triple ((k,t,1)) under
block derivation of a symmetric BIBD. The block size is left unspecified. -/
def BlockParameterClaim : Prop :=
  ∀ (Point Block : Type) [DecidableEq Point] [DecidableEq Block]
    (D : IncidenceDesign Point Block) (k lam : ℕ) (a : Block),
    D.IsSymmetricBIBD k lam → a ∈ D.blockIds →
    ∃ s : ℕ, (D.deriveAtBlock a).IsTDesign 2 s 1

/-- Necessary point count in the same asserted triple under point derivation. -/
def PointParameterClaim : Prop :=
  ∀ (Point Block : Type) [DecidableEq Point] [DecidableEq Block]
    (D : IncidenceDesign Point Block) (k lam : ℕ) (p : Point),
    D.IsSymmetricBIBD k lam → p ∈ D.points →
    (D.deriveAtPoint p).points.card = k

/-- The complement of the nonzero squares in the additive group of order 11. -/
def seed : Finset (ZMod 11) := {0, 2, 6, 7, 8, 10}

/-- Develop the seed by all eleven translations. -/
def translatedDesign : IncidenceDesign (ZMod 11) (ZMod 11) where
  points := Finset.univ
  blockIds := Finset.univ
  block i := Finset.univ.filter fun x => x - i ∈ seed

def blockDerived : IncidenceDesign (ZMod 11) (ZMod 11) :=
  translatedDesign.deriveAtBlock 0

def pointDerived : IncidenceDesign (ZMod 11) (ZMod 11) :=
  translatedDesign.deriveAtPoint 0

private theorem original_blocks :
    ∀ i : ZMod 11, (translatedDesign.block i).card = 6 := by decide

private theorem original_pairs :
    ∀ x y : ZMod 11, x ≠ y →
      (translatedDesign.containing {x, y}).card = 3 := by decide

private theorem original_simple :
    ∀ i j : ZMod 11, translatedDesign.block i = translatedDesign.block j → i = j := by
  decide

theorem translated_design_parameters :
    translatedDesign.points.card = 11 ∧ translatedDesign.IsSymmetricBIBD 6 3 ∧
      translatedDesign.blockIds.card < translatedDesign.points.card.choose 6 := by
  refine ⟨by decide, ⟨?_, ?_, by decide⟩, by decide⟩
  · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · intro i _
      exact ⟨Finset.subset_univ _, original_blocks i⟩
    · intro U hU
      obtain ⟨x, y, hne, rfl⟩ :=
        Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hU).2
      exact original_pairs x y hne
  · intro i _ j _
    exact original_simple i j

private theorem block_intersection_sizes :
    ∀ i : ZMod 11, i ≠ 0 → (blockDerived.block i).card = 3 := by decide

private theorem block_derived_simple :
    ∀ i j : ZMod 11, i ≠ 0 → j ≠ 0 →
      blockDerived.block i = blockDerived.block j → i = j := by decide

theorem translated_block_coverage (a : ZMod 11) {U : Finset (ZMod 11)}
    (hU : U ⊆ (translatedDesign.deriveAtBlock a).points) (hcard : U.card = 2) :
    ((translatedDesign.deriveAtBlock a).containing U).card = 2 := by
  rw [IncidenceDesign.containing_deriveAtBlock translatedDesign a hU,
    Finset.card_erase_of_mem]
  · rw [translated_design_parameters.2.1.1.coverage (Finset.subset_univ _) hcard]
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hU⟩

theorem block_derived_parameters :
    blockDerived.points.card = 6 ∧ blockDerived.blockIds.card = 10 ∧
      blockDerived.IsTDesign 2 3 2 ∧ blockDerived.IsSimple := by
  refine ⟨by decide, by decide, ⟨by decide, by decide, by decide, ?_, ?_⟩, ?_⟩
  · intro i hi
    exact ⟨Finset.inter_subset_right, block_intersection_sizes i (Finset.mem_erase.mp hi).1⟩
  · intro U hU
    exact translated_block_coverage 0 (Finset.mem_powersetCard.mp hU).1
      (Finset.mem_powersetCard.mp hU).2
  · intro i hi j hj
    exact block_derived_simple i j (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hj).1

private theorem point_derived_sizes :
    ∀ i : ZMod 11, 0 ∈ translatedDesign.block i →
      (pointDerived.block i).card = 5 := by
  intro i hi
  exact (Finset.card_erase_of_mem hi).trans (congrArg (· - 1) (original_blocks i))

private theorem point_derived_singletons :
    ∀ x : ZMod 11, x ≠ 0 → (pointDerived.containing {x}).card = 3 := by decide

private theorem point_derived_simple :
    ∀ i j : ZMod 11, 0 ∈ translatedDesign.block i → 0 ∈ translatedDesign.block j →
      pointDerived.block i = pointDerived.block j → i = j := by decide

theorem point_derived_parameters :
    pointDerived.points.card = 10 ∧ pointDerived.blockIds.card = 6 ∧
      pointDerived.IsTDesign 1 5 3 ∧ pointDerived.IsSimple := by
  refine ⟨by decide, by decide, ⟨by decide, by decide, by decide, ?_, ?_⟩, ?_⟩
  · intro i hi
    exact ⟨Finset.erase_subset_erase _ (Finset.subset_univ _),
      point_derived_sizes i (Finset.mem_filter.mp hi).2⟩
  · intro U hU
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hU).2
    have hx : x ∈ pointDerived.points :=
      (Finset.mem_powersetCard.mp hU).1 (Finset.mem_singleton_self x)
    exact point_derived_singletons x (Finset.mem_erase.mp hx).1
  · intro i hi j hj
    exact point_derived_simple i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

private theorem pair_in_translated_block :
    ∀ a : ZMod 11, ({a, a + 2} : Finset (ZMod 11)) ⊆ translatedDesign.block a ∧
      ({a, a + 2} : Finset (ZMod 11)).card = 2 := by decide

/-- Every block choice violates the unit-index requirement for every block size. -/
theorem translated_block_parameter_failure (a : ZMod 11) (s : ℕ) :
    ¬ (translatedDesign.deriveAtBlock a).IsTDesign 2 s 1 := by
  intro h
  obtain ⟨hU, hcard⟩ := pair_in_translated_block a
  have htwo := translated_block_coverage a hU hcard
  have hone := h.coverage hU hcard
  exact (by decide : (2 : ℕ) ≠ 1) (htwo.symm.trans hone)

theorem translated_point_count (p : ZMod 11) :
    (translatedDesign.deriveAtPoint p).points.card = 10 := by
  change (translatedDesign.points.erase p).card = 10
  have hp : p ∈ translatedDesign.points := Finset.mem_univ p
  rw [Finset.card_erase_of_mem hp, translated_design_parameters.1]

theorem block_parameter_claim_false : ¬ BlockParameterClaim := by
  intro h
  obtain ⟨s, hs⟩ := h (ZMod 11) (ZMod 11) translatedDesign 6 3 0
    translated_design_parameters.2.1 (Finset.mem_univ 0)
  exact translated_block_parameter_failure 0 s hs

theorem point_parameter_claim_false : ¬ PointParameterClaim := by
  intro h
  have hsix := h (ZMod 11) (ZMod 11) translatedDesign 6 3 0
    translated_design_parameters.2.1 (Finset.mem_univ 0)
  exact (by decide : (10 : ℕ) ≠ 6) ((translated_point_count 0).symm.trans hsix)

/-- The parameter formula is a necessary conjunct under either convention. -/
theorem conjecture_00000008435_false (R S : Prop) :
    ¬ (BlockParameterClaim ∧ R ∧ S) ∧ ¬ (PointParameterClaim ∧ R ∧ S) :=
  ⟨fun h => block_parameter_claim_false h.1, fun h => point_parameter_claim_false h.1⟩

#print axioms translated_design_parameters
#print axioms block_derived_parameters
#print axioms point_derived_parameters
#print axioms conjecture_00000008435_false

end Submission00000008435
