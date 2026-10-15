import Std

/-!
# A counterexample to conjecture 00000006238

The conjecture identifies the fixed points of complement with clopen
subobjects. We construct the complete powerset lattice of the discrete
two-point space, with its actual set complement and topology. Its singleton
is nonempty, proper, and clopen, but not fixed by complement.
-/

namespace Conjecture6238

abbrev Subset (X : Type) := X → Prop

def empty {X : Type} : Subset X := fun _ => False
def whole {X : Type} : Subset X := fun _ => True
def complement {X : Type} (A : Subset X) : Subset X := fun x => ¬ A x
def intersection {X : Type} (A B : Subset X) : Subset X := fun x => A x ∧ B x
def union {X : Type} (A B : Subset X) : Subset X := fun x => A x ∨ B x
def Included {X : Type} (A B : Subset X) : Prop := ∀ x, A x → B x
def supremum {X : Type} (F : Subset X → Prop) : Subset X :=
  fun x => ∃ A, F A ∧ A x
def infimum {X : Type} (F : Subset X → Prop) : Subset X :=
  fun x => ∀ A, F A → A x

/-- Arbitrary families have a least upper bound: powerset completeness. -/
theorem supremum_is_lub {X : Type} (F : Subset X → Prop) :
    (∀ A, F A → Included A (supremum F)) ∧
    (∀ B, (∀ A, F A → Included A B) → Included (supremum F) B) := by
  constructor
  · intro A hA x hx
    exact ⟨A, hA, hx⟩
  · intro B hB x hx
    obtain ⟨A, hA, hAx⟩ := hx
    exact hB A hA x hAx

/-- Arbitrary families also have a greatest lower bound. -/
theorem infimum_is_glb {X : Type} (F : Subset X → Prop) :
    (∀ A, F A → Included (infimum F) A) ∧
    (∀ B, (∀ A, F A → Included B A) → Included B (infimum F)) := by
  constructor
  · intro A hA x hx
    exact hx A hA
  · intro B hB x hx A hA
    exact hB A hA x hx

theorem complement_square {X : Type} (A : Subset X) :
    complement (complement A) = A := by
  classical
  funext x
  apply propext
  constructor
  · intro h
    exact Classical.byContradiction h
  · intro h hn
    exact hn h

theorem complement_meet {X : Type} (A : Subset X) :
    intersection A (complement A) = empty := by
  funext x
  apply propext
  exact ⟨fun h => h.2 h.1, False.elim⟩

theorem complement_join {X : Type} (A : Subset X) :
    union A (complement A) = whole := by
  classical
  funext x
  apply propext
  exact ⟨fun _ => True.intro, fun _ => Classical.em (A x)⟩

theorem complement_reverses_inclusion {X : Type} (A B : Subset X)
    (h : Included A B) : Included (complement B) (complement A) := by
  intro x hnB hA
  exact hnB (h x hA)

/-- The topology axioms, including unions of arbitrary families of opens. -/
structure Topology (X : Type) where
  isOpen : Subset X → Prop
  empty_open : isOpen empty
  whole_open : isOpen whole
  intersection_open : ∀ A B, isOpen A → isOpen B → isOpen (intersection A B)
  supremum_open : ∀ F, (∀ A, F A → isOpen A) → isOpen (supremum F)

def IsClosed {X : Type} (T : Topology X) (A : Subset X) : Prop :=
  T.isOpen (complement A)

def IsClopen {X : Type} (T : Topology X) (A : Subset X) : Prop :=
  T.isOpen A ∧ IsClosed T A

def IsFixed {X : Type} (A : Subset X) : Prop := complement A = A

/-- Complement has no fixed subset whenever an ambient point is available. -/
theorem no_fixed_subset {X : Type} (x : X) (A : Subset X) : ¬ IsFixed A := by
  intro h
  have he : (¬ A x) = A x := congrArg (fun S => S x) h
  have hn : ¬ A x := fun hx => (Eq.mpr he hx) hx
  exact hn (Eq.mp he hn)

def discreteTwo : Topology Bool where
  isOpen := fun _ => True
  empty_open := True.intro
  whole_open := True.intro
  intersection_open := fun _ _ _ _ => True.intro
  supremum_open := fun _ _ => True.intro

def singleton : Subset Bool := fun x => x = false

theorem singleton_nonempty : ∃ x, singleton x := ⟨false, rfl⟩

theorem singleton_proper : ∃ x, ¬ singleton x := by
  exact ⟨true, Bool.noConfusion⟩

theorem singleton_clopen : IsClopen discreteTwo singleton :=
  ⟨True.intro, True.intro⟩

theorem singleton_complement : complement singleton = (fun x : Bool => x = true) := by
  funext x
  apply propext
  unfold complement singleton
  cases x <;> decide

theorem singleton_not_fixed : ¬ IsFixed singleton :=
  no_fixed_subset false singleton

/-- The exact fixed-point assertion, restricted to this admissible space. -/
def DiscreteFixedPointClaim : Prop :=
  ∀ A : Subset Bool, IsFixed A ↔ IsClopen discreteTwo A

theorem not_discrete_fixed_point_claim : ¬ DiscreteFixedPointClaim := by
  intro h
  exact singleton_not_fixed ((h singleton).mpr singleton_clopen)

/-- The corresponding universal topological assertion is false. -/
def UniversalFixedPointClaim : Prop :=
  ∀ (X : Type) (T : Topology X) (A : Subset X), IsFixed A ↔ IsClopen T A

theorem not_universal_fixed_point_claim : ¬ UniversalFixedPointClaim := by
  intro h
  exact not_discrete_fixed_point_claim (h Bool discreteTwo)

/-- Any larger conjunction containing the disputed clause is refuted. -/
theorem refutes_every_claim_covering_discrete_case (C : Prop)
    (h : C → DiscreteFixedPointClaim) : ¬ C := by
  intro hc
  exact not_discrete_fixed_point_claim (h hc)

end Conjecture6238

#print axioms Conjecture6238.complement_square
#print axioms Conjecture6238.no_fixed_subset
#print axioms Conjecture6238.not_discrete_fixed_point_claim
#print axioms Conjecture6238.not_universal_fixed_point_claim
#print axioms Conjecture6238.refutes_every_claim_covering_discrete_case
