import NumberParts
import StarHeap
import OutcomeBridge

/-!
Counterexample to the complete-invariant clause of TLMC 00000008872.
Every definition below uses genuine finite normal-play games. In particular,
atomic weight zero is verified through its defining far-star equivalence in
ALL finite game contexts, with arbitrarily large canonical Nim heaps.
-/
namespace TLMC8872

/-- Normal-play outcome, recorded as the first-player winning statuses of
Left and Right. Conway's comparison exactly determines these statuses. -/
def normalOutcome (g : Game) : Bool × Bool :=
  (!(le g zero), !(le zero g))

/-- Standard far-star equivalence, with 'arbitrarily large Nim heap' expressed
by eventual equality for each fixed arbitrary short-game context. -/
def FarStarEquiv (g h : Game) : Prop :=
  ∀ x : Game, ∃ N : Nat, ∀ n : Nat, N ≤ n →
    normalOutcome (add (add g x) (nimHeap n)) =
    normalOutcome (add (add h x) (nimHeap n))

/-- The zero fiber of the standard atomic-weight definition. An all-small
game has atomic weight zero exactly when it is far-star equivalent to zero:
this is the defining condition `0 · up =_farstar g`, since `0 · up = 0`.
We need no assertion or implementation for nonzero atomic weights. -/
def HasAtomicWeightZero (g : Game) : Prop := FarStarEquiv g zero

theorem zero_atomicWeightZero : HasAtomicWeightZero zero := by
  intro x
  exact ⟨0, fun _ _ => rfl⟩

/-- This includes every finite context and every sufficiently large Nim heap,
not a finite list of sample tests. -/
theorem star_farStarEquiv_zero : FarStarEquiv star zero := by
  intro x
  refine ⟨sizeOf x + 2, ?_⟩
  intro n hn
  change
    (!(le (add (add star x) (nimHeap n)) zero),
      !(le zero (add (add star x) (nimHeap n)))) =
    (!(le (add (add zero x) (nimHeap n)) zero),
      !(le zero (add (add zero x) (nimHeap n))))
  rw [← outcome_conway, ← outcome_conway, star_heap, zero_add]
  apply outcome_stable_between
  · unfold toggle
    split <;> omega
  · omega

theorem star_atomicWeightZero : HasAtomicWeightZero star :=
  star_farStarEquiv_zero

/-- A precise necessary consequence of the conjecture's claimed completeness:
the all-small games with the common weight zero and numerical part zero
would all have to be equivalent. -/
def CompleteZeroFiber : Prop :=
  ∀ g h : Game,
    AllSmall g → AllSmall h →
    HasAtomicWeightZero g → HasAtomicWeightZero h →
    NumericalPartZero g → NumericalPartZero h → Equiv g h

/-- The complete invariant assertion is false. -/
theorem not_completeZeroFiber : ¬ CompleteZeroFiber := by
  intro h
  exact zero_star_inequivalent
    (h zero star zero_allSmall star_allSmall
      zero_atomicWeightZero star_atomicWeightZero
      zero_numericalPartZero star_numericalPartZero)

/-- Full witness: equal atomic and numerical parts, distinct game values. -/
theorem counterexample :
    AllSmall zero ∧ AllSmall star ∧
    HasAtomicWeightZero zero ∧ HasAtomicWeightZero star ∧
    NumericalPartZero zero ∧ NumericalPartZero star ∧
    ¬ Equiv zero star :=
  ⟨zero_allSmall, star_allSmall, zero_atomicWeightZero, star_atomicWeightZero,
    zero_numericalPartZero, star_numericalPartZero, zero_star_inequivalent⟩

/-- Their outcomes already differ without adding any context. -/
theorem distinct_outcomes :
    normalOutcome zero = (false, false) ∧
    normalOutcome star = (true, true) := by
  simp [normalOutcome, zero, star, le_node]

/-- Standard recursive number-game condition. Added to check the source's
stronger wording that immediate options are number games. -/
inductive IsNumber : Game → Prop where
  | node {l r : List Game}
      (left : ∀ g ∈ l, IsNumber g)
      (right : ∀ g ∈ r, IsNumber g)
      (separated : ∀ g ∈ l, ∀ h ∈ r, Lt g h) : IsNumber (.node l r)

def OptionsAreNumbers : Game → Prop
  | .node l r => (∀ g ∈ l, IsNumber g) ∧ (∀ g ∈ r, IsNumber g)

theorem zero_isNumber : IsNumber zero :=
  .node (by simp) (by simp) (by simp)

theorem source_option_condition :
    OptionsAreNumbers zero ∧ OptionsAreNumbers star := by
  constructor
  · simp [OptionsAreNumbers, zero]
  · simpa [OptionsAreNumbers, star] using And.intro zero_isNumber zero_isNumber

/-- The same necessary completeness consequence on the source's explicitly
restricted domain: every immediate option must itself be a number game. -/
def CompleteSourceZeroFiber : Prop :=
  ∀ g h : Game,
    AllSmall g → AllSmall h →
    OptionsAreNumbers g → OptionsAreNumbers h →
    HasAtomicWeightZero g → HasAtomicWeightZero h →
    NumericalPartZero g → NumericalPartZero h → Equiv g h

/-- Completeness fails even with the source's number-options restriction. -/
theorem not_completeSourceZeroFiber : ¬ CompleteSourceZeroFiber := by
  intro h
  exact zero_star_inequivalent
    (h zero star zero_allSmall star_allSmall
      source_option_condition.1 source_option_condition.2
      zero_atomicWeightZero star_atomicWeightZero
      zero_numericalPartZero star_numericalPartZero)

#print axioms counterexample
#print axioms not_completeZeroFiber
#print axioms not_completeSourceZeroFiber
#print axioms star_farStarEquiv_zero
#print axioms distinct_outcomes
#print axioms source_option_condition

end TLMC8872
