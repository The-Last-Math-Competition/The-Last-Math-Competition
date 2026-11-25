import Std

namespace C501

def occupiedAndSeparators (lengths : List Nat) : Nat :=
  (lengths.map fun l => l + 1).sum

def pathJoinShift (lengths : List Nat) : Nat :=
  (lengths.map fun l => (l + 1) / 3).sum

theorem path_join_shift_le (lengths : List Nat) :
    pathJoinShift lengths ≤ occupiedAndSeparators lengths / 3 := by
  induction lengths with
  | nil => decide
  | cons length rest ih =>
    change (length + 1) / 3 + pathJoinShift rest ≤
      (length + 1 + occupiedAndSeparators rest) / 3
    omega

structure Runs (n : Nat) where
  lengths : List Nat
  positive : ∀ l ∈ lengths, 0 < l
  withinCycle : occupiedAndSeparators lengths ≤ n

inductive InducedShape (n : Nat) where
  | fullCycle
  | paths (runs : Runs n)

/-- The nonzero reduced homology degree of the full cycle complex, shifted by one. -/
def cycleShift (n : Nat) : Nat := n / 3 + if n % 3 = 2 then 1 else 0

theorem cycle_shift_eq_floor (n : Nat) : cycleShift n = (n + 1) / 3 := by
  unfold cycleShift
  split <;> omega

def ceilThird (n : Nat) : Nat := (n + 2) / 3

theorem ceil_third_is_least (n : Nat) :
    n ≤ 3 * ceilThird n ∧ ∀ k, n ≤ 3 * k → ceilThird n ≤ k := by
  unfold ceilThird
  constructor
  · omega
  · intro k bound
    omega

theorem cycle_shift_eq_ceiling {n : Nat} (positive : 0 < n) :
    cycleShift n = ceilThird (n - 1) := by
  rw [cycle_shift_eq_floor]
  unfold ceilThird
  omega

/-- The numerical homology support from the cycle and path independence complexes.
The argument `d` is one more than the homology degree. An empty list of paths
has shifted degree zero, as required for the empty vertex subset. -/
def HasShiftedHomology : InducedShape n → Nat → Prop
  | .fullCycle, d => d = cycleShift n
  | .paths runs, d =>
      (∀ l ∈ runs.lengths, l % 3 ≠ 1) ∧ d = pathJoinShift runs.lengths

theorem proper_shift_le {n d : Nat} {runs : Runs n}
    (nonzero : HasShiftedHomology (.paths runs) d) : d ≤ n / 3 := by
  have joinBound := path_join_shift_le runs.lengths
  have room := runs.withinCycle
  change (∀ l ∈ runs.lengths, l % 3 ≠ 1) ∧ d = pathJoinShift runs.lengths at nonzero
  rw [nonzero.2]
  omega

theorem supported_shift_le {n d : Nat} {s : InducedShape n}
    (nonzero : HasShiftedHomology s d) : d ≤ cycleShift n := by
  cases s with
  | fullCycle =>
    change d = cycleShift n at nonzero
    exact Nat.le_of_eq nonzero
  | paths runs =>
    have bound := proper_shift_le nonzero
    rw [cycle_shift_eq_floor]
    omega

/-- Hochster's nonvanishing condition at bidegrees `(i,i+d)`, after replacing
the actual induced independence complexes by their homology support data. -/
def HochsterSupport {Subset : Type} (size : Subset → Nat) (shape : Subset → InducedShape n)
    (quotientBetti : Nat → Nat → Prop) : Prop :=
  ∀ i d, quotientBetti i (i + d) ↔
    ∃ W, size W = i + d ∧ HasShiftedHomology (shape W) d

/-- `betti i j` says that the graded Betti number in bidegree `(i,j)` is nonzero. -/
def MaximalBettiShift (betti : Nat → Nat → Prop) (r : Nat) : Prop :=
  (∃ i, betti i (i + r)) ∧ ∀ d, (∃ i, betti i (i + d)) → d ≤ r

theorem quotient_regularity {Subset : Type} {n : Nat} (hn : 3 ≤ n)
    (size : Subset → Nat) (shape : Subset → InducedShape n) (full : Subset)
    (fullSize : size full = n) (fullShape : shape full = .fullCycle)
    {quotientBetti : Nat → Nat → Prop} (hochster : HochsterSupport size shape quotientBetti) :
    MaximalBettiShift quotientBetti (cycleShift n) := by
  constructor
  · let i := n - cycleShift n
    refine ⟨i, (hochster i (cycleShift n)).mpr ⟨full, ?_, ?_⟩⟩
    · rw [fullSize]
      have bound : cycleShift n ≤ n := by rw [cycle_shift_eq_floor]; omega
      dsimp [i]
      omega
    · simp [fullShape, HasShiftedHomology]
  · intro d ⟨i, nonzero⟩
    obtain ⟨W, _, hasHomology⟩ := (hochster i d).mp nonzero
    exact supported_shift_le hasHomology

theorem ideal_regularity {Subset : Type} {n : Nat} (hn : 3 ≤ n)
    (size : Subset → Nat) (shape : Subset → InducedShape n) (full : Subset)
    (fullSize : size full = n) (fullShape : shape full = .fullCycle)
    {quotientBetti idealBetti : Nat → Nat → Prop}
    (hochster : HochsterSupport size shape quotientBetti)
    (shift : ∀ i j, idealBetti i j ↔ quotientBetti (i + 1) j) :
    MaximalBettiShift idealBetti (ceilThird (n - 1) + 1) := by
  rw [← cycle_shift_eq_ceiling (by omega : 0 < n)]
  have quotientMax := quotient_regularity hn size shape full fullSize fullShape hochster
  constructor
  · let i := n - (cycleShift n + 1)
    have strict : cycleShift n < n := by rw [cycle_shift_eq_floor]; omega
    have rearrange : i + (cycleShift n + 1) = (i + 1) + cycleShift n := by omega
    refine ⟨i, (shift i _).mpr ?_⟩
    rw [rearrange]
    apply (hochster (i + 1) (cycleShift n)).mpr
    refine ⟨full, ?_, ?_⟩
    · rw [fullSize]
      dsimp [i]
      omega
    · simp [fullShape, HasShiftedHomology]
  · intro d ⟨i, nonzero⟩
    cases d with
    | zero => exact Nat.zero_le _
    | succ d =>
      have qNonzero := (shift i (i + (d + 1))).mp nonzero
      have difference : i + (d + 1) = (i + 1) + d := by omega
      rw [difference] at qNonzero
      exact Nat.succ_le_succ (quotientMax.2 d ⟨i + 1, qNonzero⟩)

#print axioms path_join_shift_le
#print axioms ideal_regularity

end C501
