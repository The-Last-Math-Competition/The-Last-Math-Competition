import Std

namespace Conjecture9614

def iterate {X : Type} (step : X → X) : Nat → X → X
  | 0, value => value
  | n + 1, value => iterate step n (step value)

theorem iterate_add {X : Type} (step : X → X) (a b : Nat) (x : X) :
    iterate step (a + b) x = iterate step b (iterate step a x) := by
  induction a generalizing x with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [Nat.succ_add]
    exact ih (step x)

theorem iterate_step {X : Type} (step : X → X) (n : Nat) (x : X) :
    iterate step n (step x) = step (iterate step n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (step x)

/-- The first coordinate is the stage. Two representatives are equal if some
    common later stage sends them to the same vector. -/
def EventuallyEqual {X : Type} (step : X → X) (p q : Nat × X) : Prop :=
  ∃ a b : Nat, p.1 + a = q.1 + b ∧ iterate step a p.2 = iterate step b q.2

def stationarySetoid {X : Type} (step : X → X) : Setoid (Nat × X) where
  r := EventuallyEqual step
  iseqv := {
    refl := fun p => ⟨0, 0, rfl, rfl⟩
    symm := by
      intro p q equal
      obtain ⟨a, b, time, value⟩ := equal
      exact ⟨b, a, time.symm, value.symm⟩
    trans := by
      intro p q r first second
      obtain ⟨a, b, time₁, value₁⟩ := first
      obtain ⟨c, d, time₂, value₂⟩ := second
      refine ⟨a + c, d + b, by omega, ?_⟩
      calc
        iterate step (a + c) p.2 = iterate step c (iterate step a p.2) := iterate_add _ _ _ _
        _ = iterate step c (iterate step b q.2) := congrArg (iterate step c) value₁
        _ = iterate step (b + c) q.2 := (iterate_add _ _ _ _).symm
        _ = iterate step (c + b) q.2 := by rw [Nat.add_comm b c]
        _ = iterate step b (iterate step c q.2) := iterate_add _ _ _ _
        _ = iterate step b (iterate step d r.2) := congrArg (iterate step b) value₂
        _ = iterate step (d + b) r.2 := (iterate_add _ _ _ _).symm
  }

def StationaryLimit {X : Type} (step : X → X) := Quotient (stationarySetoid step)

/-- The first step factors through a smaller state space R, on which the
    transition is invertible. This includes R=X with projection the identity. -/
structure Representatives {X : Type} (step : X → X) (R : Type) where
  project : X → R
  embed : R → X
  move : R → R
  undo : R → R
  projectEmbed : ∀ r, project (embed r) = r
  undoMove : ∀ r, undo (move r) = r
  moveUndo : ∀ r, move (undo r) = r
  factorStep : ∀ value, step value = embed (move (project value))

namespace Representatives

variable {X R : Type} {step : X → X} (data : Representatives step R)

def atStage (p : Nat × X) : R := iterate data.undo p.1 (data.project p.2)

private theorem project_step (x : X) : data.project (step x) = data.move (data.project x) := by
  rw [data.factorStep, data.projectEmbed]

private theorem project_iterate (n : Nat) (x : X) :
    data.project (iterate step n x) = iterate data.move n (data.project x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change data.project (iterate step n (step x)) =
      iterate data.move n (data.move (data.project x))
    rw [ih, data.project_step]

private theorem at_stage_step (n : Nat) (x : X) :
    data.atStage (n + 1, step x) = data.atStage (n, x) := by
  change iterate data.undo n (data.undo (data.project (step x))) =
    iterate data.undo n (data.project x)
  rw [data.project_step, data.undoMove]

private theorem at_stage_advance (n a : Nat) (x : X) :
    data.atStage (n + a, iterate step a x) = data.atStage (n, x) := by
  induction a generalizing n x with
  | zero => rfl
  | succ a ih =>
    change data.atStage (n + (a + 1), iterate step a (step x)) = data.atStage (n, x)
    rw [show n + (a + 1) = n + 1 + a by omega, ih, data.at_stage_step]

private theorem at_stage_respects_limit {p q : Nat × X}
    (equal : EventuallyEqual step p q) : data.atStage p = data.atStage q := by
  obtain ⟨a, b, time, value⟩ := equal
  calc
    data.atStage p = data.atStage (p.1 + a, iterate step a p.2) :=
      (data.at_stage_advance p.1 a p.2).symm
    _ = data.atStage (q.1 + b, iterate step b q.2) := by rw [time, value]
    _ = data.atStage q := data.at_stage_advance q.1 b q.2

private theorem iterate_move_undo (n : Nat) (r : R) :
    iterate data.move n (iterate data.undo n r) = r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    change iterate data.move n (data.move (iterate data.undo n (data.undo r))) = r
    rw [iterate_step data.undo, data.moveUndo, ih]

private theorem stage_zero_representative (n : Nat) (x : X) :
    EventuallyEqual step (n, x) (0, data.embed (data.atStage (n, x))) := by
  refine ⟨1, n + 1, by simp, ?_⟩
  change step x = iterate step n (step (data.embed (data.atStage (n, x))))
  rw [iterate_step, data.factorStep (iterate step n (data.embed (data.atStage (n, x))))]
  rw [data.project_iterate, data.projectEmbed]
  change step x = data.embed
    (data.move (iterate data.move n (iterate data.undo n (data.project x))))
  rw [data.iterate_move_undo, data.factorStep]

def evaluate (value : StationaryLimit step) : R :=
  Quotient.lift data.atStage (fun _ _ h => data.at_stage_respects_limit h) value

def representative (r : R) : StationaryLimit step := Quotient.mk _ (0, data.embed r)

theorem evaluate_representative (r : R) : data.evaluate (data.representative r) = r :=
  data.projectEmbed r

theorem representative_evaluate (value : StationaryLimit step) :
    data.representative (data.evaluate value) = value := by
  induction value using Quotient.inductionOn with
  | h p =>
    apply Eq.symm
    apply Quotient.sound
    exact data.stage_zero_representative p.1 p.2

end Representatives

abbrev F3 := Fin 3
abbrev PairVector := F3 × F3
abbrev TripleVector := F3 × F3 × F3

def stepA (v : PairVector) : PairVector :=
  let sum := v.1 + v.2
  (sum, sum)

def stepB (v : TripleVector) : TripleVector :=
  (v.2.1 + v.2.2, v.1 + v.2.2, v.1 + v.2.1)

def inverseB (v : TripleVector) : TripleVector :=
  let twiceSum := 2 * (v.1 + v.2.1 + v.2.2)
  (twiceSum - v.1, twiceSum - v.2.1, twiceSum - v.2.2)

private theorem residue_cases (a : F3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  have bound := a.isLt
  have values : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 := by omega
  rcases values with zero | one | two
  · exact Or.inl (Fin.ext zero)
  · exact Or.inr (Or.inl (Fin.ext one))
  · exact Or.inr (Or.inr (Fin.ext two))

private def double (r : F3) : F3 := r + r

private theorem double_double (r : F3) : double (double r) = r := by
  rcases residue_cases r with rfl | rfl | rfl <;> decide

def representativesA : Representatives stepA F3 where
  project := fun v => v.1 + v.2
  embed := fun r => (double r, double r)
  move := double
  undo := double
  projectEmbed := double_double
  undoMove := double_double
  moveUndo := double_double
  factorStep := by
    intro v
    change (v.1 + v.2, v.1 + v.2) = (double (double (v.1 + v.2)), double (double (v.1 + v.2)))
    rw [double_double]

theorem inverseB_stepB (v : TripleVector) : inverseB (stepB v) = v := by
  obtain ⟨a, b, c⟩ := v
  rcases residue_cases a with rfl | rfl | rfl <;>
    rcases residue_cases b with rfl | rfl | rfl <;>
    rcases residue_cases c with rfl | rfl | rfl <;> decide

theorem stepB_inverseB (v : TripleVector) : stepB (inverseB v) = v := by
  obtain ⟨a, b, c⟩ := v
  rcases residue_cases a with rfl | rfl | rfl <;>
    rcases residue_cases b with rfl | rfl | rfl <;>
    rcases residue_cases c with rfl | rfl | rfl <;> decide

def representativesB : Representatives stepB TripleVector where
  project := id
  embed := id
  move := stepB
  undo := inverseB
  projectEmbed := fun _ => rfl
  undoMove := inverseB_stepB
  moveUndo := stepB_inverseB
  factorStep := fun _ => rfl

def tripleEnumeration : List TripleVector :=
  (List.finRange 3).flatMap fun a =>
    (List.finRange 3).flatMap fun b =>
      (List.finRange 3).map fun c => (a, b, c)

private theorem residue_mem_enumeration (a : F3) : a ∈ List.finRange 3 := by
  rcases residue_cases a with rfl | rfl | rfl <;> decide

theorem triple_enumeration_complete (v : TripleVector) : v ∈ tripleEnumeration := by
  obtain ⟨a, b, c⟩ := v
  exact List.mem_flatMap.mpr ⟨a, residue_mem_enumeration a,
    List.mem_flatMap.mpr ⟨b, residue_mem_enumeration b,
      List.mem_map.mpr ⟨c, residue_mem_enumeration c, rfl⟩⟩⟩

theorem enumeration_sizes :
    (List.finRange 3).length = 3 ∧ (List.finRange 3).Nodup ∧
    tripleEnumeration.length = 27 ∧ tripleEnumeration.Nodup := by decide

private theorem add_one_ne (a : F3) : a + 1 ≠ a := by
  rcases residue_cases a with rfl | rfl | rfl <;> decide

private theorem no_residue_surjection (f : F3 → TripleVector) :
    ¬ (∀ vector, ∃ r, f r = vector) := by
  intro onto
  let missing : TripleVector := ((f 0).1 + 1, (f 1).2.1 + 1, (f 2).2.2 + 1)
  obtain ⟨r, equal⟩ := onto missing
  rcases residue_cases r with rfl | rfl | rfl
  · exact add_one_ne (f 0).1 (congrArg Prod.fst equal.symm)
  · exact add_one_ne (f 1).2.1 (congrArg (fun v => v.2.1) equal.symm)
  · exact add_one_ne (f 2).2.2 (congrArg (fun v => v.2.2) equal.symm)

theorem no_stationary_surjection :
    ¬ ∃ f : StationaryLimit stepA → StationaryLimit stepB,
      ∀ target, ∃ source, f source = target := by
  intro ⟨f, onto⟩
  let reduced : F3 → TripleVector := fun r =>
    representativesB.evaluate (f (representativesA.representative r))
  apply no_residue_surjection reduced
  intro vector
  obtain ⟨source, equal⟩ := onto (representativesB.representative vector)
  refine ⟨representativesA.evaluate source, ?_⟩
  change representativesB.evaluate
    (f (representativesA.representative (representativesA.evaluate source))) = vector
  rw [Representatives.representative_evaluate, equal, Representatives.evaluate_representative]

end Conjecture9614

#print axioms Conjecture9614.Representatives.evaluate_representative
#print axioms Conjecture9614.Representatives.representative_evaluate
#print axioms Conjecture9614.inverseB_stepB
#print axioms Conjecture9614.stepB_inverseB
#print axioms Conjecture9614.enumeration_sizes
#print axioms Conjecture9614.no_stationary_surjection
