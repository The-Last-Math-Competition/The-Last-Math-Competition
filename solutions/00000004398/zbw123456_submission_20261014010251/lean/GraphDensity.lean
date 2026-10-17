import Init
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace GraphDensity
abbrev Graph (n : Nat) := Fin n → Fin n → Bool
def Simple {n : Nat} (G : Graph n) : Prop :=
  (∀ i, G i i = false) ∧ (∀ i j, G i j = G j i)
def complete (n : Nat) : Graph n := fun i j => decide (i ≠ j)
/-- Every map from m labelled vertices to n vertices, built by choosing its
first value and then its remaining values. -/
def allMaps : (m n : Nat) → List (Fin m → Fin n)
  | 0, _ => [fun i => Fin.elim0 i]
  | m+1, n => (List.finRange n).flatMap fun v =>
      (allMaps m n).map fun f => Fin.cases v f

/-- The enumeration omits no vertex map. -/
theorem mem_allMaps (m n : Nat) (f : Fin m → Fin n) : f ∈ allMaps m n := by
  induction m with
  | zero =>
    have hf : f = (fun i => Fin.elim0 i) := by funext i; exact Fin.elim0 i
    simp [allMaps, hf]
  | succ m ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, ?_, ?_⟩
    · apply List.mem_ofFn.mpr
      exact ⟨f 0, rfl⟩
    · apply List.mem_map.mpr
      refine ⟨fun i => f i.succ, ih _, ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp

def isHom {m n : Nat} (F : Graph m) (G : Graph n) (f : Fin m → Fin n) : Bool :=
  (List.finRange m).all fun i => (List.finRange m).all fun j =>
    !(F i j) || G (f i) (f j)
def homCount {m n : Nat} (F : Graph m) (G : Graph n) : Nat :=
  ((allMaps m n).filter (isHom F G)).length
/-- Equality of homomorphism densities, with denominators cleared. -/
def SameDensity {m n k : Nat} (F : Graph m) (G : Graph n) (H : Graph k) : Prop :=
  homCount F G * k^m = homCount F H * n^m
/-- The precise single-density definition printed in the problem. -/
def Forcing {m : Nat} (F : Graph m) : Prop :=
  ∀ (n k : Nat), 0 < n → 0 < k → ∀ (G : Graph n) (H : Graph k),
  Simple G → Simple H → SameDensity F G H →
  ∀ (r : Nat) (J : Graph r), Simple J → SameDensity J G H
/-- A triangle and an isolated vertex. -/
def triangleIsolate : Graph 4 := fun i j =>
  decide (i.val < 3 ∧ j.val < 3 ∧ i ≠ j)
/-- The three-leaf star. -/
def star : Graph 4 := fun i j =>
  decide ((i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0))

theorem simple_examples : Simple triangleIsolate ∧ Simple star := by unfold Simple; decide
/-- Exact size and absence of duplicate tuples in the two enumerations
used in this counterexample. Coverage is mem_allMaps above. -/
theorem enumeration_two : (allMaps 2 4).length=16 ∧
    ((allMaps 2 4).map (fun f => [f 0,f 1])).Nodup := by decide
theorem enumeration_three : (allMaps 3 4).length=64 ∧
    ((allMaps 3 4).map (fun f => [f 0,f 1,f 2])).Nodup := by decide

theorem edge_counts : homCount (complete 2) triangleIsolate = 6 ∧
    homCount (complete 2) star = 6 := by decide
theorem triangle_counts : homCount (complete 3) triangleIsolate = 6 ∧
    homCount (complete 3) star = 0 := by decide

theorem complete_two_not_forcing : ¬ Forcing (complete 2) := by
  intro h
  have he : SameDensity (complete 2) triangleIsolate star := by unfold SameDensity; decide
  have htri := h 4 4 (by decide) (by decide) triangleIsolate star
    simple_examples.1 simple_examples.2 he 3 (complete 3) (by unfold Simple; decide)
  exact (by unfold SameDensity; decide : ¬ SameDensity (complete 3) triangleIsolate star) htri

/-- It already fails to include all complete graphs, so the asserted exact
classification (complete graphs together with complete bipartite graphs) fails. -/
theorem not_all_complete_forcing : ¬ (∀ n, 0 < n → Forcing (complete n)) := by
  intro h
  exact complete_two_not_forcing (h 2 (by decide))
#print axioms complete_two_not_forcing
#print axioms not_all_complete_forcing
end GraphDensity
