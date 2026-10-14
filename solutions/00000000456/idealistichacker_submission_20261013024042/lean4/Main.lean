import Std
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Conjecture456
abbrev Triple (k : Nat) := Fin k × Fin k × Fin k
abbrev Columns := Triple 2
abbrev Labels := Triple 3
abbrev Obj := Columns × Labels
inductive Step where
  | north | east
  deriving DecidableEq, Repr
open Step
def triples (k : Nat) : List (Triple k) :=
  (List.finRange k).flatMap fun a =>
    (List.finRange k).flatMap fun b =>
      (List.finRange k).map fun c => (a,b,c)
def path (c : Columns) : List Step :=
  List.replicate c.1.val east ++ [north] ++
  List.replicate (c.2.1.val - c.1.val) east ++ [north] ++
  List.replicate (c.2.2.val - c.2.1.val) east ++ [north] ++
  List.replicate (2 - c.2.2.val) east
def above (x y : Nat) : List Step → Bool
  | [] => decide (3*x ≤ 2*y)
  | s::ss => decide (3*x ≤ 2*y) &&
      match s with
      | north => above x (y+1) ss
      | east => above (x+1) y ss
def pathGood (c : Columns) : Prop :=
  c.1 ≤ c.2.1 ∧ c.2.1 ≤ c.2.2 ∧
  (path c).count north = 3 ∧ (path c).count east = 2 ∧
  above 0 0 (path c) = true
instance (c : Columns) : Decidable (pathGood c) := by unfold pathGood; infer_instance
def sortedColumns (c : Columns) : Prop :=
  c.1 ≤ c.2.1 ∧ c.2.1 ≤ c.2.2 ∧
  3*c.1.val ≤ 0 ∧ 3*c.2.1.val ≤ 2 ∧ 3*c.2.2.val ≤ 4
instance (c : Columns) : Decidable (sortedColumns c) := by unfold sortedColumns; infer_instance
def labelGood (c : Columns) (l : Labels) : Prop :=
  l.1 ≠ l.2.1 ∧ l.1 ≠ l.2.2 ∧ l.2.1 ≠ l.2.2 ∧
  (c.1 = c.2.1 → l.1 < l.2.1) ∧
  (c.1 = c.2.2 → l.1 < l.2.2) ∧
  (c.2.1 = c.2.2 → l.2.1 < l.2.2)
instance (c : Columns) (l : Labels) : Decidable (labelGood c l) := by unfold labelGood; infer_instance
def valid (o : Obj) : Prop := pathGood o.1 ∧ labelGood o.1 o.2
instance (o : Obj) : Decidable (valid o) := by unfold valid; infer_instance
def allObjects : List Obj :=
  (triples 2).flatMap fun c => (triples 3).map fun l => (c,l)
def parking : List Obj := allObjects.filter fun o => decide (valid o)
def expected : List Obj := [
  ((0,0,0),(0,1,2)),
  ((0,0,1),(0,1,2)),
  ((0,0,1),(0,2,1)),
  ((0,0,1),(1,2,0))]
def prefAt (c : Columns) (l : Labels) (j : Fin 3) : Fin 2 :=
  if l.1 = j then c.1 else if l.2.1 = j then c.2.1 else c.2.2
def preferences (o : Obj) : Triple 2 :=
  (prefAt o.1 o.2 0, prefAt o.1 o.2 1, prefAt o.1 o.2 2)
def expectedPreferences : List (Triple 2) := [(0,0,0),(0,0,1),(0,1,0),(1,0,0)]
def words : Nat → List (List Step)
  | 0 => [[]]
  | n+1 => (words n).map (north :: ·) ++ (words n).map (east :: ·)
def wordGood (w : List Step) : Prop :=
  w.count north = 3 ∧ w.count east = 2 ∧ above 0 0 w = true
instance (w : List Step) : Decidable (wordGood w) := by unfold wordGood; infer_instance
def dyckWords := (words 5).filter fun w => decide (wordGood w)
theorem word_universe (n : Nat) (w : List Step) : w ∈ words n ↔ w.length = n := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons s w => cases s <;> simp [words, ih]
theorem raw_word_bridge : dyckWords = ((triples 2).filter fun c => decide (pathGood c)).map path := by decide
theorem dyck_words_exact : dyckWords = [[north,north,north,east,east],[north,north,east,north,east]] := by decide
theorem path_injective : ∀ c d : Columns,
  pathGood c → pathGood d → path c = path d → c = d := by simp only [Prod.forall]; decide
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1)*factorial n
theorem coprime : Nat.gcd 3 2 = 1 := by decide
theorem path_sorted_bridge : ∀ c : Columns, pathGood c ↔ sortedColumns c := by simp only [Prod.forall]; decide
theorem universe_complete : ∀ o : Obj, o ∈ allObjects := by simp only [Prod.forall]; decide
theorem universe_nodup : allObjects.Nodup := by decide
theorem parking_membership : ∀ o : Obj, o ∈ parking ↔ valid o := by simp only [Prod.forall]; decide
theorem parking_exact : parking = expected := by decide
theorem parking_nodup : parking.Nodup := by decide
theorem parking_count : parking.length = 4 := by decide
theorem preference_image : parking.map preferences = expectedPreferences := by decide
theorem preferences_injective : ∀ o v : Obj,
  valid o → valid v → preferences o = preferences v → o = v := by simp only [Prod.forall]; decide
theorem ratio_height_first : factorial (3+2-1) / factorial (3-1) = 12 := by decide
theorem necessary_count_clause_false :
  parking.length ≠ factorial (3+2-1) / factorial (3-1) := by decide

theorem labels_exhaustive : ∀ c : Columns, ∀ l : Labels,
  labelGood c l → ∀ j : Fin 3, j = l.1 ∨ j = l.2.1 ∨ j = l.2.2 := by
  simp only [Prod.forall]
  decide

def evalCoefficients : List Nat → Nat → Nat
  | [], _ => 0
  | a :: as, q => a + q * evalCoefficients as q

theorem eval_at_one (as : List Nat) : evalCoefficients as 1 = as.sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [evalCoefficients, ih]

def RequiredPositiveRefinement (as : List Nat) : Prop :=
  evalCoefficients as 1 = parking.length ∧
  evalCoefficients as 1 = factorial (3+2-1) / factorial (3-1)

theorem no_positive_refinement_at_witness :
  ¬ ∃ as : List Nat, RequiredPositiveRefinement as := by
  rintro ⟨as, h⟩
  exact necessary_count_clause_false (h.1.symm.trans h.2)

theorem expanded_specialization_negation :
  ¬ ∃ as : List Nat,
    evalCoefficients as 1 = (allObjects.filter fun o => decide (valid o)).length ∧
    evalCoefficients as 1 = factorial (3+2-1) / factorial (3-1) := by
  exact no_positive_refinement_at_witness
end Conjecture456
