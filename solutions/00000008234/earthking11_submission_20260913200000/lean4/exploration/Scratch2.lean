import Std

set_option maxRecDepth 1000000

namespace Scratch2

abbrev Alloc (n m : Nat) := Fin m → Fin n

def bsize {n m : Nat} (a : Alloc n m) (i : Fin n) : Nat :=
  ((List.finRange m).filter (fun g => decide (a g = i))).length

/-- Unit additive valuation: the value of a bundle is its cardinality. -/
abbrev value {n m : Nat} (a : Alloc n m) (i : Fin n) : Nat := bsize a i

/-- Agent `i` envies agent `j` when `j`'s bundle is worth strictly more. -/
abbrev envy {n m : Nat} (a : Alloc n m) (i j : Fin n) : Prop := value a i < value a j

/-- EF1 exactly as defined: every ordered pair `(i,j)` is envy-free after removing
some good from `j`'s bundle (or was already envy-free). -/
def ef1 {n m : Nat} (a : Alloc n m) : Prop :=
  ∀ i j : Fin n, ¬ envy a i j ∨ ∃ g : Fin m, a g = j ∧ value a j - 1 ≤ value a i

/-- Computable size-gap form of EF1 under unit valuations. -/
def isEF1 {n m : Nat} (a : Alloc n m) : Bool :=
  (List.finRange n).all (fun i =>
    (List.finRange n).all (fun j => decide (bsize a j ≤ bsize a i + 1)))

abbrev hamming {n m : Nat} (a b : Alloc n m) : Nat :=
  ((List.finRange m).filter (fun g => decide (a g ≠ b g))).length

abbrev Adj {n m : Nat} (a b : Alloc n m) : Prop := hamming a b = 1

def alloc00 : Alloc 2 2 := fun _ => 0
def alloc01 : Alloc 2 2 := fun g => g
def alloc10 : Alloc 2 2 := fun g => if g = 0 then 1 else 0
def alloc11 : Alloc 2 2 := fun _ => 1

theorem fin2_forall {C : Fin 2 → Prop} (h0 : C 0) (h1 : C 1) : ∀ g, C g :=
  Fin.cases (motive := fun g => C g) h0
    (fun i => Fin.cases (motive := fun k => C (Fin.succ k)) h1
      (fun j => Fin.elim0 j) i)

theorem fin2_val_cases (x : Fin 2) : x = 0 ∨ x = 1 :=
  fin2_forall (C := fun y => y = 0 ∨ y = 1) (Or.inl rfl) (Or.inr rfl) x

theorem value_alloc01 (i : Fin 2) : value alloc01 i = 1 :=
  fin2_forall (C := fun i => value alloc01 i = 1) (by decide) (by decide) i

theorem value_alloc10 (i : Fin 2) : value alloc10 i = 1 :=
  fin2_forall (C := fun i => value alloc10 i = 1) (by decide) (by decide) i

theorem value_alloc00_zero : value alloc00 0 = 2 := by decide
theorem value_alloc00_one : value alloc00 1 = 0 := by decide
theorem value_alloc11_zero : value alloc11 0 = 0 := by decide
theorem value_alloc11_one : value alloc11 1 = 2 := by decide

theorem ef1_alloc01 : ef1 alloc01 := by
  intro i j
  left
  intro henv
  simp only [envy, value_alloc01] at henv
  exact absurd henv (by decide)

theorem ef1_alloc10 : ef1 alloc10 := by
  intro i j
  left
  intro henv
  simp only [envy, value_alloc10] at henv
  exact absurd henv (by decide)

theorem not_ef1_alloc00 : ¬ ef1 alloc00 := by
  intro h
  have h10 := h 1 0
  rcases h10 with hnoenv | ⟨g, hg, hle⟩
  · have hlt : value alloc00 1 < value alloc00 0 := by decide
    exact hnoenv hlt
  · rw [value_alloc00_zero, value_alloc00_one] at hle
    exact absurd hle (by decide)

theorem not_ef1_alloc11 : ¬ ef1 alloc11 := by
  intro h
  have h01 := h 0 1
  rcases h01 with hnoenv | ⟨g, hg, hle⟩
  · have hlt : value alloc11 0 < value alloc11 1 := by decide
    exact hnoenv hlt
  · rw [value_alloc11_one, value_alloc11_zero] at hle
    exact absurd hle (by decide)

theorem isEF1_alloc00 : isEF1 alloc00 = false := by decide
theorem isEF1_alloc01 : isEF1 alloc01 = true := by decide
theorem isEF1_alloc10 : isEF1 alloc10 = true := by decide
theorem isEF1_alloc11 : isEF1 alloc11 = false := by decide

def allAllocs22 : List (Alloc 2 2) := [alloc00, alloc01, alloc10, alloc11]

theorem exactly_two_ef1_bool : (allAllocs22.filter isEF1).length = 2 := by decide

theorem alloc_cases22 (a : Alloc 2 2) :
    a = alloc00 ∨ a = alloc01 ∨ a = alloc10 ∨ a = alloc11 := by
  rcases fin2_val_cases (a 0) with h0 | h0 <;>
  rcases fin2_val_cases (a 1) with h1 | h1
  · left; funext g; rcases fin2_val_cases g with rfl | rfl <;> simp [alloc00, h0, h1]
  · right; left; funext g; rcases fin2_val_cases g with rfl | rfl <;> simp [alloc01, h0, h1]
  · right; right; left; funext g; rcases fin2_val_cases g with rfl | rfl <;> simp [alloc10, h0, h1]
  · right; right; right; funext g; rcases fin2_val_cases g with rfl | rfl <;> simp [alloc11, h0, h1]

theorem ef1_classification (a : Alloc 2 2) (h : ef1 a) :
    a = alloc01 ∨ a = alloc10 := by
  rcases alloc_cases22 a with h00 | h01 | h10 | h11
  · rw [h00] at h; exact (not_ef1_alloc00 h).elim
  · exact Or.inl h01
  · exact Or.inr h10
  · rw [h11] at h; exact (not_ef1_alloc11 h).elim

theorem ef1_iff_bool (a : Alloc 2 2) : ef1 a ↔ isEF1 a = true := by
  constructor
  · intro h
    rcases ef1_classification a h with rfl | rfl
    · exact isEF1_alloc01
    · exact isEF1_alloc10
  · intro h
    rcases alloc_cases22 a with h00 | h01 | h10 | h11
    · rw [h00] at h; exact absurd h (by decide)
    · rw [h01]; exact ef1_alloc01
    · rw [h10]; exact ef1_alloc10
    · rw [h11] at h; exact absurd h (by decide)

theorem no_adj_ef1 (a b : Alloc 2 2) (ha : ef1 a) (hb : ef1 b) : ¬ Adj a b := by
  rcases ef1_classification a ha with rfl | rfl <;>
  rcases ef1_classification b hb with rfl | rfl <;>
  decide

inductive ReachN (a : Alloc 2 2) : Nat → Alloc 2 2 → Prop
  | zero : ReachN a 0 a
  | succ {k : Nat} {b c : Alloc 2 2} : ReachN a k b → ef1 c → Adj b c → ReachN a (k + 1) c

theorem reachN_eq {a : Alloc 2 2} (ha : ef1 a) :
    ∀ k b, ReachN a k b → b = a := by
  intro k
  induction k with
  | zero =>
      intro b h
      cases h
      rfl
  | succ k ih =>
      intro b h
      cases h with
      | succ hrec hc hadj =>
          have heq : _ = a := ih _ hrec
          rw [heq] at hadj
          exact (no_adj_ef1 a _ ha hc hadj).elim

theorem alloc01_ne_alloc10 : alloc01 ≠ alloc10 := by
  intro h
  have h0 := congrArg (fun f : Alloc 2 2 => f 0) h
  exact (by decide : alloc01 0 ≠ alloc10 0) h0

theorem no_path_between_diagonals :
    ¬ (∃ k, ReachN alloc01 k alloc10) := by
  rintro ⟨k, hk⟩
  have heq : alloc10 = alloc01 := reachN_eq ef1_alloc01 k alloc10 hk
  exact alloc01_ne_alloc10 heq.symm

def EF1Connected : Prop :=
  ∀ a b : Alloc 2 2, ef1 a → ef1 b → ∃ k, ReachN a k b

theorem not_ef1_connected : ¬ EF1Connected := by
  intro h
  rcases h alloc01 alloc10 ef1_alloc01 ef1_alloc10 with ⟨k, hk⟩
  exact no_path_between_diagonals ⟨k, hk⟩

end Scratch2

#print axioms Scratch2.ef1_classification
#print axioms Scratch2.not_ef1_connected
#print axioms Scratch2.no_path_between_diagonals
#print axioms Scratch2.exactly_two_ef1_bool
#print axioms Scratch2.alloc_cases22
