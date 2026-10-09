import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Count
import Lean.Elab.Tactic.Omega

namespace SupplementScout

def lower (k : ℕ) (i : Fin (k+1)) : Option (Fin (k+1)) :=
  if h : i.val < k then some ⟨i.val+1, by omega⟩ else none

def upper (k : ℕ) (i : Fin (k+1)) : Option (Fin (k+1)) :=
  if h : 0 < i.val then some ⟨i.val-1, by omega⟩ else none

def word (k : ℕ) (i : Fin (k+1)) : List Bool :=
  List.replicate (k-i.val) false ++ List.replicate i.val true

def wt (k : ℕ) (i : Fin (k+1)) : ℤ := (k : ℤ) - 2 * (i.val : ℤ)
def epsilon {k : ℕ} (i : Fin (k+1)) : ℕ := i.val
def phi (k : ℕ) (i : Fin (k+1)) : ℕ := k-i.val

theorem lower_eq_some_iff (k : ℕ) (i j : Fin (k+1)) :
    lower k i = some j ↔ i.val+1=j.val := by
  unfold lower
  split
  · simp only [Option.some.injEq, Fin.ext_iff]
  · simp only [reduceCtorEq, false_iff]
    omega

theorem upper_eq_some_iff (k : ℕ) (i j : Fin (k+1)) :
    upper k i = some j ↔ j.val+1=i.val := by
  unfold upper
  split
  · simp only [Option.some.injEq, Fin.ext_iff]
    omega
  · simp only [reduceCtorEq, false_iff]
    omega

theorem partial_inverse (k : ℕ) (i j : Fin (k+1)) :
    lower k i = some j ↔ upper k j = some i := by
  rw [lower_eq_some_iff, upper_eq_some_iff]

theorem balance (k : ℕ) (i : Fin (k+1)) :
    (phi k i : ℤ) = (epsilon i : ℤ) + wt k i := by
  unfold phi epsilon wt
  omega

theorem upper_none_iff (k : ℕ) (i : Fin (k+1)) :
    upper k i = none ↔ epsilon i = 0 := by
  unfold upper epsilon
  split <;> simp only [reduceCtorEq, false_iff, true_iff] <;> omega

theorem lower_none_iff (k : ℕ) (i : Fin (k+1)) :
    lower k i = none ↔ phi k i = 0 := by
  unfold lower phi
  split <;> simp only [reduceCtorEq, false_iff, true_iff] <;> omega

theorem lower_epsilon (k : ℕ) (i j : Fin (k+1))
    (h : lower k i = some j) : epsilon j = epsilon i + 1 := by
  exact (lower_eq_some_iff k i j).mp h |>.symm

theorem lower_phi (k : ℕ) (i j : Fin (k+1))
    (h : lower k i = some j) : phi k j + 1 = phi k i := by
  have hj := (lower_eq_some_iff k i j).mp h
  unfold phi
  omega

theorem lower_weight (k : ℕ) (i j : Fin (k+1))
    (h : lower k i = some j) : wt k j = wt k i - 2 := by
  have hj := (lower_eq_some_iff k i j).mp h
  unfold wt
  omega

theorem word_true_count (k : ℕ) (i : Fin (k+1)) :
    (word k i).count true = i.val := by
  simp [word, List.count_replicate]

theorem word_injective (k : ℕ) : Function.Injective (word k) := by
  intro i j h
  apply Fin.ext
  simpa only [word_true_count] using congrArg (List.count true) h

theorem word_length (k : ℕ) (i : Fin (k+1)) : (word k i).length = k := by
  simp only [word, List.length_append, List.length_replicate]
  omega

theorem family_card (k : ℕ) : Fintype.card (Fin (k+1)) = k+1 :=
  Fintype.card_fin _

theorem card_distinguishes (k l : ℕ) (e : Fin (k+1) ≃ Fin (l+1)) : k=l := by
  have h := Fintype.card_congr e
  simpa only [Fintype.card_fin, Nat.add_right_cancel_iff] using h

#check lower_eq_some_iff
#check partial_inverse
#check balance
#check word_injective
#check family_card
#check card_distinguishes
#print axioms card_distinguishes

end SupplementScout
