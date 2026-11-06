import Std.Tactic

/-!
# TLMC 00000004993: incompatible oddness and attained minimum

The proof is universally quantified over the set of attainable numbers. It
requires no postulated geometric example and makes no claim about the true
Betti numbers of Spin(7) manifolds.
-/
namespace TLMC4993

/-- Ordinary oddness of a natural number, by its standard arithmetic form. -/
def IsOdd (n : Nat) : Prop := ∃ k : Nat, n = 2 * k + 1

/-- A minimum is attained and is a lower bound, not merely an infimum. -/
def IsMinimum (attainable : Nat → Prop) (m : Nat) : Prop :=
  attainable m ∧ ∀ n : Nat, attainable n → m ≤ n

/-- The first arithmetic consequence of the printed odd-values clause. -/
def AllAttainableOdd (attainable : Nat → Prop) : Prop :=
  ∀ n : Nat, attainable n → IsOdd n

/-- Only the first two explicit clauses are needed for the contradiction. -/
def PrintedArithmeticClauses (attainable : Nat → Prop) : Prop :=
  AllAttainableOdd attainable ∧ IsMinimum attainable 1186

theorem even_value : 1186 = 2 * 593 := by decide

theorem minimum_is_attained (attainable : Nat → Prop) (m : Nat)
    (h : IsMinimum attainable m) : attainable m := h.1

theorem odd_of_minimum (attainable : Nat → Prop) (m : Nat)
    (hOdd : AllAttainableOdd attainable) (hMin : IsMinimum attainable m) :
    IsOdd m := hOdd m (minimum_is_attained attainable m hMin)

theorem no_even_is_odd (j : Nat) : ¬ IsOdd (2 * j) := by
  intro h
  obtain ⟨k, hk⟩ := h
  omega

theorem not_odd_1186 : ¬ IsOdd 1186 := by
  rw [even_value]
  exact no_even_is_odd 593

theorem no_even_minimum (attainable : Nat → Prop) (j : Nat)
    (hOdd : AllAttainableOdd attainable) : ¬ IsMinimum attainable (2 * j) := by
  intro hMin
  exact no_even_is_odd j (odd_of_minimum attainable (2 * j) hOdd hMin)

theorem disproof (attainable : Nat → Prop) :
    ¬ PrintedArithmeticClauses attainable := by
  intro h
  exact not_odd_1186 (odd_of_minimum attainable 1186 h.1 h.2)

/-- The extra geometric/parity claims cannot repair an inconsistent conjunction. -/
theorem full_conjunction_impossible (attainable : Nat → Prop) (otherClauses : Prop) :
    ¬ (PrintedArithmeticClauses attainable ∧ otherClauses) := by
  intro h
  exact disproof attainable h.1

/-- Any intended class, with any admissibility restriction and Betti-number map. -/
def Attained {M : Type u} (admissible : M → Prop) (b3 : M → Nat) (n : Nat) : Prop :=
  ∃ X : M, admissible X ∧ b3 X = n

/-- Direct specialization to a class of objects with third/fourth invariants. -/
theorem geometric_form_impossible {M : Type u}
    (admissible : M → Prop) (b3 b4 : M → Nat) :
    ¬ ((∀ X : M, admissible X → IsOdd (b3 X)) ∧
       IsMinimum (Attained admissible b3) 1186 ∧
       (∀ X : M, admissible X → IsOdd (b3 X + b4 X))) := by
  intro h
  have ho : AllAttainableOdd (Attained admissible b3) := by
    intro n hn
    obtain ⟨X, hX, heq⟩ := hn
    rw [← heq]
    exact h.1 X hX
  exact disproof (Attained admissible b3) ⟨ho, h.2.1⟩

/-- Even without a leastness proof, the claimed 1186 example contradicts oddness. -/
theorem claimed_example_impossible {M : Type u}
    (admissible : M → Prop) (b3 : M → Nat)
    (hOdd : ∀ X : M, admissible X → IsOdd (b3 X)) :
    ¬ Attained admissible b3 1186 := by
  intro h
  obtain ⟨X, hX, heq⟩ := h
  have ho := hOdd X hX
  rw [heq] at ho
  exact not_odd_1186 ho

end TLMC4993

#print axioms TLMC4993.even_value
#print axioms TLMC4993.minimum_is_attained
#print axioms TLMC4993.odd_of_minimum
#print axioms TLMC4993.no_even_is_odd
#print axioms TLMC4993.not_odd_1186
#print axioms TLMC4993.no_even_minimum
#print axioms TLMC4993.disproof
#print axioms TLMC4993.full_conjunction_impossible
#print axioms TLMC4993.geometric_form_impossible
#print axioms TLMC4993.claimed_example_impossible
