import Classes
import Mathlib.Algebra.FreeMonoid.Basic

namespace FixedAlphabetA1

/-- Mathlib's actual free monoid, with one fixed Bool alphabet and concatenation multiplication. -/
def fixedMonoidCrystal : A1Crystal (FreeMonoid Bool) := monoidCrystal

theorem fixed_monoid_multiply (u v : FreeMonoid Bool) :
    (u*v : FreeMonoid Bool) = List.append (α:=Bool) u v := rfl

theorem all_k_in_one_free_monoid (k : ℕ) (i : Fin (k+1)) :
    fixedMonoidCrystal.e (embedding k i)=((family k).e i).map (embedding k) ∧
    fixedMonoidCrystal.f (embedding k i)=((family k).f i).map (embedding k) :=
  ⟨embedding_e k i,embedding_f k i⟩

def ClosedSubset {V : Type} (A : A1Crystal V) (s : Set V) : Prop :=
  ∀ x ∈ s, ∀ y, A.f x = some y ∨ A.e x = some y → y ∈ s

theorem Walk.closed_mem {V : Type} {A : A1Crystal V} {s : Set V}
    (hs : ClosedSubset A s) {x y : V} (h : Walk A x y) (hx : x∈s) : y∈s := by
  induction h with
  | refl => exact hx
  | @snoc u v h edge ih =>
    rcases edge with hf | hf
    · exact hs u ih v (.inl hf)
    · exact hs u ih v (.inr ((A.inverse v u).mp hf))

theorem connected_irreducible {V : Type} (A : A1Crystal V) (hc : Connected A)
    (s : Set V) (hn : s.Nonempty) (hs : ClosedSubset A s) : s=Set.univ := by
  rcases hn with ⟨x,hx⟩
  apply Set.eq_univ_of_forall
  intro y
  exact (hc x y).closed_mem hs hx

theorem family_irreducible (k : ℕ) (s : Set (Fin (k+1)))
    (hn : s.Nonempty) (hs : ClosedSubset (family k) s) : s=Set.univ :=
  connected_irreducible (family k) (family_connected k) s hn hs

theorem iterate_succ_right {V : Type} (op : V → Option V) (n : ℕ) (x : V) :
    iterate op (n+1) x = (iterate op n x).bind op := by
  induction n generalizing x with
  | zero => simp [iterate]
  | succ n ih =>
    cases h : op x with
    | none => simp [iterate,h]
    | some y =>
      simp only [iterate,h,Option.bind_some]
      exact ih y

theorem highest_iterate (k i : ℕ) (hi : i<k+1) :
    iterate (family k).f i 0 = some ⟨i,hi⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi' : i<k+1 := by omega
    rw [iterate_succ_right,ih hi']
    change (family k).f ⟨i,hi'⟩ = some ⟨i+1,hi⟩
    exact (SupplementScout.lower_eq_some_iff k ⟨i,hi'⟩ ⟨i+1,hi⟩).mpr rfl

/-- Explicit nonempty source-admissible witnesses for every k over the same alphabet. -/
theorem all_k_admissible (k : ℕ) :
    Nonempty (Fin (k+1)) ∧ Connected (family k) ∧
    (∀ i, monoidCrystal.e (embedding k i)=((family k).e i).map (embedding k)) ∧
    (∀ i, monoidCrystal.f (embedding k i)=((family k).f i).map (embedding k)) :=
  ⟨⟨0⟩,family_connected k,embedding_e k,embedding_f k⟩

#check monoidCrystal
#check fixedMonoidCrystal
#check all_k_in_one_free_monoid
#check A1Crystal.tensor
#check monoid_cons_e
#check monoid_cons_f
#check embedding_e
#check embedding_f
#check family_irreducible
#check family_full_strings
#check highest_iterate
#check familyClass_injective
#check fixed_alphabet_finiteness_false
#print axioms all_k_admissible
#print axioms all_k_in_one_free_monoid
#print axioms family_irreducible
#print axioms family_full_strings
#print axioms highest_iterate
#print axioms familyClass_injective
#print axioms fixed_alphabet_finiteness_false

end FixedAlphabetA1
