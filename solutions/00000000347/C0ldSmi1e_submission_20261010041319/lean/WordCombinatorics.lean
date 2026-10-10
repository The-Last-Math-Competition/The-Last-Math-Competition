import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace SturmianCF

variable {A : Type*} [Fintype A]

def block (w : ℕ → A) (n j : ℕ) : Fin n → A := fun i => w (j + i)

def Factor (w : ℕ → A) (n : ℕ) := Set.range (block w n)

noncomputable instance factorFintype (w : ℕ → A) (n : ℕ) : Fintype (Factor w n) :=
  Fintype.ofFinite _

noncomputable def complexity (w : ℕ → A) (n : ℕ) : ℕ := Fintype.card (Factor w n)

/-- No two distinct suffixes of the word are equal. -/
def Aperiodic (w : ℕ → A) : Prop := ∀ i j : ℕ, i < j → ∃ k : ℕ, w (i+k) ≠ w (j+k)

def factorPrefix (w : ℕ → A) (n : ℕ) : Factor w (n+1) → Factor w n := fun u =>
  ⟨fun i => u.1 i.castSucc, by
    obtain ⟨j, hj⟩ := u.2
    exact ⟨j, by ext i; exact congrFun hj i.castSucc⟩⟩

omit [Fintype A] in
theorem factorPrefix_surjective (w : ℕ → A) (n : ℕ) : Function.Surjective (factorPrefix w n) := by
  rintro ⟨u,j,rfl⟩
  exact ⟨⟨block w (n+1) j, j, rfl⟩, rfl⟩

theorem complexity_mono_step (w : ℕ → A) (n : ℕ) :
    complexity w n ≤ complexity w (n+1) :=
  Fintype.card_le_of_surjective _ (factorPrefix_surjective w n)

theorem eq_tails_of_complexity_eq (w : ℕ → A) (n : ℕ)
    (hc : complexity w (n+1) = complexity w n)
    {j l : ℕ} (hjl : block w n j = block w n l) :
    ∀ k, w (j+k) = w (l+k) := by
  have hinj : Function.Injective (factorPrefix w n) :=
    ((Fintype.bijective_iff_surjective_and_card _).2 ⟨factorPrefix_surjective w n, hc⟩).1
  have extend : ∀ a b, block w n a = block w n b →
      block w (n+1) a = block w (n+1) b := by
    intro a b hab
    have hp : factorPrefix w n ⟨block w (n+1) a, a, rfl⟩ =
        factorPrefix w n ⟨block w (n+1) b, b, rfl⟩ := Subtype.ext hab
    exact congrArg Subtype.val (hinj hp)
  have hall : ∀ k, block w n (j+k) = block w n (l+k) := by
    intro k
    induction k with
    | zero => simpa using hjl
    | succ k ih =>
      have h := extend _ _ ih
      funext i
      have hi := congrFun h i.succ
      simpa [block, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
  intro k
  have h := congrFun (extend _ _ (hall k)) (0 : Fin (n+1))
  simpa [block] using h

theorem complexity_strict_step (w : ℕ → A) (ha : Aperiodic w) (n : ℕ) :
    complexity w n < complexity w (n+1) := by
  by_contra hn
  have hc : complexity w (n+1) = complexity w n :=
    le_antisymm (Nat.le_of_not_gt hn) (complexity_mono_step w n)
  obtain ⟨j,l,hne,heq⟩ := Finite.exists_ne_map_eq_of_infinite (block w n)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨k,hk⟩ := ha j l hlt
    exact hk (eq_tails_of_complexity_eq w n hc heq k)
  · obtain ⟨k,hk⟩ := ha l j hgt
    exact hk (eq_tails_of_complexity_eq w n hc heq.symm k)

theorem complexity_zero (w : ℕ → A) : complexity w 0 = 1 := by
  have : Unique (Factor w 0) :=
    { default := ⟨block w 0 0, 0, rfl⟩
      uniq := fun _ => Subtype.ext (Subsingleton.elim _ _) }
  exact Fintype.card_unique

theorem length_add_one_le_complexity (w : ℕ → A) (ha : Aperiodic w) (n : ℕ) :
    n+1 ≤ complexity w n := by
  induction n with
  | zero => simp [complexity_zero]
  | succ n ih => have := complexity_strict_step w ha n; omega

end SturmianCF
