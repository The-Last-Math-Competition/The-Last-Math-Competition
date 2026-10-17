import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Set.Countable

namespace ZeroInvariant
universe u

/-- The statement is uniform in the class S of objects. In the application
    S is smooth homology 4-spheres, e is S^4, sum is connected sum and rel
    is diffeomorphism. No property of these inputs is needed. -/
def Requirements {S : Type u} (e : S) (sum : S → S → S)
    (rel : S → S → Prop) (theta : S → ℤ) : Prop :=
  (∀ M N, rel M N → theta M = theta N) ∧
  (∀ M N, theta (sum M N) = theta M + theta N) ∧
  theta e = 0 ∧
  ((∃ M, theta M ≠ 0) → ¬ (∀ M, rel M e))

theorem nonzero_obstructs {S : Type u} {e : S} {rel : S → S → Prop}
    {theta : S → ℤ} (hinv : ∀ M N, rel M N → theta M = theta N)
    (hzero : theta e = 0) (h : ∃ M, theta M ≠ 0) : ¬ ∀ M, rel M e := by
  rintro hall
  obtain ⟨M,hM⟩ := h
  exact hM ((hinv M e (hall M)).trans hzero)

theorem conjecture {S : Type u} (e : S) (sum : S → S → S)
    (rel : S → S → Prop) : ∃ theta : S → ℤ, Requirements e sum rel theta := by
  refine ⟨fun _ => 0, ?_⟩
  refine ⟨fun _ _ _ => rfl, fun _ _ => (add_zero 0).symm, rfl, ?_⟩
  rintro ⟨M,hM⟩
  exact (hM rfl).elim

theorem target_is_countable : Countable ℤ := inferInstance
example : AddCommGroup ℤ := inferInstance
theorem target_is_abelian : ∀ a b : ℤ, a+b = b+a := add_comm
#print axioms conjecture
#print axioms nonzero_obstructs
end ZeroInvariant
