import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

namespace IdentityPeriodic
abbrev Plane := Fin 2 → ℝ

def F (x : Plane) : Plane := x
noncomputable def coordinatePolynomial (i : Fin 2) : MvPolynomial (Fin 2) ℝ := MvPolynomial.X i

theorem polynomial_map (x : Plane) (i : Fin 2) :
    (F x) i = MvPolynomial.eval x (coordinatePolynomial i) := by
  simp [F, coordinatePolynomial]

def fixed (n : ℕ) : Set Plane := {x | F^[n] x = x}

theorem iterate_identity (n : ℕ) (x : Plane) : F^[n] x = x := by
  have h : F = (id : Plane → Plane) := rfl
  rw [h, Function.iterate_id]
  rfl

theorem fixed_univ (n : ℕ) : fixed n = Set.univ := by
  ext x
  simp [fixed, iterate_identity]

/-- A concrete injection of the real line into the true fixed-point set. -/
def realEmbedding (r : ℝ) : Plane := fun _ => r

theorem embedding_injective : Function.Injective realEmbedding := by
  intro r s h
  exact congrFun h 0

theorem infinitely_many_fixed (n : ℕ) : (fixed n).Infinite := by
  have hr : (Set.range realEmbedding).Infinite :=
    Set.infinite_range_of_injective embedding_injective
  apply hr.mono
  rintro x ⟨r,rfl⟩
  exact iterate_identity n _

/-- All fixed-point counts required by the classification would have to be finite. -/
theorem no_finite_counting : ¬ (∀ n : ℕ, 0 < n → (fixed n).Finite) := by
  intro h
  exact (infinitely_many_fixed 1) (h 1 (by norm_num))

/-- The least-period convention also leaves infinitely many period-one points. -/
def exactPeriod (n : ℕ) : Set Plane :=
  {x | 0 < n ∧ F^[n] x = x ∧ ∀ k : ℕ, 0 < k → k < n → F^[k] x ≠ x}

theorem exact_period_one : exactPeriod 1 = Set.univ := by
  ext x
  simp only [exactPeriod, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  refine ⟨by norm_num, iterate_identity 1 x, ?_⟩
  intro k hk hlt
  omega

theorem infinitely_many_exact_one : (exactPeriod 1).Infinite := by
  rw [exact_period_one, ← fixed_univ 1]
  exact infinitely_many_fixed 1

/-- The same identity preserves the compact unit square. -/
def square : Set Plane := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

theorem square_invariant {x : Plane} (hx : x ∈ square) : F x ∈ square := hx

theorem infinite_square_fixed (n : ℕ) : (square ∩ fixed n).Infinite := by
  have hi : (Set.Icc (0 : ℝ) 1).Infinite := Set.Icc_infinite (by norm_num)
  have he : (realEmbedding '' Set.Icc (0 : ℝ) 1).Infinite :=
    hi.image embedding_injective.injOn
  apply he.mono
  rintro x ⟨r,hr,rfl⟩
  exact ⟨fun _ => hr, iterate_identity n _⟩

#print axioms polynomial_map
#print axioms iterate_identity
#print axioms infinitely_many_fixed
#print axioms no_finite_counting
#print axioms infinitely_many_exact_one
#print axioms infinite_square_fixed
end IdentityPeriodic
