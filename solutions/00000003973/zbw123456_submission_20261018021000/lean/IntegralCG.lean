import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Set
namespace IntegralCG
noncomputable section
variable {n : ℕ}
abbrev Space (n : ℕ) := Fin n → ℝ
def integral : Set (Space n) := {x | ∃ z : Fin n → ℤ, x = fun i => (z i : ℝ)}
def integerHull (P : Set (Space n)) := convexHull ℝ (P ∩ integral)
def IsZeroOnePolytope (P : Set (Space n)) : Prop :=
  ∃ V : Set (Space n), (∀ x ∈ V, ∀ i, x i = 0 ∨ x i = 1) ∧ P = convexHull ℝ V
def CG (P : Set (Space n)) : Set (Space n) :=
  {x ∈ P | ∀ (a : Space n →ₗ[ℝ] ℝ) (b : ℝ),
    (∀ z : Fin n → ℤ, ∃ k : ℤ, a (fun i => (z i : ℝ)) = k) →
    (∀ y ∈ P, a y ≤ b) → a x ≤ (⌊b⌋ : ℤ)}

theorem integerHull_eq {P : Set (Space n)} (hP : IsZeroOnePolytope P) :
    integerHull P = P := by
  obtain ⟨V,hV,rfl⟩ := hP
  apply le_antisymm
  · exact convexHull_min Set.inter_subset_left (convex_convexHull ℝ V)
  · apply convexHull_mono
    intro x hx
    refine ⟨subset_convexHull ℝ V hx, ?_⟩
    refine ⟨fun i => if x i = 0 then 0 else 1, ?_⟩
    funext i
    rcases hV x hx i with h|h <;> simp [h]

def HasRank (P : Set (Space n)) (r : ℕ) : Prop :=
  IsLeast {k | (CG^[k]) P = integerHull P} r

theorem rank_zero {P : Set (Space n)} (hP : IsZeroOnePolytope P) : HasRank P 0 := by
  refine ⟨?_, fun k _ => Nat.zero_le k⟩
  simpa only [Set.mem_setOf_eq, Function.iterate_zero_apply] using (integerHull_eq hP).symm

theorem no_positive_rank {P : Set (Space n)} (hP : IsZeroOnePolytope P)
    {r : ℕ} (hr : HasRank P r) : r = 0 :=
  le_antisymm (hr.2 (rank_zero hP).1) (Nat.zero_le r)

theorem no_quadratic_family : ¬ ∃ (P : (n : ℕ) → Set (Space n))
    (r : ℕ → ℕ) (c : ℝ), 0 < c ∧
    (∀ n, IsZeroOnePolytope (P n) ∧ HasRank (P n) (r n)) ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n:ℝ)^2 ≤ r n := by
  rintro ⟨P,r,c,hc,hP,N,hl⟩
  have hz := no_positive_rank (hP (N+1)).1 (hP (N+1)).2
  have hb := hl (N+1) (by omega)
  rw [hz] at hb
  have hn : (0:ℝ) < N+1 := by positivity
  have hp := mul_pos hc (sq_pos_of_pos hn)
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hb
  linarith

#print axioms rank_zero
#print axioms no_quadratic_family
end
end IntegralCG
