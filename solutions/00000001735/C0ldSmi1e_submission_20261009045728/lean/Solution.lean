import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Conjecture 00000001735: the two asserted properties are incompatible

The solutions are all ordered pairs of integers.  The original statement imposes
neither a primitiveness condition nor a restriction of the right-hand side to
cube-free integers.  `solutionCount` is the cardinality of the full solution set;
using cardinal numbers ensures an infinite set is never silently assigned count 0.
-/

namespace Conjecture1735

/-- All integer solutions, with no coprimality or size restriction. -/
def solutionSet (k : ℤ) : Set (ℤ × ℤ) :=
  {p | p.1 ^ 3 - 2 * p.2 ^ 3 = k}

/-- The full solution count, including infinite cardinalities. -/
def solutionCount (k : ℤ) : Cardinal := Cardinal.mk (solutionSet k)

/-- At right-hand side zero, the sole integer solution is the origin. -/
theorem zero_fiber (x y : ℤ) (h : x ^ 3 - 2 * y ^ 3 = 0) : x = 0 ∧ y = 0 := by
  have hxy : x ^ 3 = 2 * y ^ 3 := by linarith
  have habs : x.natAbs ^ 3 = 2 * y.natAbs ^ 3 := by
    simpa only [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_ofNat] using congrArg Int.natAbs hxy
  have hy : y = 0 := by
    by_contra hy
    have hyabs : y.natAbs ≠ 0 := by simpa using hy
    have hfac := congrArg (fun n : ℕ => n.factorization 2) habs
    dsimp only at hfac
    rw [Nat.factorization_pow, Nat.factorization_mul (by norm_num) (pow_ne_zero _ hyabs),
      Nat.factorization_pow] at hfac
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply,
      Nat.prime_two.factorization_self] at hfac
    omega
  subst y
  simpa using h

theorem solutionSet_zero : solutionSet 0 = {(0, 0)} := by
  ext p
  constructor
  · intro hp
    obtain ⟨hx, hy⟩ := zero_fiber p.1 p.2 hp
    simpa [Set.mem_singleton_iff, Prod.ext_iff] using And.intro hx hy
  · rintro rfl
    norm_num [solutionSet]

theorem solutionCount_zero : solutionCount 0 = 1 := by
  simp [solutionCount, solutionSet_zero]

/-- Multiplying both coordinates multiplies the right-hand side by the cube. -/
def scaleSolution (t k : ℤ) (p : solutionSet k) : solutionSet (t ^ 3 * k) :=
  ⟨(t * p.val.1, t * p.val.2), by
    change (t * p.val.1) ^ 3 - 2 * (t * p.val.2) ^ 3 = t ^ 3 * k
    calc
      _ = t ^ 3 * (p.val.1 ^ 3 - 2 * p.val.2 ^ 3) := by ring
      _ = _ := by rw [p.property]⟩

theorem scaleSolution_injective (t k : ℤ) (ht : t ≠ 0) :
    Function.Injective (scaleSolution t k) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · have hfirst := congrArg (fun s : solutionSet (t ^ 3 * k) => s.val.1) h
    exact mul_left_cancel₀ ht hfirst
  · have hsecond := congrArg (fun s : solutionSet (t ^ 3 * k) => s.val.2) h
    exact mul_left_cancel₀ ht hsecond

theorem solutionCount_le_scaled (t k : ℤ) (ht : t ≠ 0) :
    solutionCount k ≤ solutionCount (t ^ 3 * k) :=
  Cardinal.mk_le_of_injective (scaleSolution_injective t k ht)

/-- Every nonzero positive integer scale preserves a globally maximal count. -/
theorem scaled_is_maximizer {m : Cardinal} (hbound : ∀ k : ℤ, solutionCount k ≤ m)
    {k : ℤ} (hk : solutionCount k = m) (n : ℕ) :
    solutionCount (((n : ℤ) + 1) ^ 3 * k) = m := by
  apply le_antisymm (hbound _)
  rw [← hk]
  exact solutionCount_le_scaled _ _ (by omega)

theorem scaled_rhs_injective {k : ℤ} (hk : k ≠ 0) :
    Function.Injective (fun n : ℕ => ((n : ℤ) + 1) ^ 3 * k) := by
  intro a b hab
  have hcube : ((a : ℤ) + 1) ^ 3 = ((b : ℤ) + 1) ^ 3 :=
    mul_right_cancel₀ hk hab
  have hab' : (a : ℤ) + 1 = (b : ℤ) + 1 :=
    (show Odd (3 : ℕ) by decide).pow_injective hcube
  exact_mod_cast (by omega : (a : ℤ) = b)

/-- If a finite or infinite maximum is attained away from zero, infinitely many
right-hand sides attain it. -/
theorem infinite_maximizers_of_nonzero_maximizer {m : Cardinal}
    (hbound : ∀ k : ℤ, solutionCount k ≤ m)
    {k : ℤ} (hk : solutionCount k = m) (hk0 : k ≠ 0) :
    Set.Infinite {j : ℤ | solutionCount j = m} := by
  have hrange := Set.infinite_range_of_injective (scaled_rhs_injective hk0)
  apply hrange.mono
  rintro j ⟨n, rfl⟩
  exact scaled_is_maximizer hbound hk n

/-- A maximum of 12 means a universal upper bound and actual attainment. -/
def MaximumIsTwelve : Prop :=
  (∀ k : ℤ, solutionCount k ≤ 12) ∧ ∃ k : ℤ, solutionCount k = 12

/-- The two substantive assertions of the original conjecture. -/
def Conjecture : Prop :=
  MaximumIsTwelve ∧ Set.Finite {k : ℤ | solutionCount k = 12}

theorem twelve_solution_rhs_ne_zero {k : ℤ} (hk : solutionCount k = 12) : k ≠ 0 := by
  intro hzero
  subst k
  rw [solutionCount_zero] at hk
  norm_num at hk

/-- The first clause forces the negation of the second clause. -/
theorem maximum_twelve_implies_infinite_maximizers (h : MaximumIsTwelve) :
    Set.Infinite {k : ℤ | solutionCount k = 12} := by
  obtain ⟨k, hk⟩ := h.2
  exact infinite_maximizers_of_nonzero_maximizer h.1 hk (twelve_solution_rhs_ne_zero hk)

/-- Full disproof of the conjunction as written. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  exact maximum_twelve_implies_infinite_maximizers h.1 h.2

/-- The standard convention that a Thue right-hand side is nonzero gives the
same contradiction. -/
def NonzeroConjecture : Prop :=
  (∀ k : ℤ, k ≠ 0 → solutionCount k ≤ 12) ∧
  (∃ k : ℤ, k ≠ 0 ∧ solutionCount k = 12) ∧
  Set.Finite {k : ℤ | k ≠ 0 ∧ solutionCount k = 12}

theorem nonzero_conjecture_false : ¬ NonzeroConjecture := by
  rintro ⟨hbound, ⟨k, _hk0, hk⟩, hfinite⟩
  have hall : ∀ j : ℤ, solutionCount j ≤ 12 := by
    intro j
    by_cases hj : j = 0
    · subst j
      rw [solutionCount_zero]
      norm_num
    · exact hbound j hj
  have hsame : {j : ℤ | j ≠ 0 ∧ solutionCount j = 12} =
      {j : ℤ | solutionCount j = 12} := by
    ext j
    exact ⟨And.right, fun hj => ⟨twelve_solution_rhs_ne_zero hj, hj⟩⟩
  rw [hsame] at hfinite
  exact maximum_twelve_implies_infinite_maximizers ⟨hall, k, hk⟩ hfinite

end Conjecture1735
