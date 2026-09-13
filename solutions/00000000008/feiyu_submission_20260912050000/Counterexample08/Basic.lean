import Mathlib

/-!
# A local-obstruction counterexample to conjecture 00000000008

Conjecture 00000000008 asserts that for a square-free integer-coefficient
quadratic `f` there is a constant `c_f > 0` giving the prime-value count the
lower bound `c_f · x / log x`. As stated it omits the condition that no prime
divides every value of `f`, and it is false.

Take `f n = n² + n + 2`. Its values are the values of the integer quadratic
`X² + X + 2`, which is irreducible over `ℚ` — hence square-free — and has
discriminant `1 - 8 = -7 ≠ 0`, so it has no repeated root. But `n(n+1)` is
always even, so `f n` is always even, and `f n ≥ 4` for `n ≥ 1`. The only
prime value is `f 0 = 2`.

Everything the conjecture requires of `f` is established here *about `f`*: the
link to the polynomial is `F_eval`, and squarefreeness is Mathlib's
`Squarefree`, not a side computation on literals.
-/

namespace Counterexample08

open Polynomial Filter

/-- The counterexample: `f n = n² + n + 2`. -/
def f (n : ℕ) : ℕ := n * n + n + 2

/-! ## `f` satisfies the hypotheses of the conjecture -/

/-- The quadratic whose values `f` computes. It is taken over `ℚ` so that
`Squarefree` carries its usual meaning of having no repeated root; its
coefficients are the integers `1, 1, 2`. -/
noncomputable def F : ℚ[X] := X ^ 2 + X + 2

theorem F_natDegree : F.natDegree = 2 := by
  unfold F; compute_degree!

theorem F_coeff_two : F.coeff 2 = 1 := by simp [F, coeff_X]

theorem F_coeff_one : F.coeff 1 = 1 := by simp [F, coeff_X]

theorem F_coeff_zero : F.coeff 0 = 2 := by simp [F, coeff_X]

/-- The discriminant `b² - 4ac` of the coefficients of `F` is `-7`, in
particular nonzero, so `F` has no repeated root. -/
theorem F_discriminant :
    F.coeff 1 ^ 2 - 4 * F.coeff 2 * F.coeff 0 = -7 := by
  rw [F_coeff_zero, F_coeff_one, F_coeff_two]; norm_num

/-- `f` is the value function of `F`. This is what ties the polynomial facts
below to the counting statement above. -/
theorem F_eval (n : ℕ) : F.eval (n : ℚ) = (f n : ℚ) := by
  simp only [F, eval_add, eval_pow, eval_X, eval_ofNat, f]
  push_cast
  ring

theorem F_no_root (x : ℚ) : ¬ F.IsRoot x := by
  simp only [IsRoot, F, eval_add, eval_pow, eval_X, eval_ofNat]
  nlinarith [sq_nonneg (2 * x + 1)]

theorem F_irreducible : Irreducible F := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [F_natDegree]
  · exact F_no_root

/-- `F` is square-free, as the conjecture requires. -/
theorem F_squarefree : Squarefree F := F_irreducible.squarefree

/-! ## Yet `f` has only one prime value -/

/-- Every value of `f` is even: `f n = n(n+1) + 2`. -/
theorem f_even (n : ℕ) : 2 ∣ f n := by
  have hrw : f n = n * (n + 1) + 2 := by unfold f; ring
  rw [hrw]
  obtain ⟨k, hk⟩ := Nat.even_mul_succ_self n
  omega

theorem f_ge_four {n : ℕ} (hn : 1 ≤ n) : 4 ≤ f n := by
  unfold f
  have : n ≤ n * n := Nat.le_mul_of_pos_left n (by omega)
  omega

/-- For positive `n` the value is even and larger than `2`, hence composite. -/
theorem f_not_prime {n : ℕ} (hn : 1 ≤ n) : ¬ Nat.Prime (f n) := by
  intro hp
  have h4 := f_ge_four hn
  rcases (hp.eq_one_or_self_of_dvd 2 (f_even n)) with h | h <;> omega

/-- The prime values of `f` are exactly the one at `n = 0`, namely `f 0 = 2`. -/
theorem f_prime_iff (n : ℕ) : Nat.Prime (f n) ↔ n = 0 := by
  constructor
  · intro hp
    by_contra hn
    exact f_not_prime (by omega) hp
  · rintro rfl
    simpa [f] using Nat.prime_two

/-- The prime-value count of `f` on `{0, 1, …, x}`. -/
def primeValueCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun n => Nat.Prime (f n))).card

theorem filter_eq_zero (x : ℕ) :
    (Finset.range (x + 1)).filter (fun n => Nat.Prime (f n)) = {0} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hp⟩
    exact (f_prime_iff n).mp hp
  · rintro rfl
    exact ⟨by omega, (f_prime_iff 0).mpr rfl⟩

/-- The count is `1` for every cutoff: it does not grow at all. -/
theorem primeValueCount_eq_one (x : ℕ) : primeValueCount x = 1 := by
  unfold primeValueCount
  rw [filter_eq_zero]
  simp

/-! ## The conjectured lower bound fails -/

/-- The conclusion of conjecture 00000000008 for this `f`, in the
division-free form `c · x ≤ (count) · log x`, which for `x ≥ 2` is equivalent
to `count ≥ c · x / log x`. -/
def LowerBoundHolds : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
    c * x ≤ (primeValueCount x : ℝ) * Real.log x

/-- Conjecture 00000000008 is false: `f` is a square-free integer quadratic
whose prime-value count admits no such lower bound, because the count is
bounded while `log` is `o(x)`. -/
theorem conjecture_00000000008_false : ¬ LowerBoundHolds := by
  rintro ⟨c, hc, N, hN⟩
  have hlo : ∀ᶠ y : ℝ in atTop, ‖Real.log y‖ ≤ (c / 2) * ‖id y‖ :=
    Real.isLittleO_log_id_atTop.def (by positivity)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hlo
  obtain ⟨m, hm⟩ := exists_nat_ge (max M 1)
  set x := max N (max m 1) with hxdef
  have hxN : N ≤ x := le_max_left _ _
  have hxm : m ≤ x := le_trans (le_max_left _ _) (le_max_right _ _)
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) (le_max_right _ _)
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hxRM : M ≤ (x : ℝ) := by
    have hmx : (m : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxm
    calc M ≤ max M 1 := le_max_left _ _
      _ ≤ (m : ℝ) := hm
      _ ≤ (x : ℝ) := hmx
  have h2 := hM (x : ℝ) hxRM
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id] at h2
  rw [abs_of_nonneg (Real.log_nonneg hxR1),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (x : ℝ))] at h2
  have h1 := hN x hxN
  rw [primeValueCount_eq_one] at h1
  simp only [Nat.cast_one, one_mul] at h1
  nlinarith

end Counterexample08
