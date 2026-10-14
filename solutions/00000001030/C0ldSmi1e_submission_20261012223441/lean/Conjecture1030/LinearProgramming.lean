import Conjecture1030.Definitions

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Conjecture1030

/-- The scaled degree-five polynomial used in the cardinality argument. -/
def lpValue (t : ℝ) : ℝ := (1 + t) * (5 * t ^ 2 - 1) ^ 2

theorem lpValue_nonneg {t : ℝ} (ht : -1 ≤ t) : 0 ≤ lpValue t := by
  exact mul_nonneg (by linarith) (sq_nonneg _)

@[simp] theorem lpValue_one : lpValue 1 = 32 := by norm_num [lpValue]

theorem sphere_inner_bounds (x y : S2) :
    -1 ≤ ⟪(x : E), (y : E)⟫ ∧ ⟪(x : E), (y : E)⟫ ≤ 1 := by
  have h := abs_real_inner_le_norm (x : E) (y : E)
  simpa only [sphere_norm, one_mul, abs_le] using h

theorem lpValue_inner_nonneg (x y : S2) :
    0 ≤ lpValue ⟪(x : E), (y : E)⟫ :=
  lpValue_nonneg (sphere_inner_bounds x y).1

@[simp] theorem lpValue_inner_self (x : S2) :
    lpValue ⟪(x : E), (x : E)⟫ = 32 := by
  rw [real_inner_self_eq_norm_sq, sphere_norm]
  norm_num [lpValue]

theorem lp_sum_ge_thirty_two (X : Finset S2) (x : S2) (hx : x ∈ X) :
    32 ≤ ∑ y ∈ X, lpValue ⟪(x : E), (y : E)⟫ := by
  simpa only [lpValue_inner_self] using
    (Finset.single_le_sum (fun y (_hy : y ∈ X) => lpValue_inner_nonneg x y) hx)

/-- Internal interface: the integral/design argument must establish the exact sum. -/
theorem card_ge_twelve_of_lp_sum (X : Finset S2) (x : S2) (hx : x ∈ X)
    (hsum : ∑ y ∈ X, lpValue ⟪(x : E), (y : E)⟫ = (8 / 3 : ℝ) * X.card) :
    12 ≤ X.card := by
  have h := lp_sum_ge_thirty_two X x hx
  have hcard : (12 : ℝ) ≤ X.card := by rw [hsum] at h; linarith
  exact_mod_cast hcard

theorem lpValue_inner_eq_zero_of_twelve (X : Finset S2) (x y : S2)
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) (hcard : X.card = 12)
    (hsum : ∑ z ∈ X, lpValue ⟪(x : E), (z : E)⟫ = (8 / 3 : ℝ) * X.card) :
    lpValue ⟪(x : E), (y : E)⟫ = 0 := by
  have hpair := Finset.add_le_sum
    (fun z (_hz : z ∈ X) => lpValue_inner_nonneg x z) hx hy hxy
  rw [lpValue_inner_self, hsum, hcard] at hpair
  have hn := lpValue_inner_nonneg x y
  linarith

theorem lpValue_eq_zero_iff (t : ℝ) :
    lpValue t = 0 ↔ t = -1 ∨ t ^ 2 = 1 / 5 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (by linarith)
    · have hs := sq_eq_zero_iff.mp h
      exact Or.inr (by linarith)
  · rintro (h | h)
    · simp [lpValue, h]
    · simp [lpValue, h]

theorem sphere_inner_roots_of_twelve (X : Finset S2) (x y : S2)
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) (hcard : X.card = 12)
    (hsum : ∑ z ∈ X, lpValue ⟪(x : E), (z : E)⟫ = (8 / 3 : ℝ) * X.card) :
    ⟪(x : E), (y : E)⟫ = -1 ∨ ⟪(x : E), (y : E)⟫ ^ 2 = 1 / 5 :=
  (lpValue_eq_zero_iff _).mp
    (lpValue_inner_eq_zero_of_twelve X x y hx hy hxy hcard hsum)

theorem sphere_eq_neg_of_inner_neg_one (x y : S2)
    (h : ⟪(x : E), (y : E)⟫ = -1) : (y : E) = -(x : E) := by
  have hs := norm_add_sq_real (x : E) (y : E)
  rw [sphere_norm, sphere_norm, h] at hs
  have hz : ‖(x : E) + (y : E)‖ = 0 := by nlinarith [norm_nonneg ((x : E) + (y : E))]
  have hv : (x : E) + (y : E) = 0 := norm_eq_zero.mp hz
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hv)

/-- The exact second moment forces the antipode in every twelve-point equality case. -/
theorem exists_antipode_of_squared_sum (X : Finset S2) (x : S2) (hx : x ∈ X)
    (hcard : X.card = 12)
    (hroots : ∀ y ∈ X, x ≠ y →
      ⟪(x : E), (y : E)⟫ = -1 ∨ ⟪(x : E), (y : E)⟫ ^ 2 = 1 / 5)
    (hsum : ∑ y ∈ X, ⟪(x : E), (y : E)⟫ ^ 2 = 4) :
    ∃ y ∈ X, (y : E) = -(x : E) := by
  classical
  by_contra hn
  push_neg at hn
  have hother (y : S2) (hy : y ∈ X.erase x) :
      ⟪(x : E), (y : E)⟫ ^ 2 = 1 / 5 := by
    obtain ⟨hne, hyX⟩ := Finset.mem_erase.mp hy
    rcases hroots y hyX (Ne.symm hne) with hneg | hsq
    · exact False.elim (hn y hyX (sphere_eq_neg_of_inner_neg_one x y hneg))
    · exact hsq
  have hcount : (X.erase x).card = 11 := by
    rw [Finset.card_erase_of_mem hx, hcard]
  have herase : ∑ y ∈ X.erase x, ⟪(x : E), (y : E)⟫ ^ 2 = (11 : ℝ) * (1 / 5) := by
    calc
      _ = ∑ _y ∈ X.erase x, (1 / 5 : ℝ) := Finset.sum_congr rfl hother
      _ = _ := by simp [hcount]
  have hall := Finset.sum_erase_add X (fun y : S2 => ⟪(x : E), (y : E)⟫ ^ 2) hx
  dsimp only at hall
  rw [herase, hsum, real_inner_self_eq_norm_sq, sphere_norm] at hall
  norm_num at hall

end Conjecture1030
