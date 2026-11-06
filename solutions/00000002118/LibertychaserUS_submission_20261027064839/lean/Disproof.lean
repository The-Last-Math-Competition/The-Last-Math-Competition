import Mathlib

/-!
# Conjecture 00000002118: the third cumulant of Quicksort comparisons

The conjecture asserts that the third cumulant `κ₃(n)` of the Quicksort comparison
count `C_n` has the form `κ₃(n) = 2 n - 6 log n + C` with an explicit constant `C`,
(linear main term with coefficient 2).

We refute the exact form: no constant `C` makes the identity hold for all `n ≥ 2`
(natural logarithm), and no base `b > 0`, `b ≠ 1` works either.

Model (standard): `C_n` is the number of comparisons of Quicksort with a uniformly random
pivot on `n` distinct keys. Its law is determined by `C_0 = C_1 = 0` and, for `n ≥ 2`,
  `C_n = (n - 1) + C_J + C'_{n-1-J}`,
where `J` is uniform on `{0, …, n-1}` and `C`, `C'` are independent copies of the cost.

Representation. The law of `C_n` is the probability mass function `qsPmf n : ℕ → ℚ`,
`qsPmf n v = P(C_n = v)`, defined by the distributional recursion above. In the
convolution the summation ranges are `range (j*j+1)` and `range ((n-1-j)*(n-1-j)+1)`.
These cover the supports, since `C_j ≤ j(j-1)/2 ≤ j*j` almost surely, so no mass is lost.
All values are exact rationals.

`kappa3 n` is the third cumulant of `C_n`, i.e. its third central moment
`E[(C_n - E C_n)^3]`, as a finite sum over `v ≤ n*n`.
-/

namespace TLMC2118

open Finset

/-- `qsPmf n v = P(C_n = v)` for the Quicksort comparison count with uniform pivot.
Base cases `C_0 = C_1 = 0`; for `n ≥ 2` the step is the convolution
`C_n = (n-1) + C_J + C'_{n-1-J}`, `J` uniform on `Fin n`, with independent copies. -/
def qsPmf (n : ℕ) : ℕ → ℚ :=
  if h : n ≤ 1 then fun v => if v = 0 then 1 else 0
  else fun v => (1 / (n : ℚ)) *
    ∑ j : Fin n, ∑ x ∈ range ((j : ℕ) * (j : ℕ) + 1),
      ∑ y ∈ range ((n - 1 - (j : ℕ)) * (n - 1 - (j : ℕ)) + 1),
        (if v = (n - 1) + x + y then qsPmf (j : ℕ) x * qsPmf (n - 1 - (j : ℕ)) y else 0)
termination_by n
decreasing_by
  all_goals simp_wf
  all_goals have := j.isLt
  all_goals omega

/-- Raw moment `E[C_n ^ k]`. -/
def mom (n k : ℕ) : ℚ := ∑ v ∈ range (n * n + 1), (v : ℚ) ^ k * qsPmf n v

/-- Third cumulant of `C_n`: the third central moment `E[(C_n - E C_n)^3]`. -/
def kappa3 (n : ℕ) : ℚ := ∑ v ∈ range (n * n + 1), ((v : ℚ) - mom n 1) ^ 3 * qsPmf n v

lemma qsPmf_base (n : ℕ) (h : n ≤ 1) (v : ℕ) :
    qsPmf n v = if v = 0 then 1 else 0 := by
  rw [qsPmf, dif_pos h]

lemma qsPmf_step (n : ℕ) (h : 2 ≤ n) (v : ℕ) :
    qsPmf n v = (1 / (n : ℚ)) *
      ∑ j : Fin n, ∑ x ∈ range ((j : ℕ) * (j : ℕ) + 1),
        ∑ y ∈ range ((n - 1 - (j : ℕ)) * (n - 1 - (j : ℕ)) + 1),
          (if v = (n - 1) + x + y then qsPmf (j : ℕ) x * qsPmf (n - 1 - (j : ℕ)) y else 0) := by
  rw [qsPmf, dif_neg (show ¬ n ≤ 1 by omega)]

lemma qsPmf_zero : qsPmf 0 = fun v => if v = 0 then 1 else 0 := by
  funext v
  exact qsPmf_base 0 (by norm_num) v

lemma qsPmf_one : qsPmf 1 = fun v => if v = 0 then 1 else 0 := by
  funext v
  exact qsPmf_base 1 (by norm_num) v

lemma qsPmf_two : qsPmf 2 = fun v => if v = 1 then 1 else 0 := by
  funext v
  rw [qsPmf_step 2 le_rfl v]
  simp [Fin.sum_univ_two, Finset.sum_range_succ, qsPmf_zero, qsPmf_one]
  split_ifs <;> norm_num

lemma qsPmf_three : qsPmf 3 = fun v => if v = 2 then 1 / 3 else if v = 3 then 2 / 3 else 0 := by
  funext v
  rw [qsPmf_step 3 (by norm_num) v]
  simp [Fin.sum_univ_three, Finset.sum_range_succ, qsPmf_zero, qsPmf_one, qsPmf_two]
  split_ifs <;> norm_num <;> omega

lemma qsPmf_four : qsPmf 4 = fun v =>
    if v = 4 then 1 / 2 else if v = 5 then 1 / 6 else if v = 6 then 1 / 3 else 0 := by
  funext v
  rw [qsPmf_step 4 (by norm_num) v]
  simp [Fin.sum_univ_four, Finset.sum_range_succ, qsPmf_zero, qsPmf_one, qsPmf_two, qsPmf_three]
  split_ifs <;> norm_num <;> omega

/-- kappa_3(2) = 0. -/
lemma kappa3_two : kappa3 2 = 0 := by
  norm_num [kappa3, mom, qsPmf_two, Finset.sum_range_succ]

/-- kappa_3(3) = -2/27. -/
lemma kappa3_three : kappa3 3 = -2 / 27 := by
  norm_num [kappa3, mom, qsPmf_three, Finset.sum_range_succ]

/-- kappa_3(4) = 13/54. -/
lemma kappa3_four : kappa3 4 = 13 / 54 := by
  norm_num [kappa3, mom, qsPmf_four, Finset.sum_range_succ]

/-- `log 3 - log 2 = log (3/2) > 0.39`, from the alternating series bound for `log (1 - x)`. -/
lemma log_three_sub_log_two_gt : (0.39 : ℝ) < Real.log 3 - Real.log 2 := by
  have key := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 3)
    (by norm_num [abs_of_pos]) 4
  have hl : Real.log (1 - (1 : ℝ) / 3) = Real.log 2 - Real.log 3 := by
    rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  rw [hl] at key
  norm_num [Finset.sum_range_succ, abs_le] at key
  obtain ⟨k1, k2⟩ := key
  linarith

/-- No constant `C` with `κ₃(n) = 2n - 6 log n + C` for all `n ≥ 2` (natural logarithm). -/
theorem conjecture_00000002118_fails :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      (kappa3 n : ℝ) = 2 * (n : ℝ) - 6 * Real.log (n : ℝ) + C := by
  rintro ⟨C, hC⟩
  have h2 := hC 2 (by norm_num)
  have h3 := hC 3 (by norm_num)
  rw [kappa3_two] at h2
  rw [kappa3_three] at h3
  push_cast at h2 h3
  have hl := log_three_sub_log_two_gt
  linarith

/-- No base `b > 0`, `b ≠ 1`, and constant `C` with
`κ₃(n) = 2n - 6 log_b n + C` for all `n ≥ 2`. -/
theorem conjecture_00000002118_fails_any_base :
    ¬ ∃ b C : ℝ, 0 < b ∧ b ≠ 1 ∧ ∀ n : ℕ, 2 ≤ n →
      (kappa3 n : ℝ) = 2 * (n : ℝ) - 6 * (Real.log (n : ℝ) / Real.log b) + C := by
  rintro ⟨b, C, hb, hb1, hC⟩
  have hlb : Real.log b ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hb hb1
  have h2 := hC 2 (by norm_num)
  have h3 := hC 3 (by norm_num)
  have h4 := hC 4 (by norm_num)
  rw [kappa3_two] at h2
  rw [kappa3_three] at h3
  rw [kappa3_four] at h4
  push_cast at h2 h3 h4
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hl4, show 2 * Real.log 2 / Real.log b = 2 * (Real.log 2 / Real.log b) by ring] at h4
  have ha : Real.log 2 / Real.log b = 203 / 324 := by linarith
  have hb3 : Real.log 3 / Real.log b = 315 / 324 := by linarith
  have e2 : Real.log 2 = 203 / 324 * Real.log b := (div_eq_iff hlb).mp ha
  have e3 : Real.log 3 = 315 / 324 * Real.log b := (div_eq_iff hlb).mp hb3
  have key : 203 * Real.log 3 = 315 * Real.log 2 := by
    rw [e2, e3]
    ring
  have hl := log_three_sub_log_two_gt
  have hL2 := Real.log_two_lt_d9
  linarith

end TLMC2118

#print axioms TLMC2118.conjecture_00000002118_fails
#print axioms TLMC2118.conjecture_00000002118_fails_any_base
