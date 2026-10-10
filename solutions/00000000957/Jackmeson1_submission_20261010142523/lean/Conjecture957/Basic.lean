import Mathlib
import Conjecture957.Statement

/-! # Conjecture 00000000957: frame potential local minima are r-fold repeated orthonormal bases

Refutation by the doubled Mercedes-Benz frame in R^2 (r = 3, d = 2, N = 6). -/

-- (formal statement: see Statement.lean)

namespace C957

/-- Unit vector `(x, y)`. -/
noncomputable def pt (x y : ℝ) : E 2 := !₂[x, y]

lemma inner_pt (a b c d : ℝ) : inner ℝ (pt a b) (pt c d) = a * c + b * d := by
  simp [pt, PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma norm_sq_pt (a b : ℝ) : ‖pt a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  simp [pt, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

lemma coord1 (x : E 2) : x = pt (x 0) (x 1) := by
  ext k; fin_cases k <;> simp [pt]

lemma coord (Φ : Fin N → E 2) (i : Fin N) : Φ i = pt (Φ i 0) (Φ i 1) := by
  ext k; fin_cases k <;> simp [pt]

/-- Key identity: in R^2, `FP = N²/2 + ((∑ a_i)² + (∑ b_i)²)/2` with `a = x²-y²`, `b = 2xy`. -/
lemma fp_eq {N : ℕ} (Φ : UnitTuples 2 N) :
    FP Φ = (N : ℝ) ^ 2 / 2 + ((∑ i, ((Φ.1 i 0) ^ 2 - (Φ.1 i 1) ^ 2)) ^ 2
      + (∑ i, (2 * Φ.1 i 0 * Φ.1 i 1)) ^ 2) / 2 := by
  have hu : ∀ i, (Φ.1 i 0) ^ 2 + (Φ.1 i 1) ^ 2 = 1 := by
    intro i
    have h := norm_sq_pt (Φ.1 i 0) (Φ.1 i 1)
    rw [← coord, Φ.2 i] at h
    linarith
  have key : ∀ i j, (inner ℝ (Φ.1 i) (Φ.1 j)) ^ 2 =
      (1 + ((Φ.1 i 0) ^ 2 - (Φ.1 i 1) ^ 2) * ((Φ.1 j 0) ^ 2 - (Φ.1 j 1) ^ 2)
        + (2 * Φ.1 i 0 * Φ.1 i 1) * (2 * Φ.1 j 0 * Φ.1 j 1)) / 2 := by
    intro i j
    rw [coord (Φ.1) i, coord (Φ.1) j, inner_pt]
    simp only [← coord]
    have hi := hu i
    have hj := hu j
    linear_combination (((Φ.1 j 0) ^ 2 + (Φ.1 j 1) ^ 2) * hi + hj) / 2
  unfold FP
  simp_rw [key, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp only [nsmul_eq_mul, mul_one]
  ring

/-- Doubled Mercedes-Benz frame: unit vectors at angles 0, 60, 120 degrees, each twice. -/
noncomputable def mb : UnitTuples 2 (3 * 2) :=
  ⟨fun k => ![pt 1 0, pt (1 / 2) (Real.sqrt 3 / 2), pt (-1 / 2) (Real.sqrt 3 / 2),
      pt 1 0, pt (1 / 2) (Real.sqrt 3 / 2), pt (-1 / 2) (Real.sqrt 3 / 2)] (Fin.cast (by norm_num) k),
   by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    intro i
    have : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 → ‖pt a b‖ = 1 := by
      intro a b h
      have := norm_sq_pt a b
      nlinarith [norm_nonneg (pt a b)]
    fin_cases i <;> simp <;> apply this <;> nlinarith⟩

lemma mb_isFrame : IsFrame mb := by
  refine ⟨3, by norm_num, fun x => ?_⟩
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨a, b, rfl⟩ : ∃ a b, x = pt a b := ⟨x 0, x 1, coord1 x⟩
  simp [mb, inner_pt, norm_sq_pt, Fin.sum_univ_six]
  nlinarith [h3]

lemma mb_isMin (Ψ : UnitTuples 2 (3 * 2)) : FP mb ≤ FP Ψ := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [fp_eq Ψ, fp_eq mb]
  have ha : ∑ i, ((mb.1 i 0) ^ 2 - (mb.1 i 1) ^ 2) = 0 := by
    simp [mb, pt, Fin.sum_univ_six]; nlinarith [h3]
  have hb : ∑ i, (2 * mb.1 i 0 * mb.1 i 1) = 0 := by
    simp [mb, pt, Fin.sum_univ_six]; ring
  rw [ha, hb]
  nlinarith [sq_nonneg (∑ i, ((Ψ.1 i 0) ^ 2 - (Ψ.1 i 1) ^ 2)), sq_nonneg (∑ i, (2 * Ψ.1 i 0 * Ψ.1 i 1))]

lemma mb_isLocalMin : IsLocalMin FP mb :=
  Filter.Eventually.of_forall mb_isMin

lemma mb_not_repeated : ¬ IsRepeatedONB 3 mb := by
  rintro ⟨e, f, s, he, -, h⟩
  obtain ⟨hs0, h0⟩ := h 0
  obtain ⟨hs1, h1⟩ := h 1
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ip : inner ℝ (mb.1 0) (mb.1 1) = 1 / 2 := by
    simp [mb, inner_pt]
  rw [h0, h1, inner_smul_left, inner_smul_right] at ip
  by_cases hf : f 0 = f 1
  · have h11 : inner ℝ (e (f 1)) (e (f 1)) = 1 := by
      simp [he.1 (f 1)]
    rw [hf, h11] at ip
    rcases hs0 with a | a <;> rcases hs1 with b | b <;> simp [a, b] at ip <;> norm_num at ip
  · rw [he.inner_eq_zero hf] at ip
    simp at ip

theorem main : Claim := by
  intro hC
  exact mb_not_repeated (hC 2 3 (by norm_num) (by norm_num) mb mb_isFrame mb_isLocalMin)

end C957
