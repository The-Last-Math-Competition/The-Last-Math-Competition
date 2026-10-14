import Conjecture1421.Basic

/-!
The actual transition powers and their total variation distance.

The four coordinate matrices (constant, equal first coordinate, equal second
coordinate, identity) are closed under right multiplication by `transition`.
Their scalar recurrence proves the power formula directly from matrix powers.
For positive times, deviations from stationarity have one sign on each first
coordinate block; summing those absolute values gives the exact TV distance.
-/

noncomputable section
open scoped BigOperators
namespace Conjecture1421

lemma transition_decomp (n : ℕ) (x y : State n) :
    transition n x y =
      (if x = y then s n else 0) +
      (if x.1 = y.1 then 1 / (2 * size n) else 0) +
      (if x.2 = y.2 then 1 / (2 * size n) else 0) := by
  rw [transition_apply]
  have hn := size_ne_zero n
  by_cases ha : x.1 = y.1 <;> by_cases hb : x.2 = y.2
  · have hxy : x = y := Prod.ext ha hb
    simp [ha, hb, hxy, s]
    field_simp
    ring
  · have hxy : x ≠ y := fun h => hb (congrArg Prod.snd h)
    simp [ha, hb, hxy]
  · have hxy : x ≠ y := fun h => ha (congrArg Prod.fst h)
    simp [ha, hb, hxy]
  · have hxy : x ≠ y := fun h => ha (congrArg Prod.fst h)
    simp [ha, hb, hxy]

lemma mul_transition_apply (n : ℕ) (M : Matrix (State n) (State n) ℝ)
    (x y : State n) :
    (M * transition n) x y =
      s n * M x y + (1 / (2 * size n)) * (∑ b : Second n, M x (y.1,b)) +
      (1 / (2 * size n)) * (∑ a : ZMod 2, M x (a,y.2)) := by
  classical
  simp_rw [Matrix.mul_apply, transition_decomp, mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, Fintype.sum_prod_type]
  simp only [Prod.ext_iff, Finset.sum_ite_irrel, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul]
  simp [ite_and, Finset.sum_ite_irrel]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The four-dimensional algebra of matrices determined by coordinate equalities. -/
def coordKernel (n : ℕ) (A B C D : ℝ) : Matrix (State n) (State n) ℝ :=
  fun x y => A + (if x.1 = y.1 then B else 0) +
    (if x.2 = y.2 then C else 0) + (if x = y then D else 0)

lemma coordKernel_sum_second (n : ℕ) (A B C D : ℝ) (x : State n) (a : ZMod 2) :
    (∑ b : Second n, coordKernel n A B C D x (a,b)) =
      size n * A + C + (if x.1 = a then size n * B + D else 0) := by
  classical
  simp only [coordKernel, Finset.sum_add_distrib, Prod.ext_iff]
  by_cases h : x.1 = a <;> simp [h, size]
  all_goals ring

lemma coordKernel_sum_first (n : ℕ) (A B C D : ℝ) (x : State n) (b : Second n) :
    (∑ a : ZMod 2, coordKernel n A B C D x (a,b)) =
      2 * A + B + (if x.2 = b then 2 * C + D else 0) := by
  classical
  simp only [coordKernel, Finset.sum_add_distrib, Prod.ext_iff]
  by_cases h : x.2 = b <;> simp [h]
  all_goals ring

lemma coordKernel_mul_transition (n : ℕ) (A B C D : ℝ) :
    coordKernel n A B C D * transition n =
      coordKernel n (A + (B+C)/(2*size n)) (q n * B + D/(2*size n))
        (r * C + D/(2*size n)) (s n * D) := by
  ext x y
  rw [mul_transition_apply, coordKernel_sum_second, coordKernel_sum_first]
  have hn := size_ne_zero n
  by_cases ha : x.1 = y.1 <;> by_cases hb : x.2 = y.2
  all_goals simp [coordKernel, Prod.ext_iff, ha, hb, q, r, s]
  all_goals field_simp [size_ne_zero n]
  all_goals ring

/-- A closed formula for the actual matrix powers, proved by matrix induction. -/
lemma transition_pow_coord (n t : ℕ) :
    transition n ^ t = coordKernel n
      ((1 - q n ^ t - r ^ t + s n ^ t) / (2 * size n))
      ((q n ^ t - s n ^ t) / size n)
      ((r ^ t - s n ^ t) / 2) (s n ^ t) := by
  induction t with
  | zero =>
      ext x y
      simp [coordKernel, Matrix.one_apply]
  | succ t ih =>
      rw [pow_succ, ih, coordKernel_mul_transition]
      simp only [pow_succ]
      generalize q n ^ t = Q, r ^ t = R, s n ^ t = S
      all_goals unfold q r s
      all_goals field_simp [size_ne_zero n]
      all_goals ring

lemma transition_pow_apply (n t : ℕ) (x y : State n) :
    (transition n ^ t) x y =
      (1 + (if x.1 = y.1 then 1 else -1) * q n ^ t +
        (size n * (if x.2 = y.2 then 1 else 0) - 1) *
          (r ^ t + (if x.1 = y.1 then 1 else -1) * s n ^ t)) / (2 * size n) := by
  rw [transition_pow_coord]
  by_cases ha : x.1 = y.1 <;> by_cases hb : x.2 = y.2
  all_goals simp only [coordKernel, Prod.ext_iff, ha, hb, and_self, if_true, if_false, and_false, false_and]
  all_goals field_simp [size_ne_zero n]
  all_goals ring

lemma transition_pow_sum_second (n t : ℕ) (x : State n) (a : ZMod 2) :
    (∑ b : Second n, (transition n ^ t) x (a,b)) =
      (1 + (if x.1 = a then q n ^ t else -q n ^ t)) / 2 := by
  rw [transition_pow_coord, coordKernel_sum_second]
  have hn := size_ne_zero n
  by_cases ha : x.1 = a <;> simp [ha]
  all_goals field_simp [size_ne_zero n]
  all_goals ring

lemma r_nonneg : 0 ≤ r := by norm_num [r]

lemma s_le_r (n : ℕ) : s n ≤ r := by
  have h : 0 ≤ 1 / size n := le_of_lt (one_div_pos.mpr (size_pos n))
  unfold s r
  linarith

lemma pow_sum_le_q (n t : ℕ) (ht : 1 ≤ t) : r ^ t + s n ^ t ≤ q n ^ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction k with
  | zero => simp [q_eq_r_add_s]
  | succ k ih =>
      have hr := pow_nonneg r_nonneg (1+k)
      have hs := pow_nonneg (s_nonneg n) (1+k)
      have hq := q_eq_r_add_s n
      have hmul := mul_le_mul_of_nonneg_right ih (le_of_lt (q_pos n))
      rw [Nat.add_succ, pow_succ, pow_succ, pow_succ]
      nlinarith [mul_nonneg hr (s_nonneg n), mul_nonneg hs r_nonneg]

/-- The geometric difference bound controlling the opposite first-coordinate block. -/
lemma pow_diff_le_q (n t : ℕ) :
    (size n - 1) * (r ^ t - s n ^ t) ≤ q n ^ t := by
  have hn := size_ne_zero n
  have hbase : (size n - 1) * (r - s n) = q n := by
    unfold r s q
    field_simp
    ring
  have hsq : s n ≤ q n := by rw [q_eq_r_add_s]; linarith [r_nonneg]
  have hmain : ∀ k : ℕ, (size n - 1) * (r ^ (k+1) - s n ^ (k+1)) ≤ q n ^ (k+1) := by
    intro k
    induction k with
    | zero => simpa using le_of_eq hbase
    | succ k ih =>
        have ht : s n ^ (k+1) ≤ s n * q n ^ k := by
          rw [pow_succ]
          nlinarith [mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (s_nonneg n) hsq k) (s_nonneg n)]
        have hmul := mul_le_mul_of_nonneg_right ih r_nonneg
        have hmul2 := mul_le_mul_of_nonneg_left ht (le_of_lt (q_pos n))
        have hbasemul := congrArg (fun z : ℝ => z * s n ^ (k+1)) hbase
        have hq := q_eq_r_add_s n
        simp only [pow_succ] at ih ht hmul hmul2 hbasemul ⊢
        rw [hq] at hmul hmul2 hbasemul ⊢
        nlinarith only [hmul, hmul2, hbasemul]
  cases t with
  | zero => simp
  | succ k => exact hmain k

lemma transition_pow_deviation (n t : ℕ) (x y : State n) :
    (transition n ^ t) x y - 1 / (2 * size n) =
      ((if x.1 = y.1 then 1 else -1) * q n ^ t +
        (size n * (if x.2 = y.2 then 1 else 0) - 1) *
          (r ^ t + (if x.1 = y.1 then 1 else -1) * s n ^ t)) / (2 * size n) := by
  rw [transition_pow_apply]
  ring

lemma deviation_same_nonneg (n t : ℕ) (ht : 1 ≤ t) (x y : State n)
    (ha : x.1 = y.1) : 0 ≤ (transition n ^ t) x y - 1 / (2 * size n) := by
  rw [transition_pow_deviation]
  apply div_nonneg _ (by have := size_pos n; positivity)
  by_cases hb : x.2 = y.2
  · simp only [ha, hb, if_true, mul_one, one_mul]
    have hn : 0 ≤ size n - 1 := by linarith [size_ge_four n]
    exact add_nonneg (pow_nonneg (le_of_lt (q_pos n)) t)
      (mul_nonneg hn (add_nonneg (pow_nonneg r_nonneg t) (pow_nonneg (s_nonneg n) t)))
  · simp only [ha, hb, if_true, if_false, mul_zero, zero_sub, one_mul, neg_mul,
      one_mul]
    linarith [pow_sum_le_q n t ht]

lemma deviation_other_nonpos (n t : ℕ) (x y : State n)
    (ha : x.1 ≠ y.1) : (transition n ^ t) x y - 1 / (2 * size n) ≤ 0 := by
  rw [transition_pow_deviation]
  apply div_nonpos_of_nonpos_of_nonneg _ (by have := size_pos n; positivity)
  by_cases hb : x.2 = y.2
  · simp only [ha, hb, if_false, if_true, mul_one, neg_mul, one_mul]
    linarith [pow_diff_le_q n t]
  · simp only [ha, hb, if_false, mul_zero, zero_sub, neg_mul, one_mul]
    have hsr : s n ^ t ≤ r ^ t := pow_le_pow_left₀ (s_nonneg n) (s_le_r n) t
    have hq := pow_nonneg (le_of_lt (q_pos n)) t
    linarith

lemma deviation_sum_second (n t : ℕ) (x : State n) (a : ZMod 2) :
    (∑ b : Second n, ((transition n ^ t) x (a,b) - 1 / (2 * size n))) =
      (if x.1 = a then q n ^ t else -q n ^ t) / 2 := by
  rw [Finset.sum_sub_distrib, transition_pow_sum_second]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  change (1 + (if x.1 = a then q n ^ t else -q n ^ t)) / 2 -
    size n * (1 / (2 * size n)) = _
  by_cases h : x.1 = a <;> simp only [h, if_true, if_false]
  all_goals field_simp [size_ne_zero n]
  all_goals ring

lemma abs_deviation_sum_second (n t : ℕ) (ht : 1 ≤ t) (x : State n)
    (a : ZMod 2) :
    (∑ b : Second n, |(transition n ^ t) x (a,b) - 1 / (2 * size n)|) = q n ^ t / 2 := by
  by_cases ha : x.1 = a
  · calc
      _ = ∑ b : Second n, ((transition n ^ t) x (a,b) - 1 / (2 * size n)) := by
        apply Finset.sum_congr rfl
        intro b _
        exact abs_of_nonneg (deviation_same_nonneg n t ht x (a,b) ha)
      _ = q n ^ t / 2 := by rw [deviation_sum_second]; simp [ha]
  · calc
      _ = ∑ b : Second n, -((transition n ^ t) x (a,b) - 1 / (2 * size n)) := by
        apply Finset.sum_congr rfl
        intro b _
        exact abs_of_nonpos (deviation_other_nonpos n t x (a,b) ha)
      _ = q n ^ t / 2 := by rw [Finset.sum_neg_distrib, deviation_sum_second]; simp [ha]; ring

lemma tvFrom_pos (n t : ℕ) (ht : 1 ≤ t) (x : State n) : tvFrom n t x = q n ^ t / 2 := by
  unfold tvFrom
  rw [Fintype.sum_prod_type]
  simp_rw [abs_deviation_sum_second n t ht x]
  simp

lemma tvFrom_zero (n : ℕ) (x : State n) : tvFrom n 0 x = 1 - 1 / (2 * size n) := by
  have hc : 0 ≤ 1 / (2 * size n) := by have := size_pos n; positivity
  have hc1 : 1 / (2 * size n) ≤ 1 := by
    apply (div_le_iff₀ (by have := size_pos n; positivity)).2
    linarith [size_ge_four n]
  have hentry (y : State n) : |(transition n ^ 0) x y - 1 / (2 * size n)| =
      (if x = y then 1 - 2 / (2 * size n) else 0) + 1 / (2 * size n) := by
    by_cases h : x = y
    · simp only [pow_zero, Matrix.one_apply, h, if_true]
      rw [abs_of_nonneg (sub_nonneg.mpr hc1)]
      ring
    · simp only [pow_zero, Matrix.one_apply, h, if_false, zero_sub, abs_neg,
        abs_of_nonneg hc, zero_add]
  unfold tvFrom
  simp_rw [hentry]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, state_card, nsmul_eq_mul]
  rw [Nat.cast_mul, Nat.cast_ofNat]
  change (1/2 : ℝ) * (1 - 2/(2*size n) + (2*size n) * (1/(2*size n))) = _
  field_simp [size_ne_zero n]
  ring

/-- The exact TV distance from every starting point, including the initial point mass. -/
lemma tvFrom_eq (n t : ℕ) (x : State n) :
    tvFrom n t x = if t = 0 then 1 - 1 / (2 * size n) else q n ^ t / 2 := by
  by_cases ht : t = 0
  · subst t
    simp only [if_true, tvFrom_zero]
  · simp only [ht, if_false]
    exact tvFrom_pos n t (Nat.one_le_iff_ne_zero.mpr ht) x

lemma worstTV_eq (n t : ℕ) :
    worstTV n t = if t = 0 then 1 - 1 / (2 * size n) else q n ^ t / 2 := by
  unfold worstTV
  simp only [tvFrom_eq]
  exact Finset.sup'_const _ _

end Conjecture1421
