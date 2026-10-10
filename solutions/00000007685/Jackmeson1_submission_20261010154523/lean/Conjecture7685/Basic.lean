import Mathlib
import Conjecture7685.Statement

/-! # Conjecture 00000007685: the Jackson integral of the theta quotient theta_3(zq)/theta_3(z)

We show that `J_q = r + 1/r` with `r = theta(q)/theta(1)`, hence `2 ≤ J_q ≤ 4` on `(0,1)`, so the
claimed leading coefficient `Γ(1/4)^2/(2 π^(3/2)) ≈ 1.18` (which is `< 2`) is impossible. -/

-- (formal statement: see Statement.lean)

namespace C7685

open Filter Topology

section theta
variable {q : ℝ}

lemma term_eq (hq : q ≠ 0) (w : ℝ) (hw : w ≠ 0) (k : ℤ) :
    q ^ (k ^ 2) * (q ^ 2 * w) ^ k = q⁻¹ * w⁻¹ * (q ^ ((k + 1) ^ 2) * w ^ (k + 1)) := by
  have e : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
  rw [e, zpow_add₀ hq, zpow_add₀ hq, zpow_add₀ hw, mul_zpow, zpow_mul, zpow_ofNat]
  simp only [zpow_ofNat]
  field_simp

lemma theta_shift (hq : q ≠ 0) (w : ℝ) (hw : w ≠ 0) :
    theta q (q ^ 2 * w) = q⁻¹ * w⁻¹ * theta q w := by
  unfold theta
  simp_rw [term_eq hq w hw]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun k => q ^ (k ^ 2) * w ^ k)

lemma f_le (hq0 : 0 < q) (hq1 : q < 1) (k : ℤ) : q ^ (k ^ 2) ≤ q ^ k.natAbs := by
  have h : (k.natAbs : ℤ) ≤ k ^ 2 := by
    rcases Int.natAbs_eq k with h | h <;> nlinarith [sq_nonneg (k.natAbs : ℤ)]
  calc q ^ (k ^ 2) ≤ q ^ (k.natAbs : ℤ) := zpow_le_zpow_right_of_le_one₀ hq0 hq1.le h
    _ = q ^ k.natAbs := zpow_natCast _ _

lemma summ_f (hq0 : 0 < q) (hq1 : q < 1) : Summable (fun k : ℤ => q ^ (k ^ 2)) := by
  have hg : Summable (fun k : ℤ => q ^ k.natAbs) :=
    (summable_int_iff_summable_nat_and_neg).2
      ⟨by simpa using summable_geometric_of_lt_one hq0.le hq1,
       by simpa using summable_geometric_of_lt_one hq0.le hq1⟩
  exact Summable.of_nonneg_of_le (fun k => by positivity) (f_le hq0 hq1) hg

lemma g_le (hq0 : 0 < q) (hq1 : q < 1) (k : ℤ) :
    q ^ (k ^ 2 + k) ≤ q ^ (k ^ 2) + q ^ ((k + 1) ^ 2) := by
  rcases le_or_gt 0 k with h | h
  · have : q ^ (k ^ 2 + k) ≤ q ^ (k ^ 2) :=
      zpow_le_zpow_right_of_le_one₀ hq0 hq1.le (by omega)
    have : 0 ≤ q ^ ((k + 1) ^ 2) := by positivity
    linarith
  · have : q ^ (k ^ 2 + k) ≤ q ^ ((k + 1) ^ 2) :=
      zpow_le_zpow_right_of_le_one₀ hq0 hq1.le (by nlinarith)
    have : 0 ≤ q ^ (k ^ 2) := by positivity
    linarith

lemma f_le' (hq0 : 0 < q) (hq1 : q < 1) (k : ℤ) :
    q ^ (k ^ 2) ≤ q ^ (k ^ 2 + k) + q ^ ((k - 1) ^ 2 + (k - 1)) := by
  rcases le_or_gt 0 k with h | h
  · have : q ^ (k ^ 2) ≤ q ^ ((k - 1) ^ 2 + (k - 1)) :=
      zpow_le_zpow_right_of_le_one₀ hq0 hq1.le (by nlinarith)
    have : 0 ≤ q ^ (k ^ 2 + k) := by positivity
    linarith
  · have : q ^ (k ^ 2) ≤ q ^ (k ^ 2 + k) :=
      zpow_le_zpow_right_of_le_one₀ hq0 hq1.le (by omega)
    have : 0 ≤ q ^ ((k - 1) ^ 2 + (k - 1)) := by positivity
    linarith

lemma summ_g (hq0 : 0 < q) (hq1 : q < 1) : Summable (fun k : ℤ => q ^ (k ^ 2 + k)) := by
  have h2 : Summable (fun k : ℤ => q ^ ((k + 1) ^ 2)) :=
    (summ_f hq0 hq1).comp_injective (add_left_injective (1 : ℤ))
  exact Summable.of_nonneg_of_le (fun k => by positivity) (g_le hq0 hq1)
    ((summ_f hq0 hq1).add h2)

lemma A_eq : theta q 1 = ∑' k : ℤ, q ^ (k ^ 2) := by simp [theta]
lemma B_eq (hq : q ≠ 0) : theta q q = ∑' k : ℤ, q ^ (k ^ 2 + k) := by
  simp only [theta]; congr 1; ext k; rw [zpow_add₀ hq]

lemma A_le (hq0 : 0 < q) (hq1 : q < 1) :
    theta q 1 ≤ 2 * theta q q := by
  rw [A_eq, B_eq hq0.ne']
  have hs := summ_g hq0 hq1
  have h2 : Summable (fun k : ℤ => q ^ ((k - 1) ^ 2 + (k - 1))) :=
    hs.comp_injective (sub_left_injective (b := (1 : ℤ)))
  calc ∑' k : ℤ, q ^ (k ^ 2) ≤ ∑' k : ℤ, (q ^ (k ^ 2 + k) + q ^ ((k - 1) ^ 2 + (k - 1))) :=
        (summ_f hq0 hq1).tsum_le_tsum (f_le' hq0 hq1) (hs.add h2)
    _ = 2 * ∑' k : ℤ, q ^ (k ^ 2 + k) := by
        rw [(hs.tsum_add h2)]
        have : ∑' k : ℤ, q ^ ((k - 1) ^ 2 + (k - 1)) = ∑' k : ℤ, q ^ (k ^ 2 + k) :=
          (Equiv.subRight (1 : ℤ)).tsum_eq (fun k : ℤ => q ^ (k ^ 2 + k))
        rw [this]; ring

lemma B_le (hq0 : 0 < q) (hq1 : q < 1) :
    theta q q ≤ 2 * theta q 1 := by
  rw [A_eq, B_eq hq0.ne']
  have hs := summ_f hq0 hq1
  have h2 : Summable (fun k : ℤ => q ^ ((k + 1) ^ 2)) := hs.comp_injective (add_left_injective (1 : ℤ))
  calc ∑' k : ℤ, q ^ (k ^ 2 + k) ≤ ∑' k : ℤ, (q ^ (k ^ 2) + q ^ ((k + 1) ^ 2)) :=
        (summ_g hq0 hq1).tsum_le_tsum (g_le hq0 hq1) (hs.add h2)
    _ = 2 * ∑' k : ℤ, q ^ (k ^ 2) := by
        rw [(hs.tsum_add h2)]
        have : ∑' k : ℤ, q ^ ((k + 1) ^ 2) = ∑' k : ℤ, q ^ (k ^ 2) :=
          (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => q ^ (k ^ 2))
        rw [this]; ring

lemma A_pos (hq0 : 0 < q) (hq1 : q < 1) : 0 < theta q 1 := by
  rw [A_eq]
  exact (summ_f hq0 hq1).tsum_pos (fun k => by positivity) 0 (by positivity)

lemma B_pos (hq0 : 0 < q) (hq1 : q < 1) : 0 < theta q q := by
  rw [B_eq hq0.ne']
  exact (summ_g hq0 hq1).tsum_pos (fun k => by positivity) 0 (by positivity)

/-- `a n = theta(q^n)` is positive. -/
lemma a_pos (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    0 < theta q (q ^ n) ∧ 0 < theta q (q ^ (n + 1)) := by
  induction n with
  | zero => simpa using ⟨A_pos hq0 hq1, B_pos hq0 hq1⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h := theta_shift hq0.ne' (q ^ n) (by positivity)
    have e : q ^ 2 * q ^ n = q ^ (n + 1 + 1) := by ring
    rw [e] at h
    rw [h]
    have := ih.1
    positivity

lemma a_rec (hq0 : 0 < q) (n : ℕ) :
    theta q (q ^ (n + 2)) = q⁻¹ * (q ^ n)⁻¹ * theta q (q ^ n) := by
  have h := theta_shift hq0.ne' (q ^ n) (by positivity)
  rwa [show q ^ 2 * q ^ n = q ^ (n + 2) by ring] at h

/-- Jackson summand `b n = q^n T(q^n)`. -/
noncomputable def b (q : ℝ) (n : ℕ) : ℝ := q ^ n * T q (q ^ n)

lemma b_eq (n : ℕ) : b q n = q ^ n * (theta q (q ^ (n + 1)) / theta q (q ^ n)) := by
  simp [b, T, pow_succ]

lemma b_step (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : b q (n + 2) = q * b q n := by
  have h1 := a_rec hq0 (n + 1)
  have h0 := a_rec hq0 n
  have p0 := (a_pos hq0 hq1 n).1
  rw [b_eq, b_eq, h1, h0]
  have : (q ^ (n + 1))⁻¹ = (q ^ n)⁻¹ * q⁻¹ := by rw [pow_succ, mul_inv]
  have hqn : q ^ n ≠ 0 := by positivity
  have hq : q ≠ 0 := hq0.ne'
  rw [this]
  field_simp
  ring

end theta

section J
variable {q : ℝ}

lemma b_even (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) : b q (2 * m) = q ^ m * b q 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [show 2 * (m + 1) = 2 * m + 2 by ring, b_step hq0 hq1, ih]; ring

lemma b_odd (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) : b q (2 * m + 1) = q ^ m * b q 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, b_step hq0 hq1, ih]; ring

/-- The Jackson integral in closed form: `J_q = r + 1/r` with `r = theta(q)/theta(1)`. -/
theorem J_eq (hq0 : 0 < q) (hq1 : q < 1) :
    J q = theta q q / theta q 1 + theta q 1 / theta q q := by
  have A := A_pos hq0 hq1
  have B := B_pos hq0 hq1
  have b0 : b q 0 = theta q q / theta q 1 := by simp [b_eq]
  have b1 : b q 1 = theta q 1 / theta q q := by
    rw [b_eq, show (1 : ℕ) + 1 = 0 + 2 by rfl, a_rec hq0 0]
    simp only [pow_zero, pow_one, inv_one, mul_one]
    field_simp
  have hg : Summable (fun m : ℕ => q ^ m) := summable_geometric_of_lt_one hq0.le hq1
  have he : Summable (fun m : ℕ => b q (2 * m)) := by
    simpa [b_even hq0 hq1] using hg.mul_right (b q 0)
  have ho : Summable (fun m : ℕ => b q (2 * m + 1)) := by
    simpa [b_odd hq0 hq1] using hg.mul_right (b q 1)
  have hs : ∑' n : ℕ, b q n = (1 - q)⁻¹ * (b q 0 + b q 1) := by
    rw [← tsum_even_add_odd he ho]
    simp only [b_even hq0 hq1, b_odd hq0 hq1]
    rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one hq0.le hq1]
    ring
  have h1 : (1 - q) ≠ 0 := by linarith
  have : J q = (1 - q) * ∑' n : ℕ, b q n := rfl
  rw [this, hs, b0, b1]
  field_simp

theorem J_bounds (hq0 : 0 < q) (hq1 : q < 1) : 2 ≤ J q ∧ J q ≤ 4 := by
  have A := A_pos hq0 hq1
  have B := B_pos hq0 hq1
  rw [J_eq hq0 hq1]
  have h1 := A_le hq0 hq1
  have h2 := B_le hq0 hq1
  set a := theta q 1
  set d := theta q q
  constructor
  · rw [div_add_div _ _ A.ne' B.ne', le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (a - d)]
  · have : d / a ≤ 2 := by rw [div_le_iff₀ A]; linarith
    have : a / d ≤ 2 := by rw [div_le_iff₀ B]; linarith
    linarith

end J

lemma c_bounds : 0 < c ∧ c < 2 := by
  have hG : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hP : 0 < Real.pi ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨by unfold c; positivity, ?_⟩
  have h54 : Real.Gamma (5 / 4) ≤ 1 := by
    have := Real.convexOn_Gamma.2 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (0 : ℝ) ≤ 3 / 4 by norm_num)
      (show (0 : ℝ) ≤ 1 / 4 by norm_num) (by norm_num)
    simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at this
    norm_num at this
    linarith
  have h14 : Real.Gamma (1 / 4) ≤ 4 := by
    have := Real.Gamma_add_one (s := 1 / 4) (by norm_num)
    norm_num at this
    linarith
  have hsq : (Real.pi ^ ((3 : ℝ) / 2)) ^ 2 = Real.pi ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    norm_num
  have h4 : 4 < Real.pi ^ ((3 : ℝ) / 2) := by
    by_contra hle
    replace hle := not_lt.mp hle
    have h27 : (3 : ℝ) ^ 3 < Real.pi ^ 3 := pow_lt_pow_left₀ Real.pi_gt_three (by norm_num) (by norm_num)
    have := pow_le_pow_left₀ hP.le hle 2
    nlinarith
  unfold c
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem main : Claim := by
  rintro ⟨-, α, L, hlim, hL⟩
  obtain ⟨cpos, clt⟩ := c_bounds
  have hev : ∀ᶠ q in 𝓝[<] (1 : ℝ), 0 < q ∧ q < 1 :=
    by filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with q hq using hq
  have hg0 : ∀ᶠ q in 𝓝[<] (1 : ℝ), 0 < (1 - q) ^ α :=
    hev.mono fun q hq => Real.rpow_pos_of_pos (by linarith [hq.2]) _
  have h1q : Tendsto (fun q : ℝ => 1 - q) (𝓝[<] 1) (𝓝 0) := by
    have : Tendsto (fun q : ℝ => 1 - q) (𝓝 1) (𝓝 (1 - 1)) :=
      (continuous_const.sub continuous_id).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  rcases lt_trichotomy α 0 with hα | hα | hα
  · -- α < 0 : J / (1-q)^α = J * (1-q)^(-α) → 0
    have hh : Tendsto (fun q : ℝ => (1 - q) ^ (-α)) (𝓝[<] 1) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (-α) (Or.inr (by linarith))).tendsto
      rw [Real.zero_rpow (by linarith : (-α) ≠ 0)] at this
      exact this.comp h1q
    have hz : Tendsto (fun q => J q / (1 - q) ^ α) (𝓝[<] 1) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using hh.const_mul 4) ?_ ?_
      · exact hev.mono fun q hq => by
          have := (J_bounds hq.1 hq.2).1
          have : 0 ≤ (1 - q) ^ α := (Real.rpow_pos_of_pos (by linarith [hq.2]) _).le
          positivity
      · exact hev.mono fun q hq => by
          have := (J_bounds hq.1 hq.2).2
          have hp : 0 < (1 - q) ^ α := Real.rpow_pos_of_pos (by linarith [hq.2]) _
          rw [Real.rpow_neg (by linarith [hq.2]), div_eq_mul_inv]
          gcongr
    have := tendsto_nhds_unique hlim hz
    rw [this] at hL
    simp at hL
    linarith
  · subst hα
    simp only [Real.rpow_zero, div_one] at hlim
    have : (2 : ℝ) ≤ L := ge_of_tendsto hlim (hev.mono fun q hq => (J_bounds hq.1 hq.2).1)
    rw [abs_of_nonneg (by linarith)] at hL
    linarith
  · have hg : Tendsto (fun q : ℝ => (1 - q) ^ α) (𝓝[<] 1) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
      rw [Real.zero_rpow hα.ne'] at this
      exact this.comp h1q
    have hJ : Tendsto (fun q => J q / (1 - q) ^ α * (1 - q) ^ α) (𝓝[<] 1) (𝓝 (L * 0)) :=
      hlim.mul hg
    have hJ' := hJ.congr' (hg0.mono fun q hq => div_mul_cancel₀ _ hq.ne')
    have : (2 : ℝ) ≤ L * 0 := ge_of_tendsto hJ' (hev.mono fun q hq => (J_bounds hq.1 hq.2).1)
    linarith

end C7685
