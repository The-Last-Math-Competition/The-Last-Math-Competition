/-
  Conjecture 00000004763 — Refutation of Subclaim 1 ("Low-Order Rational Combination"):
  Unbounded Algebraic Degree of Both `classicalToFree` and `freeToClassical`.

  Proves:
  1. Along the Gaussian cumulant ray `gaussRay t` (`c_2 = t`, `c_{n ≠ 2} = 0`),
     `classicalToFree (gaussRay t) (2 * d) = a_d * t^d` for all `d ≥ 1`, `t ∈ ℤ`,
     where `a_d = classicalToFree (gaussRay 1) (2 * d)` is nonzero for infinitely
     many `d` (for every `D`, there exists `d > D` with `a_d ≠ 0`).
  2. Along the Wigner semicircle ray `wignerRay t` (`κ_2 = t`, `κ_{n ≠ 2} = 0`),
     `freeToClassical (wignerRay t) (2 * d) = b_d * t^d` for all `d ≥ 1`, `t ∈ ℤ`,
     where the moments are Catalan numbers `C_d` satisfying `d! (d + 1)! C_d = (2d)!`
     (proved from first principles via the Euler operator on `(1 - 2 z C)^2 = 1 - 4 z`),
     and `b_d = freeToClassical (wignerRay 1) (2 * d)` is nonzero for infinitely
     many `d` (for every `D`, there exists `d > D` with `b_d ≠ 0`).
  3. Consequently, for NO finite degree bound `D` can either conversion be represented
     uniformly across orders `n` by bounded-degree polynomials or even bounded-degree
     rational combinations `P(t) / Q(t)` (`deg P ≤ D`, `deg Q ≤ D`, `Q ≠ 0`).
-/

import Conjecture00000004763.Basic
import Conjecture00000004763.LowOrderAndCrossing

namespace Conjecture00000004763

/-!
## 1. Helper Lemmas on Powers, Absolute Values, and Low-Degree Rational Combinations
-/

theorem neg_le_natAbs (x : Int) : -x ≤ (Int.natAbs x : Int) := by
  omega

theorem natAbs_add_lb (x y : Int) :
    (Int.natAbs y : Int) - (Int.natAbs x : Int) ≤ (Int.natAbs (x + y) : Int) := by
  omega

theorem natAbs_sub_ub (x y : Int) :
    (Int.natAbs (x - y) : Int) ≤ (Int.natAbs x : Int) + (Int.natAbs y : Int) := by
  omega

theorem powZ_add (t : Int) (a b : Nat) : powZ t (a + b) = powZ t a * powZ t b := by
  induction a with
  | zero => simp [powZ]
  | succ a' iha => simp [powZ, Nat.succ_add, iha, Int.mul_assoc]

theorem powZ_mono_base {x y : Int} (hx : 0 ≤ x) (hxy : x ≤ y) (k : Nat) :
    powZ x k ≤ powZ y k := by
  induction k with
  | zero => exact Int.le_refl 1
  | succ u ihu =>
    simp only [powZ]
    exact Int.mul_le_mul hxy ihu (powZ_nonneg hx u) (by omega)

theorem sumRange_natAbs_nonneg (n : Nat) (g : Nat → Int) :
    0 ≤ sumRange n (fun j => (Int.natAbs (g j) : Int)) := by
  have := sumRange_le (n := n) (f := fun _ => 0) (g := fun j => (Int.natAbs (g j) : Int))
    (fun _ _ => by dsimp only; omega)
  simpa [sumRange_const_zero] using this

theorem sumRange_even_filter (d : Nat) (g : Nat → Int) :
    sumRange (2 * d + 1) (fun j => if j % 2 = 0 then g (j / 2) else 0) =
      sumRange (d + 1) g := by
  induction d with
  | zero =>
    simp [sumRange]
  | succ m ih =>
    have hstep : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by omega
    rw [hstep, sumRange_succ, sumRange_succ, ih]
    have hodd : (2 * m + 1) % 2 = 1 := by omega
    have heven : ((2 * m + 1) + 1) % 2 = 0 := by omega
    have hdiv : ((2 * m + 1) + 1) / 2 = m + 1 := by omega
    simp [hodd, heven, hdiv, sumRange]

/-- Evaluate a univariate integer polynomial `∑_{j=0}^D p_j t^j` of degree `≤ D`. -/
def evalPolyZ (D : Nat) (p : Nat → Int) (t : Int) : Int :=
  sumRange (D + 1) (fun j => p j * powZ t j)

theorem powZ_mono_exp {t : Int} (ht : 1 ≤ t) {j D : Nat} (hj : j ≤ D) :
    powZ t j ≤ powZ t D := by
  induction D with
  | zero =>
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst hj0
    exact Int.le_refl _
  | succ m ih =>
    by_cases hle : j ≤ m
    · have h1 := ih hle
      have hpos := powZ_pos ht m
      have hmul := Int.mul_le_mul ht (Int.le_refl (powZ t m)) (by omega) (by omega)
      simp only [powZ] at hmul ⊢
      omega
    · have heq : j = m + 1 := by omega
      subst heq
      exact Int.le_refl _

theorem evalPolyZ_upper_bound (D : Nat) (p : Nat → Int) {t : Int} (ht : 1 ≤ t) :
    (Int.natAbs (evalPolyZ D p t) : Int) ≤
      (sumRange (D + 1) (fun j => (Int.natAbs (p j) : Int))) * powZ t D := by
  have hbound : ∀ sign : Int, (sign = 1 ∨ sign = -1) →
      sign * evalPolyZ D p t ≤
        (sumRange (D + 1) (fun j => (Int.natAbs (p j) : Int))) * powZ t D := by
    intro sign hsign
    unfold evalPolyZ
    rw [← sumRange_mul_left, ← sumRange_mul_right]
    apply sumRange_le
    intro j hj
    have hjle : j ≤ D := Nat.le_of_lt_succ hj
    have hpow : powZ t j ≤ powZ t D := powZ_mono_exp ht hjle
    have hpow_pos : 0 ≤ powZ t j := powZ_nonneg (by omega) j
    have hp_abs : sign * p j ≤ (Int.natAbs (p j) : Int) := by
      have h1 : p j ≤ (Int.natAbs (p j) : Int) := Int.le_natAbs
      have h2 : -p j ≤ (Int.natAbs (p j) : Int) := neg_le_natAbs (p j)
      rcases hsign with rfl | rfl <;> omega
    have hstep1 : (sign * p j) * powZ t j ≤ (Int.natAbs (p j) : Int) * powZ t j :=
      Int.mul_le_mul_of_nonneg_right hp_abs hpow_pos
    have hstep2 : (Int.natAbs (p j) : Int) * powZ t j ≤ (Int.natAbs (p j) : Int) * powZ t D :=
      Int.mul_le_mul_of_nonneg_left hpow (by omega)
    rw [← Int.mul_assoc]
    exact Int.le_trans hstep1 hstep2
  have hpos := hbound 1 (Or.inl rfl)
  have hneg := hbound (-1) (Or.inr rfl)
  omega

/-- No nonzero monomial `a * t^d` with `a ≠ 0` and `d > D` can be represented as a
    rational combination `P(t) / Q(t)` (`a * t^d * Q(t) = P(t)`) with `deg P ≤ D`,
    `deg Q ≤ D`, and `Q` not identically zero on `{0, ..., D}`. -/
theorem monomial_not_low_degree_rational
    {D d : Nat} {a : Int} (hd : D < d) (ha : a ≠ 0)
    (P Q : Nat → Int) (hQ_nz : ∃ k, k ≤ D ∧ Q k ≠ 0) :
    ∃ t : Int, 1 ≤ t ∧ evalPolyZ D Q t ≠ 0 ∧
      a * powZ t d * evalPolyZ D Q t ≠ evalPolyZ D P t := by
  have htop : ∃ K, K ≤ D ∧ Q K ≠ 0 ∧ (∀ j, K < j → j ≤ D → Q j = 0) := by
    induction D with
    | zero =>
      rcases hQ_nz with ⟨k, hk, hqk⟩
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      exact ⟨0, Nat.le_refl 0, hqk, fun _ hj1 hj2 => by omega⟩
    | succ m ih =>
      by_cases htop_m : Q (m + 1) ≠ 0
      · exact ⟨m + 1, Nat.le_refl _, htop_m, fun _ hj1 hj2 => by omega⟩
      · have hqm : Q (m + 1) = 0 := by
          cases Decidable.em (Q (m + 1) = 0) with
          | inl h => exact h
          | inr h => exact absurd h htop_m
        have hsub : ∃ k, k ≤ m ∧ Q k ≠ 0 := by
          rcases hQ_nz with ⟨k, hk, hqk⟩
          by_cases hkm : k ≤ m
          · exact ⟨k, hkm, hqk⟩
          · have heq : k = m + 1 := by omega
            subst heq
            exact absurd hqm hqk
        rcases ih (Nat.lt_of_succ_lt hd) hsub with ⟨K, hKm, hQK, hzero⟩
        refine ⟨K, Nat.le_succ_of_le hKm, hQK, ?_⟩
        intro j hjK hjle
        by_cases hjm : j ≤ m
        · exact hzero j hjK hjm
        · have heq : j = m + 1 := by omega
          subst heq
          exact hqm
  rcases htop with ⟨K, hKD, hQK, hQ_above⟩
  let SP : Int := sumRange (D + 1) P
  -- Use `sumRange_natAbs_nonneg` cleanly:
  clear SP
  let SP : Int := sumRange (D + 1) (fun j => (Int.natAbs (P j) : Int))
  let SQ : Int := sumRange K (fun j => (Int.natAbs (Q j) : Int))
  have hSP_nonneg : 0 ≤ SP := sumRange_natAbs_nonneg (D + 1) P
  have hSQ_nonneg : 0 ≤ SQ := sumRange_natAbs_nonneg K Q
  let t : Int := SP + SQ + 2
  have ht1 : 1 ≤ t := by omega
  have hQ_split : evalPolyZ D Q t = sumRange K (fun j => Q j * powZ t j) + Q K * powZ t K := by
    have htrim : ∀ M, K ≤ M → M ≤ D →
        evalPolyZ M Q t = sumRange K (fun j => Q j * powZ t j) + Q K * powZ t K := by
      intro M hKM hMD
      induction M with
      | zero =>
        have hK0 : K = 0 := Nat.eq_zero_of_le_zero hKM
        subst hK0
        simp [evalPolyZ, sumRange, powZ]
      | succ m ihm =>
        by_cases hKm : K ≤ m
        · unfold evalPolyZ
          rw [sumRange_succ, hQ_above (m + 1) (Nat.lt_succ_of_le hKm) hMD]
          simp only [Int.zero_mul, Int.add_zero]
          exact ihm hKm (Nat.le_of_succ_le hMD)
        · have heq : K = m + 1 := by omega
          subst heq
          rfl
    exact htrim D hKD (Nat.le_refl D)
  have hP_ub : (Int.natAbs (evalPolyZ D P t) : Int) ≤ SP * powZ t D :=
    evalPolyZ_upper_bound D P ht1
  have hpowD_pos : 1 ≤ powZ t D := powZ_pos ht1 D
  have ha_abs : (1 : Int) ≤ (Int.natAbs a : Int) := by omega
  have hQK_abs : (1 : Int) ≤ (Int.natAbs (Q K) : Int) := by omega
  refine ⟨t, ht1, ?_, ?_⟩
  · cases K with
    | zero =>
      rw [hQ_split]
      simp only [sumRange, powZ, Int.zero_add, Int.mul_one]
      exact hQK
    | succ m =>
      have hlow_ub : (Int.natAbs (sumRange (m + 1) (fun j => Q j * powZ t j)) : Int) ≤ SQ * powZ t m :=
        evalPolyZ_upper_bound m Q ht1
      have hpowm_pos : 1 ≤ powZ t m := powZ_pos ht1 m
      have hlead_lb : t * powZ t m ≤ (Int.natAbs (Q (m + 1) * powZ t (m + 1)) : Int) := by
        rw [Int.natAbs_mul, Int.ofNat_mul]
        have hpnonneg : 0 ≤ powZ t (m + 1) := powZ_nonneg (by omega) (m + 1)
        rw [Int.natAbs_of_nonneg hpnonneg, powZ]
        have htp_nn : 0 ≤ t * powZ t m := Int.mul_nonneg (by omega) (by omega)
        have := Int.mul_le_mul hQK_abs (Int.le_refl (t * powZ t m)) htp_nn (by omega)
        simpa using this
      have hlt_pow : SQ * powZ t m < t * powZ t m :=
        Int.mul_lt_mul_of_pos_right (by omega : SQ < t) (by omega)
      have hsub_ineq := Int.sub_le_sub hlead_lb hlow_ub
      have hcomb_lb : t * powZ t m - SQ * powZ t m ≤ (Int.natAbs (evalPolyZ D Q t) : Int) := by
        rw [hQ_split]
        exact Int.le_trans hsub_ineq (natAbs_add_lb _ _)
      intro hzero_Q
      rw [hzero_Q] at hcomb_lb
      simp only [Int.natAbs_zero] at hcomb_lb
      omega
  · have hQ_lb : powZ t D * (SP + 2) ≤ (Int.natAbs (powZ t d * evalPolyZ D Q t) : Int) := by
      rw [Int.natAbs_mul, Int.ofNat_mul]
      have hpd_nonneg : 0 ≤ powZ t d := powZ_nonneg (by omega) d
      rw [Int.natAbs_of_nonneg hpd_nonneg]
      have hd_ge : D + 1 ≤ d := hd
      have hpd_ge : t * powZ t D ≤ powZ t d := by
        have := powZ_mono_exp ht1 hd_ge
        simpa [powZ] using this
      cases K with
      | zero =>
        rw [hQ_split]
        simp only [sumRange, powZ, Int.zero_add, Int.mul_one]
        have h1 : powZ t d * 1 ≤ powZ t d * (Int.natAbs (Q 0) : Int) :=
          Int.mul_le_mul_of_nonneg_left hQK_abs hpd_nonneg
        have h2 : powZ t D * (SP + 2) ≤ t * powZ t D := by
          rw [Int.mul_comm (powZ t D)]
          exact Int.mul_le_mul_of_nonneg_right (by omega : SP + 2 ≤ t) (by omega)
        omega
      | succ m =>
        have hlow_ub : (Int.natAbs (sumRange (m + 1) (fun j => Q j * powZ t j)) : Int) ≤ SQ * powZ t m :=
          evalPolyZ_upper_bound m Q ht1
        have hpowm_pos : 1 ≤ powZ t m := powZ_pos ht1 m
        have hlead_lb : t * powZ t m ≤ (Int.natAbs (Q (m + 1) * powZ t (m + 1)) : Int) := by
          rw [Int.natAbs_mul, Int.ofNat_mul]
          have hpnonneg : 0 ≤ powZ t (m + 1) := powZ_nonneg (by omega) (m + 1)
          rw [Int.natAbs_of_nonneg hpnonneg, powZ]
          have htp_nn : 0 ≤ t * powZ t m := Int.mul_nonneg (by omega) (by omega)
          have := Int.mul_le_mul hQK_abs (Int.le_refl (t * powZ t m)) htp_nn (by omega)
          simpa using this
        have hQ_ge_one : (1 : Int) ≤ (Int.natAbs (evalPolyZ D Q t) : Int) := by
          have hdiff : (SP + 2) * powZ t m = t * powZ t m - SQ * powZ t m := by
            have : t - SQ = SP + 2 := by omega
            rw [← Int.sub_mul, this]
          have hsp_pos : (1 : Int) ≤ SP + 2 := by omega
          have hsp2 : 1 ≤ (SP + 2) * powZ t m := by
            have := Int.mul_le_mul hsp_pos hpowm_pos (by omega) (by omega)
            simpa using this
          have hsub_ineq := Int.sub_le_sub hlead_lb hlow_ub
          rw [← hdiff] at hsub_ineq
          rw [hQ_split]
          exact Int.le_trans hsp2 (Int.le_trans hsub_ineq (natAbs_add_lb _ _))
        have h1 : powZ t d * 1 ≤ powZ t d * (Int.natAbs (evalPolyZ D Q t) : Int) :=
          Int.mul_le_mul_of_nonneg_left hQ_ge_one hpd_nonneg
        have h2 : powZ t D * (SP + 2) ≤ t * powZ t D := by
          rw [Int.mul_comm (powZ t D)]
          exact Int.mul_le_mul_of_nonneg_right (by omega : SP + 2 ≤ t) (by omega)
        omega
    have hfull_lb : powZ t D * (SP + 2) ≤ (Int.natAbs (a * powZ t d * evalPolyZ D Q t) : Int) := by
      rw [Int.mul_assoc, Int.natAbs_mul, Int.ofNat_mul]
      have hlb_nn : 0 ≤ powZ t D * (SP + 2) := Int.mul_nonneg (by omega) (by omega)
      have := Int.mul_le_mul ha_abs hQ_lb hlb_nn (by omega)
      simpa [← Int.mul_assoc] using this
    intro heq_rat
    rw [heq_rat] at hfull_lb
    have hcontra : powZ t D * (SP + 2) ≤ SP * powZ t D := Int.le_trans hfull_lb hP_ub
    have : SP * powZ t D < powZ t D * (SP + 2) := by
      rw [Int.mul_comm (powZ t D), Int.add_mul]
      omega
    omega

/-!
## 2. Gaussian Ray (`gaussRay t`) and Unbounded Degree of `classicalToFree`
-/

/-- Double factorial `dfact d = (2d - 1)!!` (`dfact 0 = 1`, `dfact (d + 1) = (2d + 1) * dfact d`). -/
def dfact : Nat → Int
  | 0 => 1
  | d + 1 => ((2 * d + 1 : Nat) : Int) * dfact d

theorem dfact_pos (d : Nat) : 1 ≤ dfact d := by
  induction d with
  | zero => exact Int.le_refl 1
  | succ m ih =>
    simp only [dfact]
    have hm : (1 : Int) ≤ ((2 * m + 1 : Nat) : Int) := by omega
    have := Int.mul_le_mul hm ih (by omega) (by omega)
    simpa using this

/-- Gaussian cumulant ray: `c_2 = t` and `c_n = 0` for `n ≠ 2`. -/
def gaussRay (t : Int) (n : Nat) : Int :=
  if n = 2 then t else 0

theorem clMoment_gaussRay (t : Int) :
    ∀ n : Nat, clMoment (gaussRay t) n =
      if n % 2 = 0 then dfact (n / 2) * powZ t (n / 2) else 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp [clMoment_zero, dfact, powZ]
    | 1 =>
      rw [clMoment_succ]
      simp [sumRange, gaussRay]
    | m + 2 =>
      rw [clMoment_succ]
      have hcollapse :
          sumRange (m + 2) (fun i => binom (m + 1) i * gaussRay t (i + 1) * clMoment (gaussRay t) (m + 1 - i)) =
          binom (m + 1) 1 * t * clMoment (gaussRay t) m := by
        rw [← sumRange_single (m + 2) 1 (binom (m + 1) 1 * t * clMoment (gaussRay t) m) (by omega)]
        apply sumRange_congr
        intro i _
        by_cases hi1 : i = 1
        · subst hi1; simp [gaussRay]
        · have hne2 : i + 1 ≠ 2 := by omega
          simp [hi1, gaussRay, hne2]
      rw [hcollapse, binom_one_right, ih m (by omega)]
      by_cases hev : m % 2 = 0
      · have hev2 : (m + 2) % 2 = 0 := by omega
        have hdiv : (m + 2) / 2 = m / 2 + 1 := by omega
        have hm2 : 2 * (m / 2) = m := by omega
        simp only [hev, hev2, hdiv, ite_true, dfact, powZ, hm2]
        rw [Int.mul_assoc, Int.mul_left_comm t, ← Int.mul_assoc (((m + 1 : Nat) : Int))]
      · have hodd2 : (m + 2) % 2 ≠ 0 := by omega
        simp [hev, hodd2]

theorem momentConv_gaussRay_scale (t : Int) :
    ∀ r n : Nat, momentConv (clMoment (gaussRay t)) r n =
      if n % 2 = 0 then momentConv (clMoment (gaussRay 1)) r (2 * (n / 2)) * powZ t (n / 2) else 0 := by
  intro r
  induction r with
  | zero =>
    intro n
    cases n with
    | zero => simp [momentConv, powZ]
    | succ m =>
      simp only [momentConv]
      by_cases hev : (m + 1) % 2 = 0
      · have hpos : 0 < (m + 1) / 2 := by omega
        obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        have h2u : 2 * u.succ = (2 * u + 1) + 1 := by omega
        simp [hev, hu, h2u, momentConv]
      · simp [hev]
  | succ r' ih =>
    intro n
    simp only [momentConv]
    by_cases hev : n % 2 = 0
    · obtain ⟨d, rfl⟩ : ∃ d, n = 2 * d := ⟨n / 2, by omega⟩
      have hd_div : (2 * d) / 2 = d := by omega
      have hd_mod : (2 * d) % 2 = 0 := by omega
      simp only [hd_mod, hd_div, ite_true]
      have hcong :
          sumRange (2 * d + 1) (fun j =>
            clMoment (gaussRay t) j * momentConv (clMoment (gaussRay t)) r' (2 * d - j)) =
          sumRange (2 * d + 1) (fun j =>
            (clMoment (gaussRay 1) j * momentConv (clMoment (gaussRay 1)) r' (2 * d - j)) * powZ t d) := by
        apply sumRange_congr
        intro j _
        rw [clMoment_gaussRay t j, clMoment_gaussRay 1 j, ih (2 * d - j)]
        by_cases hjev : j % 2 = 0
        · have hrem_ev : (2 * d - j) % 2 = 0 := by omega
          have hrem2 : 2 * ((2 * d - j) / 2) = 2 * d - j := by omega
          have ht_eq : powZ t (j / 2) * powZ t ((2 * d - j) / 2) = powZ t d := by
            rw [← powZ_add]
            have hdiv_sum : j / 2 + (2 * d - j) / 2 = d := by omega
            rw [hdiv_sum]
          simp only [hjev, hrem_ev, ite_true, powZ_one, Int.mul_one, hrem2]
          calc (dfact (j / 2) * powZ t (j / 2)) *
                (momentConv (clMoment (gaussRay 1)) r' (2 * d - j) * powZ t ((2 * d - j) / 2))
            _ = (dfact (j / 2) * momentConv (clMoment (gaussRay 1)) r' (2 * d - j)) *
                (powZ t (j / 2) * powZ t ((2 * d - j) / 2)) := by
                simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
            _ = (dfact (j / 2) * momentConv (clMoment (gaussRay 1)) r' (2 * d - j)) * powZ t d := by
                rw [ht_eq]
        · simp [hjev]
      rw [hcong, sumRange_mul_right]
    · simp only [hev, ite_false]
      have hcong :
          sumRange (n + 1) (fun j =>
            clMoment (gaussRay t) j * momentConv (clMoment (gaussRay t)) r' (n - j)) =
          sumRange (n + 1) (fun _ => 0) := by
        apply sumRange_congr
        intro j _
        rw [clMoment_gaussRay t j, ih (n - j)]
        by_cases hjev : j % 2 = 0
        · have hrem_odd : (n - j) % 2 ≠ 0 := by omega
          simp [hjev, hrem_odd]
        · simp [hjev]
      rw [hcong, sumRange_const_zero]

/-- Exact homogeneity of `classicalToFree` along `gaussRay t` (inducting simultaneously over all `t`). -/
theorem classicalToFree_gaussRay :
    ∀ (n : Nat) (t : Int), 1 ≤ n → classicalToFree (gaussRay t) n =
      if n % 2 = 0 then classicalToFree (gaussRay 1) n * powZ t (n / 2) else 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t hn
    cases n with
    | zero => omega
    | succ k =>
      unfold classicalToFree at ih ⊢
      rw [frCumulant_succ]
      by_cases hev : (k + 1) % 2 = 0
      · let d := (k + 1) / 2
        have hd_div : (k + 1) / 2 = d := rfl
        simp only [hev, hd_div, ite_true]
        have hsum :
            sumRange k (fun i =>
              frCumulant (clMoment (gaussRay t)) (i + 1) *
                momentConv (clMoment (gaussRay t)) (i + 1) (k - i)) =
            sumRange k (fun i =>
              (frCumulant (clMoment (gaussRay 1)) (i + 1) *
                momentConv (clMoment (gaussRay 1)) (i + 1) (k - i)) * powZ t d) := by
          apply sumRange_congr
          intro i hi
          rw [ih (i + 1) (Nat.succ_lt_succ hi) t (Nat.succ_le_succ (Nat.zero_le i)),
              momentConv_gaussRay_scale t (i + 1) (k - i),
              momentConv_gaussRay_scale 1 (i + 1) (k - i)]
          by_cases hiev : (i + 1) % 2 = 0
          · have hrem_ev : (k - i) % 2 = 0 := by omega
            have ht_eq : powZ t ((i + 1) / 2) * powZ t ((k - i) / 2) = powZ t d := by
              rw [← powZ_add]
              have hdiv_sum : (i + 1) / 2 + (k - i) / 2 = d := by omega
              rw [hdiv_sum]
            simp only [hiev, hrem_ev, ite_true, powZ_one, Int.mul_one]
            calc (frCumulant (clMoment (gaussRay 1)) (i + 1) * powZ t ((i + 1) / 2)) *
                  (momentConv (clMoment (gaussRay 1)) (i + 1) (2 * ((k - i) / 2)) * powZ t ((k - i) / 2))
              _ = (frCumulant (clMoment (gaussRay 1)) (i + 1) *
                    momentConv (clMoment (gaussRay 1)) (i + 1) (2 * ((k - i) / 2))) *
                  (powZ t ((i + 1) / 2) * powZ t ((k - i) / 2)) := by
                  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
              _ = (frCumulant (clMoment (gaussRay 1)) (i + 1) *
                    momentConv (clMoment (gaussRay 1)) (i + 1) (2 * ((k - i) / 2))) * powZ t d := by
                  rw [ht_eq]
          · have ih1 := ih (i + 1) (Nat.succ_lt_succ hi) 1 (Nat.succ_le_succ (Nat.zero_le i))
            simp only [hiev, ite_false] at ih1 ⊢
            rw [ih1]
            simp
        rw [hsum, sumRange_mul_right, clMoment_gaussRay t (k + 1),
            frCumulant_succ (clMoment (gaussRay 1)) k, clMoment_gaussRay 1 (k + 1)]
        simp only [hev, hd_div, ite_true, powZ_one, Int.mul_one, Int.sub_mul]
      · simp only [hev, ite_false]
        rw [clMoment_gaussRay t (k + 1)]
        simp only [hev, ite_false]
        have hsum :
            sumRange k (fun i =>
              frCumulant (clMoment (gaussRay t)) (i + 1) *
                momentConv (clMoment (gaussRay t)) (i + 1) (k - i)) =
            sumRange k (fun _ => 0) := by
          apply sumRange_congr
          intro i hi
          rw [ih (i + 1) (Nat.succ_lt_succ hi) t (Nat.succ_le_succ (Nat.zero_le i)),
              momentConv_gaussRay_scale t (i + 1) (k - i)]
          by_cases hiev : (i + 1) % 2 = 0
          · have hrem_odd : (k - i) % 2 ≠ 0 := by omega
            simp [hiev, hrem_odd]
          · simp [hiev]
        rw [hsum, sumRange_const_zero]
        omega

/-- Sub-multiplicative interior bound on double factorials:
    for `1 ≤ i` and `i + 1 ≤ d`, `dfact i * dfact (d - i) ≤ dfact (d - 1)`. -/
theorem dfact_mul_interior :
    ∀ d i : Nat, 1 ≤ i → i + 1 ≤ d → dfact i * dfact (d - i) ≤ dfact (d - 1) := by
  intro d
  induction d with
  | zero => intros; omega
  | succ m ih =>
    intro i hi1 hid
    by_cases him : i = m
    · rw [him]
      have hsub : m + 1 - m = 1 := by omega
      have hpred : m + 1 - 1 = m := by omega
      rw [hsub, hpred]
      simp [dfact]
    · by_cases hi_eq1 : i = 1
      · rw [hi_eq1]
        have hsub : m + 1 - 1 = m := by omega
        rw [hsub]
        simp [dfact]
      · have hlt : i + 1 ≤ m := by omega
        have hprev := ih i hi1 hlt
        have hstep_sub : m + 1 - i = (m - i) + 1 := by omega
        have hpred_m : m = (m - 1) + 1 := by omega
        have hpred_mp1 : m + 1 - 1 = m := by omega
        rw [hstep_sub, hpred_mp1]
        simp only [dfact]
        rw [Int.mul_left_comm (dfact i)]
        have hstep1 : ((2 * (m - i) + 1 : Nat) : Int) * (dfact i * dfact (m - i)) ≤
            ((2 * (m - i) + 1 : Nat) : Int) * dfact (m - 1) :=
          Int.mul_le_mul_of_nonneg_left hprev (by omega)
        have hcoef : ((2 * (m - i) + 1 : Nat) : Int) ≤ ((2 * (m - 1) + 1 : Nat) : Int) := by omega
        have hstep2 : ((2 * (m - i) + 1 : Nat) : Int) * dfact (m - 1) ≤
            ((2 * (m - 1) + 1 : Nat) : Int) * dfact (m - 1) :=
          Int.mul_le_mul_of_nonneg_right hcoef (Int.le_trans (by omega) (dfact_pos (m - 1)))
        have hrhs : ((2 * (m - 1) + 1 : Nat) : Int) * dfact (m - 1) = dfact m := by
          conv => rhs; rw [hpred_m]; simp only [dfact]
        omega

/-- Exponential bound on Cauchy powers of the Gaussian moment sequence:
    `0 ≤ momentConv (clMoment (gaussRay 1)) r (2 * d) ≤ 3^r * dfact d`. -/
theorem momentConv_gauss_bound :
    ∀ r d : Nat,
      0 ≤ momentConv (clMoment (gaussRay 1)) r (2 * d) ∧
      momentConv (clMoment (gaussRay 1)) r (2 * d) ≤ powZ 3 r * dfact d := by
  have hr2 : ∀ d : Nat, sumRange (d + 1) (fun i => dfact i * dfact (d - i)) ≤ 3 * dfact d := by
    intro d
    match d with
    | 0 => simp [sumRange, dfact]
    | 1 => simp [sumRange, dfact]
    | m + 2 =>
      rw [sumRange_succ]
      have h_top : dfact (m + 2) * dfact (m + 2 - (m + 2)) = dfact (m + 2) := by
        simp [Nat.sub_self, dfact]
      have h_bot_mid :
          sumRange (m + 2) (fun i => dfact i * dfact (m + 2 - i)) ≤
          dfact (m + 2) + ((m + 1 : Nat) : Int) * dfact (m + 1) := by
        have hle := sumRange_le (n := m + 2)
          (f := fun i => dfact i * dfact (m + 2 - i))
          (g := fun i => (if i = 0 then dfact (m + 2) else 0) + (if i = 0 then 0 else dfact (m + 1)))
          (fun i hi => by
            by_cases hi0 : i = 0
            · subst hi0; simp [dfact]
            · simp only [hi0, ite_false, Int.zero_add]
              exact dfact_mul_interior (m + 2) i (by omega) (by omega))
        rw [sumRange_add, sumRange_single (m + 2) 0 (dfact (m + 2)) (by omega)] at hle
        have hconst : ∀ u : Nat, sumRange (u + 1) (fun i => if i = 0 then (0 : Int) else dfact (m + 1)) =
            (u : Int) * dfact (m + 1) := by
          intro u
          induction u with
          | zero => simp [sumRange]
          | succ u' ihu =>
            rw [sumRange_succ, ihu]
            simp [Int.add_mul]
        rw [hconst (m + 1)] at hle
        exact hle
      have hmid_le : ((m + 1 : Nat) : Int) * dfact (m + 1) ≤ dfact (m + 2) := by
        simp only [dfact]
        have hcoef : ((m + 1 : Nat) : Int) ≤ ((2 * (m + 1) + 1 : Nat) : Int) := by omega
        exact Int.mul_le_mul_of_nonneg_right hcoef (Int.le_trans (by omega) (dfact_pos (m + 1)))
      omega
  intro r
  induction r with
  | zero =>
    intro d
    cases d with
    | zero => simp [momentConv, powZ, dfact]
    | succ m =>
      have h2m : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [h2m]
      simp only [momentConv, powZ, Int.one_mul]
      have hpos := dfact_pos (m + 1)
      omega
  | succ r' ih =>
    intro d
    simp only [momentConv]
    have hrewrite :
        sumRange (2 * d + 1) (fun j =>
          clMoment (gaussRay 1) j * momentConv (clMoment (gaussRay 1)) r' (2 * d - j)) =
        sumRange (d + 1) (fun i =>
          dfact i * momentConv (clMoment (gaussRay 1)) r' (2 * (d - i))) := by
      rw [← sumRange_even_filter d (fun i => dfact i * momentConv (clMoment (gaussRay 1)) r' (2 * (d - i)))]
      apply sumRange_congr
      intro j _
      rw [clMoment_gaussRay 1 j, momentConv_gaussRay_scale 1 r' (2 * d - j)]
      by_cases hjev : j % 2 = 0
      · have hrem_ev : (2 * d - j) % 2 = 0 := by omega
        have hrem_div : (2 * d - j) / 2 = d - j / 2 := by omega
        simp [hjev, hrem_ev, hrem_div, powZ_one]
      · simp [hjev]
    rw [hrewrite]
    refine ⟨?_, ?_⟩
    · have h0 := sumRange_le (n := d + 1) (f := fun _ => 0)
        (g := fun i => dfact i * momentConv (clMoment (gaussRay 1)) r' (2 * (d - i)))
        (fun i _ => Int.mul_nonneg (Int.le_trans (by omega) (dfact_pos i)) (ih (d - i)).1)
      simpa [sumRange_const_zero] using h0
    · have hub := sumRange_le (n := d + 1)
        (f := fun i => dfact i * momentConv (clMoment (gaussRay 1)) r' (2 * (d - i)))
        (g := fun i => powZ 3 r' * (dfact i * dfact (d - i)))
        (fun i _ => by
          have hi_ub := Int.mul_le_mul_of_nonneg_left (ih (d - i)).2
            (Int.le_trans (by omega) (dfact_pos i))
          simpa [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using hi_ub)
      rw [sumRange_mul_left] at hub
      have hstep := Int.mul_le_mul_of_nonneg_left (hr2 d) (powZ_nonneg (a := 3) (by omega) r')
      have hpow3 : powZ 3 r' * (3 * dfact d) = powZ 3 (r' + 1) * dfact d := by
        simp [powZ, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      omega

theorem dfact_mono {a b : Nat} (hab : a ≤ b) : dfact a ≤ dfact b := by
  induction b with
  | zero =>
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
    subst ha0
    exact Int.le_refl _
  | succ m ih =>
    by_cases hle : a ≤ m
    · have h1 := ih hle
      simp only [dfact]
      have hpos := dfact_pos m
      have h2 : 1 * dfact m ≤ ((2 * m + 1 : Nat) : Int) * dfact m :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
    · have heq : a = m + 1 := by omega
      subst heq
      exact Int.le_refl _

/-- Key Unboundedness Theorem for `classicalToFree`. -/
theorem gaussRay_classicalToFree_unbounded (D : Nat) :
    ∃ d : Nat, D < d ∧ classicalToFree (gaussRay 1) (2 * d) ≠ 0 := by
  by_cases hex : ∃ d : Nat, D < d ∧ classicalToFree (gaussRay 1) (2 * d) ≠ 0
  · exact hex
  · exfalso
    have hvanish : ∀ d : Nat, D < d → classicalToFree (gaussRay 1) (2 * d) = 0 := by
      intro d hd
      cases Decidable.em (classicalToFree (gaussRay 1) (2 * d) = 0) with
      | inl h => exact h
      | inr h => exact absurd ⟨d, hd, h⟩ hex
    let B : Int := sumRange (2 * D + 1) (fun i =>
      (Int.natAbs (classicalToFree (gaussRay 1) (i + 1)) : Int) * powZ 3 (i + 1))
    have hB_nonneg : 0 ≤ B := by
      have := sumRange_le (n := 2 * D + 1) (f := fun _ => 0)
        (g := fun i => (Int.natAbs (classicalToFree (gaussRay 1) (i + 1)) : Int) * powZ 3 (i + 1))
        (fun i _ => Int.mul_nonneg (by omega) (powZ_nonneg (a := 3) (by omega) (i + 1)))
      simpa [sumRange_const_zero] using this
    let d : Nat := D + Int.toNat B + 1
    have hd_pos : 1 ≤ d := by omega
    have hmom : dfact d = frMoment (classicalToFree (gaussRay 1)) (2 * d) := by
      rw [frMoment_classicalToFree, clMoment_gaussRay 1 (2 * d)]
      have hev : (2 * d) % 2 = 0 := by omega
      have hdiv : (2 * d) / 2 = d := by omega
      simp [hev, hdiv, powZ_one]
    have h2d_eq : 2 * d = (2 * d - 1) + 1 := by omega
    rw [h2d_eq, frMoment_succ, ← h2d_eq] at hmom
    have htrunc :
        sumRange (2 * d) (fun i =>
          classicalToFree (gaussRay 1) (i + 1) *
            momentConv (frMoment (classicalToFree (gaussRay 1))) (i + 1) (2 * d - 1 - i)) =
        sumRange (2 * D + 1) (fun i =>
          if i < 2 * d then
            classicalToFree (gaussRay 1) (i + 1) *
              momentConv (clMoment (gaussRay 1)) (i + 1) (2 * d - 1 - i)
          else 0) := by
      have hfun_eq : frMoment (classicalToFree (gaussRay 1)) = clMoment (gaussRay 1) := by
        funext u; exact frMoment_classicalToFree (gaussRay 1) u
      rw [hfun_eq]
      have hle_M : 2 * D + 1 ≤ 2 * d := by omega
      have htail : ∀ M, 2 * D + 1 ≤ M → M ≤ 2 * d →
          sumRange M (fun i =>
            classicalToFree (gaussRay 1) (i + 1) *
              momentConv (clMoment (gaussRay 1)) (i + 1) (2 * d - 1 - i)) =
          sumRange (2 * D + 1) (fun i =>
            classicalToFree (gaussRay 1) (i + 1) *
              momentConv (clMoment (gaussRay 1)) (i + 1) (2 * d - 1 - i)) := by
        intro M h1 h2
        induction M with
        | zero => omega
        | succ m ihm =>
          by_cases hm_gt : 2 * D + 1 ≤ m
          · rw [sumRange_succ, ihm hm_gt (Nat.le_of_succ_le h2)]
            by_cases hmev : (m + 1) % 2 = 0
            · obtain ⟨j, hj⟩ : ∃ j, m + 1 = 2 * j := ⟨(m + 1) / 2, by omega⟩
              have hjD : D < j := by omega
              rw [hj, hvanish j hjD]
              simp
            · have hodd := classicalToFree_gaussRay (m + 1) 1 (by omega)
              simp only [hmev, ite_false] at hodd
              rw [hodd]
              simp
          · have heq : m + 1 = 2 * D + 1 := by omega
            rw [heq]
      rw [htail (2 * d) hle_M (Nat.le_refl _)]
      apply sumRange_congr
      intro i hi
      have hilt : i < 2 * d := Nat.lt_of_lt_of_le hi hle_M
      simp [hilt]
    rw [htrunc] at hmom
    have hub :
        sumRange (2 * D + 1) (fun i =>
          if i < 2 * d then
            classicalToFree (gaussRay 1) (i + 1) *
              momentConv (clMoment (gaussRay 1)) (i + 1) (2 * d - 1 - i)
          else 0) ≤
        B * dfact (d - 1) := by
      unfold B
      rw [← sumRange_mul_right]
      apply sumRange_le
      intro i _
      have hilt : i < 2 * d := by omega
      simp only [hilt, ite_true]
      rw [momentConv_gaussRay_scale 1 (i + 1) (2 * d - 1 - i)]
      by_cases hrem_ev : (2 * d - 1 - i) % 2 = 0
      · simp only [hrem_ev, ite_true, powZ_one, Int.mul_one]
        have hdiv_le : (2 * d - 1 - i) / 2 ≤ d - 1 := by omega
        have hconv_b := momentConv_gauss_bound (i + 1) ((2 * d - 1 - i) / 2)
        have hdf_le : dfact ((2 * d - 1 - i) / 2) ≤ dfact (d - 1) := dfact_mono hdiv_le
        have habs : classicalToFree (gaussRay 1) (i + 1) ≤
            (Int.natAbs (classicalToFree (gaussRay 1) (i + 1)) : Int) := Int.le_natAbs
        have h1 := Int.mul_le_mul_of_nonneg_right habs hconv_b.1
        have ha_nn : 0 ≤ (Int.natAbs (classicalToFree (gaussRay 1) (i + 1)) : Int) := by omega
        have h2 := Int.mul_le_mul_of_nonneg_left hconv_b.2 ha_nn
        have hp_nn : 0 ≤ (Int.natAbs (classicalToFree (gaussRay 1) (i + 1)) : Int) * powZ 3 (i + 1) :=
          Int.mul_nonneg ha_nn (powZ_nonneg (a := 3) (by omega) (i + 1))
        have h3 := Int.mul_le_mul_of_nonneg_left hdf_le hp_nn
        rw [← Int.mul_assoc] at h2
        omega
      · simp only [hrem_ev, ite_false, Int.mul_zero]
        exact Int.mul_nonneg (Int.mul_nonneg (by omega) (powZ_nonneg (a := 3) (by omega) (i + 1)))
          (Int.le_trans (by omega) (dfact_pos (d - 1)))
    have hdf_eq : dfact d = ((2 * (d - 1) + 1 : Nat) : Int) * dfact (d - 1) := by
      conv => lhs; rw [show d = (d - 1) + 1 by omega]; simp only [dfact]
    have hdf_pos : 1 ≤ dfact (d - 1) := dfact_pos (d - 1)
    have hB_toNat : (Int.toNat B : Int) = B := Int.toNat_of_nonneg hB_nonneg
    have hcoef_gt : B < ((2 * (d - 1) + 1 : Nat) : Int) := by omega
    have hstrict := Int.mul_lt_mul_of_pos_right hcoef_gt (by omega : 0 < dfact (d - 1))
    omega

/-!
## 3. Wigner Semicircle Ray (`wignerRay t`), Formal Power Series Euler Operator,
      Catalan Factorial Identity, and Unbounded Degree of `freeToClassical`
-/

/-- Cauchy product of integer formal power series. -/
def seqMul (A B : Nat → Int) (n : Nat) : Int :=
  sumRange (n + 1) (fun i => A i * B (n - i))

/-- Formal power series Euler operator `(z d/dz A)_n = n * A_n`. -/
def seqEuler (A : Nat → Int) (n : Nat) : Int :=
  (n : Int) * A n

theorem sumRange_reflect (n : Nat) (f : Nat → Int) :
    sumRange (n + 1) f = sumRange (n + 1) (fun i => f (n - i)) := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    rw [sumRange_succ, ih]
    have hpeel : ∀ k (g : Nat → Int),
        sumRange (k + 1) g = g 0 + sumRange k (fun i => g (i + 1)) := by
      intro k g
      induction k with
      | zero => simp [sumRange]
      | succ k' ihk => rw [sumRange_succ, ihk, sumRange_succ]; omega
    rw [hpeel (m + 1) (fun i => f (m + 1 - i))]
    have h0 : m + 1 - 0 = m + 1 := by omega
    have hcong : sumRange (m + 1) (fun i => f (m + 1 - (i + 1))) =
        sumRange (m + 1) (fun i => f (m - i)) := by
      apply sumRange_congr
      intro i _; simp [Nat.succ_sub_succ_eq_sub]
    rw [h0, hcong]
    omega

theorem seqMul_comm (A B : Nat → Int) (n : Nat) :
    seqMul A B n = seqMul B A n := by
  unfold seqMul
  rw [sumRange_reflect]
  apply sumRange_congr
  intro i hi
  have hsub : n - (n - i) = i := by omega
  rw [hsub, Int.mul_comm]

theorem seqEuler_seqMul (A B : Nat → Int) (n : Nat) :
    seqEuler (seqMul A B) n = seqMul (seqEuler A) B n + seqMul A (seqEuler B) n := by
  unfold seqEuler seqMul
  rw [← sumRange_mul_left, ← sumRange_add]
  apply sumRange_congr
  intro i hi
  have hn_split : (n : Int) = (i : Int) + ((n - i : Nat) : Int) := by omega
  rw [hn_split, Int.add_mul]
  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

/-- Fuel-bounded Catalan convolution evaluation (structural recursion on `fuel`). -/
def catalanAux : Nat → Nat → Int
  | _, 0 => 1
  | 0, _ + 1 => 0
  | fuel + 1, d + 1 => sumRange (d + 1) (fun i => catalanAux fuel i * catalanAux fuel (d - i))

theorem catalanAux_zero (f : Nat) : catalanAux f 0 = 1 := by
  cases f <;> rfl

theorem catalanAux_stable :
    ∀ f1 f2 d, d ≤ f1 → d ≤ f2 → catalanAux f1 d = catalanAux f2 d
  | f1, f2, 0, _, _ => by rw [catalanAux_zero, catalanAux_zero]
  | 0, _, _ + 1, h1, _ => by omega
  | _ + 1, 0, _ + 1, _, h2 => by omega
  | f1 + 1, f2 + 1, d + 1, h1, h2 => by
      simp only [catalanAux]
      apply sumRange_congr
      intro i hi
      have hi1 : i ≤ f1 := by omega
      have hi2 : i ≤ f2 := by omega
      have hj1 : d - i ≤ f1 := by omega
      have hj2 : d - i ≤ f2 := by omega
      rw [catalanAux_stable f1 f2 i hi1 hi2, catalanAux_stable f1 f2 (d - i) hj1 hj2]

/-- Catalan numbers `catalan d` via Segner's convolution recurrence. -/
def catalan (d : Nat) : Int := catalanAux d d

theorem catalan_zero : catalan 0 = 1 := rfl

theorem catalan_succ (d : Nat) :
    catalan (d + 1) = sumRange (d + 1) (fun i => catalan i * catalan (d - i)) := by
  unfold catalan
  conv => lhs; simp only [catalanAux]
  apply sumRange_congr
  intro i hi
  rw [catalanAux_stable d i i (by omega) (Nat.le_refl _),
      catalanAux_stable d (d - i) (d - i) (by omega) (Nat.le_refl _)]

/-- Power series `U(z) = 1 - 2 z C(z)`. -/
def uSeries : Nat → Int
  | 0 => 1
  | d + 1 => -2 * catalan d

/-- Power series `V(z) = 1 - 4 z`. -/
def vSeries : Nat → Int
  | 0 => 1
  | 1 => -4
  | _ + 2 => 0

/-- Algebraic identity `(1 - 2 z C(z))^2 = 1 - 4 z` as formal power series. -/
theorem seqMul_uSeries_self (n : Nat) : seqMul uSeries uSeries n = vSeries n := by
  match n with
  | 0 => decide
  | 1 => decide
  | d + 2 =>
    conv => lhs; unfold seqMul
    unfold vSeries
    have hpeel0 : ∀ k (g : Nat → Int),
        sumRange (k + 1) g = g 0 + sumRange k (fun i => g (i + 1)) := by
      intro k g
      induction k with
      | zero => simp [sumRange]
      | succ k' ihk => rw [sumRange_succ, ihk, sumRange_succ]; omega
    rw [sumRange_succ, hpeel0 (d + 1)]
    simp only [Nat.sub_self, Nat.sub_zero]
    have hmid :
        sumRange (d + 1) (fun i => uSeries (i + 1) * uSeries (d + 2 - (i + 1))) =
        4 * catalan (d + 1) := by
      rw [catalan_succ, ← sumRange_mul_left]
      apply sumRange_congr
      intro i hi
      have hsub : d + 2 - (i + 1) = (d - i) + 1 := by omega
      rw [hsub]
      simp only [uSeries]
      calc (-2 * catalan i) * (-2 * catalan (d - i))
        _ = ((-2 : Int) * (-2 : Int)) * (catalan i * catalan (d - i)) := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        _ = 4 * (catalan i * catalan (d - i)) := rfl
    rw [hmid]
    simp only [uSeries, Int.one_mul, Int.mul_one]
    omega

theorem seqMul_uSeries_euler (n : Nat) :
    seqMul uSeries (seqEuler uSeries) n = if n = 1 then -2 else 0 := by
  have heul := seqEuler_seqMul uSeries uSeries n
  have hvv : seqEuler (seqMul uSeries uSeries) n = seqEuler vSeries n := by
    unfold seqEuler
    rw [seqMul_uSeries_self]
  rw [seqMul_comm (seqEuler uSeries) uSeries, hvv] at heul
  match n with
  | 0 =>
    simp only [seqEuler, vSeries, Int.zero_mul, ite_false] at heul ⊢
    omega
  | 1 =>
    simp only [seqEuler, vSeries, ite_true] at heul ⊢
    omega
  | m + 2 =>
    simp only [seqEuler, vSeries, Int.mul_zero] at heul
    have hne : m + 2 ≠ 1 := by omega
    simp only [hne, ite_false]
    omega

theorem catalan_step_recurrence (d : Nat) :
    ((d + 2 : Nat) : Int) * catalan (d + 1) = 2 * ((2 * d + 1 : Nat) : Int) * catalan d := by
  have hassoc : ∀ (A B C : Nat → Int) (n : Nat),
      seqMul (seqMul A B) C n = seqMul A (seqMul B C) n := by
    have htri : ∀ (m : Nat) (F : Nat → Nat → Nat → Int),
        sumRange (m + 1) (fun s => sumRange (s + 1) (fun a => F a (s - a) (m - s))) =
        sumRange (m + 1) (fun a => sumRange (m - a + 1) (fun b => F a b (m - a - b))) := by
      intro m
      induction m with
      | zero => intro F; simp [sumRange]
      | succ m' ihm =>
        intro F
        rw [sumRange_succ (m' + 1) (fun a => sumRange (m' + 1 - a + 1) (fun b => F a b (m' + 1 - a - b)))]
        simp only [Nat.sub_self, Nat.zero_add, sumRange_succ 0, sumRange_zero, Int.zero_add]
        have hrhs_split :
            sumRange (m' + 1) (fun a => sumRange (m' + 1 - a + 1) (fun b => F a b (m' + 1 - a - b))) =
            sumRange (m' + 1) (fun a =>
              sumRange (m' - a + 1) (fun b => F a b (m' + 1 - a - b)) + F a (m' + 1 - a) 0) := by
          apply sumRange_congr
          intro a ha
          have hlen : m' + 1 - a + 1 = (m' - a + 1) + 1 := by omega
          rw [hlen, sumRange_succ]
          have h1 : m' + 1 - a - (m' - a + 1) = 0 := by omega
          have h2 : m' - a + 1 = m' + 1 - a := by omega
          rw [h1, h2]
        rw [hrhs_split, sumRange_add]
        have hih := ihm (fun a b c => F a b (c + 1))
        have hlhs_split :
            sumRange (m' + 1 + 1) (fun s => sumRange (s + 1) (fun a => F a (s - a) (m' + 1 - s))) =
            sumRange (m' + 1) (fun s => sumRange (s + 1) (fun a => F a (s - a) ((m' - s) + 1))) +
              (sumRange (m' + 1) (fun a => F a (m' + 1 - a) 0) + F (m' + 1) 0 0) := by
          rw [sumRange_succ (m' + 1)]
          simp only [Nat.sub_self]
          rw [sumRange_succ (m' + 1) (fun a => F a (m' + 1 - a) 0), Nat.sub_self]
          have hcong1 :
              sumRange (m' + 1) (fun s => sumRange (s + 1) (fun a => F a (s - a) (m' + 1 - s))) =
              sumRange (m' + 1) (fun s => sumRange (s + 1) (fun a => F a (s - a) ((m' - s) + 1))) := by
            apply sumRange_congr
            intro s hs
            apply sumRange_congr
            intro a _
            have hsub : m' + 1 - s = (m' - s) + 1 := by omega
            rw [hsub]
          rw [hcong1]
        have hcong2 :
            sumRange (m' + 1) (fun a => sumRange (m' - a + 1) (fun b => F a b ((m' - a - b) + 1))) =
            sumRange (m' + 1) (fun a => sumRange (m' - a + 1) (fun b => F a b (m' + 1 - a - b))) := by
          apply sumRange_congr
          intro a ha
          apply sumRange_congr
          intro b hb
          have hsub : (m' - a - b) + 1 = m' + 1 - a - b := by omega
          rw [hsub]
        rw [hlhs_split, hih, hcong2]
        omega
    intro A B C n
    unfold seqMul
    have h1 : sumRange (n + 1) (fun s => sumRange (s + 1) (fun a => A a * B (s - a)) * C (n - s)) =
        sumRange (n + 1) (fun s => sumRange (s + 1) (fun a => A a * B (s - a) * C (n - s))) := by
      apply sumRange_congr
      intro s _; rw [sumRange_mul_right]
    have h2 : sumRange (n + 1) (fun a => A a * sumRange (n - a + 1) (fun b => B b * C (n - a - b))) =
        sumRange (n + 1) (fun a => sumRange (n - a + 1) (fun b => A a * B b * C (n - a - b))) := by
      apply sumRange_congr
      intro a _; rw [← sumRange_mul_left]
      apply sumRange_congr
      intro b _; rw [Int.mul_assoc]
    rw [h1, h2, htri n (fun a b c => A a * B b * C c)]
  have eq_assoc := hassoc uSeries uSeries (seqEuler uSeries) (d + 2)
  have hlhs : seqMul (seqMul uSeries uSeries) (seqEuler uSeries) (d + 2) =
      ((d + 2 : Nat) : Int) * (-2 * catalan (d + 1)) + (-4) * (((d + 1 : Nat) : Int) * (-2 * catalan d)) := by
    change sumRange (d + 3) (fun i => seqMul uSeries uSeries i * seqEuler uSeries (d + 2 - i)) = _
    have hpeel0 : ∀ k (g : Nat → Int),
        sumRange (k + 1) g = g 0 + sumRange k (fun i => g (i + 1)) := by
      intro k g
      induction k with
      | zero => simp [sumRange]
      | succ k' ihk => rw [sumRange_succ, ihk, sumRange_succ]; omega
    rw [hpeel0 (d + 2), hpeel0 (d + 1)]
    rw [seqMul_uSeries_self 0, seqMul_uSeries_self 1]
    have htail_zero :
        sumRange (d + 1) (fun i => seqMul uSeries uSeries (i + 1 + 1) * seqEuler uSeries (d + 2 - (i + 1 + 1))) = 0 := by
      rw [← sumRange_const_zero (d + 1)]
      apply sumRange_congr
      intro i _
      rw [seqMul_uSeries_self (i + 1 + 1)]
      simp [vSeries]
    rw [htail_zero]
    have hsub1 : d + 2 - 0 = d + 2 := by omega
    have hsub2 : d + 2 - 1 = d + 1 := by omega
    rw [hsub1, hsub2]
    simp only [vSeries, seqEuler, uSeries, Int.add_zero, Int.one_mul]
  have hrhs : seqMul uSeries (seqMul uSeries (seqEuler uSeries)) (d + 2) = 4 * catalan d := by
    change sumRange (d + 3) (fun i => uSeries i * seqMul uSeries (seqEuler uSeries) (d + 2 - i)) = _
    rw [← sumRange_single (d + 3) (d + 1) (4 * catalan d) (by omega)]
    apply sumRange_congr
    intro i hi
    rw [seqMul_uSeries_euler (d + 2 - i)]
    by_cases hid1 : i = d + 1
    · subst hid1
      have h1 : d + 2 - (d + 1) = 1 := by omega
      rw [h1]
      simp only [ite_true, uSeries]
      omega
    · have hne1 : d + 2 - i ≠ 1 := by omega
      simp [hid1, hne1]
  rw [hlhs, hrhs] at eq_assoc
  have h1 : ((d + 2 : Nat) : Int) * (-2 * catalan (d + 1)) =
      -2 * (((d + 2 : Nat) : Int) * catalan (d + 1)) := by
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  have h2 : (-4 : Int) * (((d + 1 : Nat) : Int) * (-2 * catalan d)) - 4 * catalan d =
      4 * (((2 * d + 1 : Nat) : Int) * catalan d) := by
    have hcast : ((2 * d + 1 : Nat) : Int) = 2 * ((d + 1 : Nat) : Int) - 1 := by omega
    rw [hcast, Int.sub_mul]
    have ht1 : (-4 : Int) * (((d + 1 : Nat) : Int) * (-2 * catalan d)) =
        8 * (((d + 1 : Nat) : Int) * catalan d) := by
      calc (-4 : Int) * (((d + 1 : Nat) : Int) * (-2 * catalan d))
        _ = ((-4 : Int) * (-2 : Int)) * (((d + 1 : Nat) : Int) * catalan d) := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        _ = 8 * (((d + 1 : Nat) : Int) * catalan d) := rfl
    have ht2 : 4 * (2 * ((d + 1 : Nat) : Int) * catalan d - 1 * catalan d) =
        8 * (((d + 1 : Nat) : Int) * catalan d) - 4 * catalan d := by
      rw [Int.mul_sub, Int.one_mul, Int.mul_assoc 2, ← Int.mul_assoc 4 2]
      rfl
    rw [ht1, ht2]
  rw [Int.mul_assoc 2]
  omega

/-- Fundamental Catalan Factorial Identity: `d! * (d + 1)! * catalan d = (2 * d)!`. -/
theorem catalan_mul_factZ (d : Nat) :
    factZ d * factZ (d + 1) * catalan d = factZ (2 * d) := by
  induction d with
  | zero => decide
  | succ m ih =>
    have h2m : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [h2m]
    simp only [factZ]
    have hstep :
        (((m + 1 : Nat) : Int) * factZ m) *
          (((m + 1 + 1 : Nat) : Int) * (((m + 1 : Nat) : Int) * factZ m)) * catalan (m + 1) =
        ((m + 1 : Nat) : Int) * (factZ m * factZ (m + 1)) *
          (((m + 2 : Nat) : Int) * catalan (m + 1)) := by
      simp only [factZ]
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [hstep, catalan_step_recurrence m]
    have hrhs :
        ((m + 1 : Nat) : Int) * (factZ m * factZ (m + 1)) *
          (2 * ((2 * m + 1 : Nat) : Int) * catalan m) =
        ((2 * m + 1 + 1 : Nat) : Int) * (((2 * m + 1 : Nat) : Int) *
          (factZ m * factZ (m + 1) * catalan m)) := by
      have h2mp2 : ((2 * m + 1 + 1 : Nat) : Int) = 2 * ((m + 1 : Nat) : Int) := by omega
      rw [h2mp2]
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [hrhs, ih]

/-- Wigner semicircle cumulant ray: `κ_2 = t` and `κ_n = 0` for `n ≠ 2`. -/
def wignerRay (t : Int) (n : Nat) : Int :=
  if n = 2 then t else 0

theorem frMoment_wignerRay (t : Int) :
    ∀ n : Nat, frMoment (wignerRay t) n =
      if n % 2 = 0 then catalan (n / 2) * powZ t (n / 2) else 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp [frMoment_zero, catalan_zero, powZ]
    | 1 =>
      rw [frMoment_succ]
      simp [sumRange, wignerRay]
    | m + 2 =>
      rw [frMoment_succ]
      have hcollapse :
          sumRange (m + 2) (fun i =>
            wignerRay t (i + 1) * momentConv (frMoment (wignerRay t)) (i + 1) (m + 1 - i)) =
          t * momentConv (frMoment (wignerRay t)) 2 m := by
        rw [← sumRange_single (m + 2) 1 (t * momentConv (frMoment (wignerRay t)) 2 m) (by omega)]
        apply sumRange_congr
        intro i _
        by_cases hi1 : i = 1
        · subst hi1; simp [wignerRay]
        · have hne2 : i + 1 ≠ 2 := by omega
          simp [hi1, wignerRay, hne2]
      rw [hcollapse]
      have hm2_unfold : momentConv (frMoment (wignerRay t)) 2 m =
          sumRange (m + 1) (fun j =>
            frMoment (wignerRay t) j * momentConv (frMoment (wignerRay t)) 1 (m - j)) := rfl
      rw [hm2_unfold]
      have hconv1 : ∀ j, j ≤ m →
          momentConv (frMoment (wignerRay t)) 1 (m - j) = frMoment (wignerRay t) (m - j) := by
        intro j _
        simp only [momentConv]
        rw [← sumRange_single (m - j + 1) (m - j) (frMoment (wignerRay t) (m - j)) (by omega)]
        apply sumRange_congr
        intro u _
        by_cases hum : u = m - j
        · subst hum; simp [Nat.sub_self, momentConv]
        · obtain ⟨w, hw⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m - j - u ≠ 0)
          simp [hum, hw, momentConv]
      by_cases hev : m % 2 = 0
      · obtain ⟨d, rfl⟩ : ∃ d, m = 2 * d := ⟨m / 2, by omega⟩
        have hev2 : (2 * d + 2) % 2 = 0 := by omega
        have hdiv : (2 * d + 2) / 2 = d + 1 := by omega
        simp only [hev2, hdiv, ite_true, catalan_succ, powZ]
        have hcong :
            sumRange (2 * d + 1) (fun j =>
              frMoment (wignerRay t) j * momentConv (frMoment (wignerRay t)) 1 (2 * d - j)) =
            sumRange (2 * d + 1) (fun j =>
              (if j % 2 = 0 then catalan (j / 2) * catalan (d - j / 2) else 0) * powZ t d) := by
          apply sumRange_congr
          intro j hj
          rw [hconv1 j (Nat.le_of_lt_succ hj), ih j (by omega), ih (2 * d - j) (by omega)]
          by_cases hjev : j % 2 = 0
          · have hrem_ev : (2 * d - j) % 2 = 0 := by omega
            have hrem_div : (2 * d - j) / 2 = d - j / 2 := by omega
            have ht_eq : powZ t (j / 2) * powZ t (d - j / 2) = powZ t d := by
              rw [← powZ_add]
              have hdiv_sum : j / 2 + (d - j / 2) = d := by omega
              rw [hdiv_sum]
            simp only [hjev, hrem_ev, hrem_div, ite_true]
            calc (catalan (j / 2) * powZ t (j / 2)) * (catalan (d - j / 2) * powZ t (d - j / 2))
              _ = (catalan (j / 2) * catalan (d - j / 2)) * (powZ t (j / 2) * powZ t (d - j / 2)) := by
                  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
              _ = (catalan (j / 2) * catalan (d - j / 2)) * powZ t d := by rw [ht_eq]
          · simp [hjev]
        rw [hcong, sumRange_mul_right,
            sumRange_even_filter d (fun i => catalan i * catalan (d - i))]
        simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      · have hodd2 : (m + 2) % 2 ≠ 0 := by omega
        simp only [hodd2, ite_false]
        have hcong :
            sumRange (m + 1) (fun j =>
              frMoment (wignerRay t) j * momentConv (frMoment (wignerRay t)) 1 (m - j)) = 0 := by
          rw [← sumRange_const_zero (m + 1)]
          apply sumRange_congr
          intro j hj
          rw [hconv1 j (Nat.le_of_lt_succ hj), ih j (by omega), ih (m - j) (by omega)]
          by_cases hjev : j % 2 = 0
          · have hrem_odd : (m - j) % 2 ≠ 0 := by omega
            simp [hjev, hrem_odd]
          · simp [hjev]
        rw [hcong, Int.mul_zero]

theorem frMoment_wignerRay_one (n : Nat) :
    frMoment (wignerRay 1) n = if n % 2 = 0 then catalan (n / 2) else 0 := by
  rw [frMoment_wignerRay 1 n]
  by_cases hev : n % 2 = 0 <;> simp [hev, powZ_one]

/-- Exact homogeneity of `freeToClassical` along `wignerRay t` (inducting simultaneously over all `t`). -/
theorem freeToClassical_wignerRay :
    ∀ (n : Nat) (t : Int), 1 ≤ n → freeToClassical (wignerRay t) n =
      if n % 2 = 0 then freeToClassical (wignerRay 1) n * powZ t (n / 2) else 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t hn
    cases n with
    | zero => omega
    | succ k =>
      unfold freeToClassical at ih ⊢
      rw [clCumulant_succ]
      by_cases hev : (k + 1) % 2 = 0
      · let d := (k + 1) / 2
        have hd_div : (k + 1) / 2 = d := rfl
        simp only [hev, hd_div, ite_true]
        have hsum :
            sumRange k (fun i =>
              binom k i * clCumulant (frMoment (wignerRay t)) (i + 1) *
                frMoment (wignerRay t) (k - i)) =
            sumRange k (fun i =>
              (binom k i * clCumulant (frMoment (wignerRay 1)) (i + 1) *
                frMoment (wignerRay 1) (k - i)) * powZ t d) := by
          apply sumRange_congr
          intro i hi
          rw [ih (i + 1) (Nat.succ_lt_succ hi) t (Nat.succ_le_succ (Nat.zero_le i)),
              frMoment_wignerRay t (k - i), frMoment_wignerRay 1 (k - i)]
          by_cases hiev : (i + 1) % 2 = 0
          · have hrem_ev : (k - i) % 2 = 0 := by omega
            have ht_eq : powZ t ((i + 1) / 2) * powZ t ((k - i) / 2) = powZ t d := by
              rw [← powZ_add]
              have hdiv_sum : (i + 1) / 2 + (k - i) / 2 = d := by omega
              rw [hdiv_sum]
            simp only [hiev, hrem_ev, ite_true, powZ_one, Int.mul_one]
            calc binom k i * (clCumulant (frMoment (wignerRay 1)) (i + 1) * powZ t ((i + 1) / 2)) *
                  (catalan ((k - i) / 2) * powZ t ((k - i) / 2))
              _ = (binom k i * clCumulant (frMoment (wignerRay 1)) (i + 1) * catalan ((k - i) / 2)) *
                  (powZ t ((i + 1) / 2) * powZ t ((k - i) / 2)) := by
                  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
              _ = (binom k i * clCumulant (frMoment (wignerRay 1)) (i + 1) * catalan ((k - i) / 2)) * powZ t d := by
                  rw [ht_eq]
          · have ih1 := ih (i + 1) (Nat.succ_lt_succ hi) 1 (Nat.succ_le_succ (Nat.zero_le i))
            simp only [hiev, ite_false] at ih1 ⊢
            rw [ih1]
            simp
        rw [hsum, sumRange_mul_right, frMoment_wignerRay t (k + 1),
            clCumulant_succ (frMoment (wignerRay 1)) k, frMoment_wignerRay 1 (k + 1)]
        simp only [hev, hd_div, ite_true, powZ_one, Int.mul_one, Int.sub_mul]
      · simp only [hev, ite_false]
        rw [frMoment_wignerRay t (k + 1)]
        simp only [hev, ite_false]
        have hsum :
            sumRange k (fun i =>
              binom k i * clCumulant (frMoment (wignerRay t)) (i + 1) *
                frMoment (wignerRay t) (k - i)) = 0 := by
          rw [← sumRange_const_zero k]
          apply sumRange_congr
          intro i hi
          rw [ih (i + 1) (Nat.succ_lt_succ hi) t (Nat.succ_le_succ (Nat.zero_le i)),
              frMoment_wignerRay t (k - i)]
          by_cases hiev : (i + 1) % 2 = 0
          · have hrem_odd : (k - i) % 2 ≠ 0 := by omega
            simp [hiev, hrem_odd]
          · simp [hiev]
        rw [hsum]
        omega

/-- Falling factorial `fallZ d j = d * (d - 1) * ... * (d - j + 1)`. -/
def fallZ : Nat → Nat → Int
  | _, 0 => 1
  | 0, _ + 1 => 0
  | d + 1, j + 1 => ((d + 1 : Nat) : Int) * fallZ d j

theorem fallZ_zero_right (d : Nat) : fallZ d 0 = 1 := by
  cases d <;> rfl

theorem fallZ_mul_factZ : ∀ d j : Nat, j ≤ d → fallZ d j * factZ (d - j) = factZ d := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst hj0
    rfl
  | succ m ih =>
    intro j hj
    cases j with
    | zero => simp [fallZ]
    | succ j' =>
      simp only [fallZ, Nat.succ_sub_succ_eq_sub, factZ]
      rw [Int.mul_assoc, ih j' (Nat.le_of_succ_le_succ hj)]

theorem fallZ_lower_bound : ∀ d j : Nat, j ≤ d → powZ ((d - j + 1 : Nat) : Int) j ≤ fallZ d j := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst hj0
    exact Int.le_refl 1
  | succ m ih =>
    intro j hj
    cases j with
    | zero => exact Int.le_refl 1
    | succ j' =>
      simp only [fallZ, powZ, Nat.succ_sub_succ_eq_sub]
      have h1 : ((m - j' + 1 : Nat) : Int) ≤ ((m + 1 : Nat) : Int) := by omega
      have h2 := ih j' (Nat.le_of_succ_le_succ hj)
      have hpos : 0 ≤ powZ ((m - j' + 1 : Nat) : Int) j' := powZ_nonneg (by omega) j'
      exact Int.mul_le_mul h1 h2 hpos (by omega)

theorem fallZ_upper_bound : ∀ d j : Nat, 0 ≤ fallZ d j ∧ fallZ d j ≤ powZ (d : Int) j := by
  intro d
  induction d with
  | zero =>
    intro j
    cases j <;> simp [fallZ, powZ]
  | succ m ih =>
    intro j
    cases j with
    | zero => simp [fallZ, powZ]
    | succ j' =>
      simp only [fallZ, powZ]
      have ⟨h0, hub⟩ := ih j'
      refine ⟨Int.mul_nonneg (by omega) h0, ?_⟩
      have hbase := powZ_mono_base (x := (m : Int)) (y := ((m + 1 : Nat) : Int)) (by omega) (by omega) j'
      exact Int.mul_le_mul_of_nonneg_left (Int.le_trans hub hbase) (by omega)

theorem wigner_catalan_term_identity (d j : Nat) (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    factZ d * factZ (d + 1) * (binom (2 * d - 1) (2 * j - 1) * catalan (d - j)) * factZ (2 * j - 1) =
      factZ (2 * d - 1) * (fallZ d j * fallZ (d + 1) j) := by
  have hpos1 : 1 ≤ factZ (d - j) := factZ_pos (d - j)
  have hpos2 : 1 ≤ factZ (d + 1 - j) := factZ_pos (d + 1 - j)
  have hpos : 0 < factZ (d - j) * factZ (d + 1 - j) := Int.mul_pos (by omega) (by omega)
  have hcat := catalan_mul_factZ (d - j)
  have hd_sub : d - j + 1 = d + 1 - j := by omega
  rw [hd_sub] at hcat
  have hbin := binom_mul_factZ (2 * d - 1) (2 * j - 1) (by omega)
  have h2d_sub : 2 * d - 1 - (2 * j - 1) = 2 * (d - j) := by omega
  rw [h2d_sub] at hbin
  have hlhs_prod :
      (factZ d * factZ (d + 1) * (binom (2 * d - 1) (2 * j - 1) * catalan (d - j)) * factZ (2 * j - 1)) *
        (factZ (d - j) * factZ (d + 1 - j)) =
      factZ d * factZ (d + 1) * factZ (2 * d - 1) := by
    calc (factZ d * factZ (d + 1) * (binom (2 * d - 1) (2 * j - 1) * catalan (d - j)) * factZ (2 * j - 1)) *
          (factZ (d - j) * factZ (d + 1 - j))
      _ = factZ d * factZ (d + 1) *
            ((binom (2 * d - 1) (2 * j - 1) * factZ (2 * j - 1)) *
              (factZ (d - j) * factZ (d + 1 - j) * catalan (d - j))) := by
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = factZ d * factZ (d + 1) *
            (binom (2 * d - 1) (2 * j - 1) * factZ (2 * j - 1) * factZ (2 * (d - j))) := by
          rw [hcat, Int.mul_assoc (binom _ _)]
      _ = factZ d * factZ (d + 1) * factZ (2 * d - 1) := by
          rw [hbin]
  have hf1 := fallZ_mul_factZ d j hjd
  have hf2 := fallZ_mul_factZ (d + 1) j (by omega)
  have hrhs_prod :
      (factZ (2 * d - 1) * (fallZ d j * fallZ (d + 1) j)) *
        (factZ (d - j) * factZ (d + 1 - j)) =
      factZ d * factZ (d + 1) * factZ (2 * d - 1) := by
    calc (factZ (2 * d - 1) * (fallZ d j * fallZ (d + 1) j)) *
          (factZ (d - j) * factZ (d + 1 - j))
      _ = (fallZ d j * factZ (d - j)) * (fallZ (d + 1) j * factZ (d + 1 - j)) * factZ (2 * d - 1) := by
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = factZ d * factZ (d + 1) * factZ (2 * d - 1) := by
          rw [hf1, hf2]
  have heq_mul :
      (factZ d * factZ (d + 1) * (binom (2 * d - 1) (2 * j - 1) * catalan (d - j)) * factZ (2 * j - 1)) *
        (factZ (d - j) * factZ (d + 1 - j)) =
      (factZ (2 * d - 1) * (fallZ d j * fallZ (d + 1) j)) *
        (factZ (d - j) * factZ (d + 1 - j)) := by
    rw [hlhs_prod, hrhs_prod]
  exact Int.eq_of_mul_eq_mul_right (by omega) heq_mul

/-- Key Unboundedness Theorem for `freeToClassical`. -/
theorem wignerRay_freeToClassical_unbounded (D : Nat) :
    ∃ d : Nat, D < d ∧ freeToClassical (wignerRay 1) (2 * d) ≠ 0 := by
  have hb2 : freeToClassical (wignerRay 1) 4 = -1 := by
    rw [freeToClassical_four]
    simp [wignerRay]
  by_cases hD1 : D < 2
  · exact ⟨2, hD1, by rw [hb2]; decide⟩
  · by_cases hex : ∃ d : Nat, D < d ∧ freeToClassical (wignerRay 1) (2 * d) ≠ 0
    · exact hex
    · exfalso
      have hvanish : ∀ d : Nat, D < d → freeToClassical (wignerRay 1) (2 * d) = 0 := by
        intro d hd
        cases Decidable.em (freeToClassical (wignerRay 1) (2 * d) = 0) with
        | inl h => exact h
        | inr h => exact absurd ⟨d, hd, h⟩ hex
      have htop : ∃ K, 2 ≤ K ∧ K ≤ D ∧ freeToClassical (wignerRay 1) (2 * K) ≠ 0 ∧
          (∀ j, K < j → freeToClassical (wignerRay 1) (2 * j) = 0) := by
        have haux : ∀ M, 2 ≤ M → M ≤ D →
            ∃ K, 2 ≤ K ∧ K ≤ M ∧ freeToClassical (wignerRay 1) (2 * K) ≠ 0 ∧
              (∀ j, K < j → j ≤ M → freeToClassical (wignerRay 1) (2 * j) = 0) := by
          intro M h2M hMD
          induction M with
          | zero => omega
          | succ m ihm =>
            by_cases hm2 : 2 ≤ m
            · by_cases htop_m : freeToClassical (wignerRay 1) (2 * (m + 1)) ≠ 0
              · exact ⟨m + 1, by omega, Nat.le_refl _, htop_m, fun _ hj1 hj2 => by omega⟩
              · have hzm : freeToClassical (wignerRay 1) (2 * (m + 1)) = 0 := by
                  cases Decidable.em (freeToClassical (wignerRay 1) (2 * (m + 1)) = 0) with
                  | inl h => exact h
                  | inr h => exact absurd h htop_m
                rcases ihm hm2 (Nat.le_of_succ_le hMD) with ⟨K, h2K, hKm, hK_nz, hK_above⟩
                refine ⟨K, h2K, Nat.le_succ_of_le hKm, hK_nz, ?_⟩
                intro j hjK hjle
                by_cases hjm : j ≤ m
                · exact hK_above j hjK hjm
                · have heq : j = m + 1 := by omega
                  subst heq; exact hzm
            · have heq : m + 1 = 2 := by omega
              rw [heq]
              exact ⟨2, Nat.le_refl 2, Nat.le_refl 2, by rw [hb2]; decide, fun _ hj1 hj2 => by omega⟩
        rcases haux D (by omega) (Nat.le_refl D) with ⟨K, h2K, hKD, hK_nz, hK_leD⟩
        refine ⟨K, h2K, hKD, hK_nz, ?_⟩
        intro j hjK
        by_cases hjD : j ≤ D
        · exact hK_leD j hjK hjD
        · exact hvanish j (by omega)
      rcases htop with ⟨K, h2K, _, hbK_nz, hb_above⟩
      let scaleJ (j : Nat) : Int := fallZ (2 * K - 1) (2 * K - 2 * j)
      have hscale_mul : ∀ j, 1 ≤ j → j ≤ K → scaleJ j * factZ (2 * j - 1) = factZ (2 * K - 1) := by
        intro j hj1 hjK
        have hsub : 2 * K - 1 - (2 * K - 2 * j) = 2 * j - 1 := by omega
        have hf := fallZ_mul_factZ (2 * K - 1) (2 * K - 2 * j) (by omega)
        rw [hsub] at hf
        exact hf
      have hpoly_id : ∀ d : Nat, K < d →
          ((2 * d : Nat) : Int) * factZ (2 * K - 1) =
          sumRange K (fun u =>
            freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1) *
              (fallZ d (u + 1) * fallZ (d + 1) (u + 1))) := by
        intro d hdK
        have hmom : catalan d = clMoment (freeToClassical (wignerRay 1)) (2 * d) := by
          rw [clMoment_freeToClassical, frMoment_wignerRay_one (2 * d)]
          have hev : (2 * d) % 2 = 0 := by omega
          have hdiv : (2 * d) / 2 = d := by omega
          simp [hev, hdiv]
        have h2d_eq : 2 * d = (2 * d - 1) + 1 := by omega
        conv at hmom => rhs; rw [h2d_eq, clMoment_succ]
        rw [← h2d_eq] at hmom
        have heven_sum :
            sumRange (2 * d) (fun i =>
              binom (2 * d - 1) i * freeToClassical (wignerRay 1) (i + 1) *
                clMoment (freeToClassical (wignerRay 1)) (2 * d - 1 - i)) =
            sumRange d (fun u =>
              binom (2 * d - 1) (2 * (u + 1) - 1) * freeToClassical (wignerRay 1) (2 * (u + 1)) *
                catalan (d - (u + 1))) := by
          have hpair : ∀ t, t ≤ d →
              sumRange (2 * t) (fun i =>
                binom (2 * d - 1) i * freeToClassical (wignerRay 1) (i + 1) *
                  clMoment (freeToClassical (wignerRay 1)) (2 * d - 1 - i)) =
              sumRange t (fun u =>
                binom (2 * d - 1) (2 * (u + 1) - 1) * freeToClassical (wignerRay 1) (2 * (u + 1)) *
                  catalan (d - (u + 1))) := by
            intro t htd
            induction t with
            | zero => rfl
            | succ t' iht =>
              have h2t : 2 * (t' + 1) = (2 * t' + 1) + 1 := by omega
              rw [h2t, sumRange_succ, sumRange_succ, iht (Nat.le_of_succ_le htd), sumRange_succ]
              have hodd_c := freeToClassical_wignerRay (2 * t' + 1) 1 (by omega)
              have hodd_m : (2 * t' + 1) % 2 ≠ 0 := by omega
              simp only [hodd_m, ite_false] at hodd_c
              rw [hodd_c]
              simp only [Int.mul_zero, Int.zero_mul, Int.add_zero]
              have h2tp2 : 2 * t' + 1 + 1 = 2 * (t' + 1) := by omega
              have hrem : 2 * d - 1 - (2 * t' + 1) = 2 * (d - (t' + 1)) := by omega
              have hrem_ev : (2 * (d - (t' + 1))) % 2 = 0 := by omega
              have hrem_div : (2 * (d - (t' + 1))) / 2 = d - (t' + 1) := by omega
              have hidx : 2 * (t' + 1) - 1 = 2 * t' + 1 := by omega
              rw [h2tp2, hrem, hidx, clMoment_freeToClassical, frMoment_wignerRay_one]
              simp only [hrem_ev, hrem_div, ite_true]
          exact hpair d (Nat.le_refl d)
        have htrunc_K :
            sumRange d (fun u =>
              binom (2 * d - 1) (2 * (u + 1) - 1) * freeToClassical (wignerRay 1) (2 * (u + 1)) *
                catalan (d - (u + 1))) =
            sumRange K (fun u =>
              binom (2 * d - 1) (2 * (u + 1) - 1) * freeToClassical (wignerRay 1) (2 * (u + 1)) *
                catalan (d - (u + 1))) := by
          have hauxK : ∀ M, K ≤ M → M ≤ d →
              sumRange M (fun u =>
                binom (2 * d - 1) (2 * (u + 1) - 1) * freeToClassical (wignerRay 1) (2 * (u + 1)) *
                  catalan (d - (u + 1))) =
              sumRange K (fun u =>
                binom (2 * d - 1) (2 * (u + 1) - 1) * freeToClassical (wignerRay 1) (2 * (u + 1)) *
                  catalan (d - (u + 1))) := by
            intro M hKM hMd
            induction M with
            | zero => omega
            | succ m ihm =>
              by_cases hKm : K ≤ m
              · rw [sumRange_succ, ihm hKm (Nat.le_of_succ_le hMd), hb_above (m + 1) (by omega)]
                simp
              · have heq : m + 1 = K := by omega
                rw [heq]
          exact hauxK d (Nat.le_of_lt hdK) (Nat.le_refl d)
        rw [heven_sum, htrunc_K] at hmom
        have hlhs_f :
            factZ d * factZ (d + 1) * catalan d * factZ (2 * K - 1) =
            factZ (2 * d - 1) * (((2 * d : Nat) : Int) * factZ (2 * K - 1)) := by
          rw [catalan_mul_factZ d]
          have h2d_f : factZ (2 * d) = ((2 * d : Nat) : Int) * factZ (2 * d - 1) := by
            conv => lhs; rw [show 2 * d = (2 * d - 1) + 1 by omega]; simp only [factZ]
            rw [show (2 * d - 1) + 1 = 2 * d by omega]
          rw [h2d_f]
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        have hrhs_f :
            factZ d * factZ (d + 1) *
              sumRange K (fun u =>
                binom (2 * d - 1) (2 * (u + 1) - 1) * freeToClassical (wignerRay 1) (2 * (u + 1)) *
                  catalan (d - (u + 1))) * factZ (2 * K - 1) =
            factZ (2 * d - 1) *
              sumRange K (fun u =>
                freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1) *
                  (fallZ d (u + 1) * fallZ (d + 1) (u + 1))) := by
          rw [← sumRange_mul_left, ← sumRange_mul_right, ← sumRange_mul_left]
          apply sumRange_congr
          intro u hu
          have huK : u + 1 ≤ K := Nat.succ_le_of_lt hu
          have hud : u + 1 ≤ d := Nat.le_trans huK (Nat.le_of_lt hdK)
          rw [← hscale_mul (u + 1) (by omega) huK]
          have hterm := wigner_catalan_term_identity d (u + 1) (by omega) hud
          calc factZ d * factZ (d + 1) *
                (binom (2 * d - 1) (2 * (u + 1) - 1) * freeToClassical (wignerRay 1) (2 * (u + 1)) *
                  catalan (d - (u + 1))) * (scaleJ (u + 1) * factZ (2 * (u + 1) - 1))
            _ = (freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1)) *
                  (factZ d * factZ (d + 1) *
                    (binom (2 * d - 1) (2 * (u + 1) - 1) * catalan (d - (u + 1))) *
                    factZ (2 * (u + 1) - 1)) := by
                simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
            _ = (freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1)) *
                  (factZ (2 * d - 1) * (fallZ d (u + 1) * fallZ (d + 1) (u + 1))) := by
                rw [hterm]
            _ = factZ (2 * d - 1) *
                  (freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1) *
                    (fallZ d (u + 1) * fallZ (d + 1) (u + 1))) := by
                simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        have hcomb :
            factZ (2 * d - 1) * (((2 * d : Nat) : Int) * factZ (2 * K - 1)) =
            factZ (2 * d - 1) *
              sumRange K (fun u =>
                freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1) *
                  (fallZ d (u + 1) * fallZ (d + 1) (u + 1))) := by
          rw [← hlhs_f, ← hrhs_f, hmom]
        have hfpos : factZ (2 * d - 1) ≠ 0 := by
          have := factZ_pos (2 * d - 1); omega
        exact Int.eq_of_mul_eq_mul_left hfpos hcomb
      let C_low : Int := sumRange (K - 1) (fun u =>
        (Int.natAbs (freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1)) : Int))
      have hC_low_nonneg : 0 ≤ C_low :=
        sumRange_natAbs_nonneg (K - 1) (fun u => freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1))
      let Coef : Int := 4 * factZ (2 * K - 1) + C_low * powZ 2 (2 * K - 2)
      have hCoef_pos : 1 ≤ Coef := by
        have hf := factZ_pos (2 * K - 1)
        have hp := powZ_nonneg (a := 2) (by omega) (2 * K - 2)
        have hm := Int.mul_nonneg hC_low_nonneg hp
        omega
      let M_nat : Nat := K + Int.toNat Coef + 2
      let d : Nat := M_nat + K - 1
      have hdK : K < d := by omega
      have hM_eq : d - K + 1 = M_nat := by omega
      have hd1_le : ((d + 1 : Nat) : Int) ≤ 2 * (M_nat : Int) := by omega
      have hid := hpoly_id d hdK
      have hK_pred : K = (K - 1) + 1 := by omega
      conv at hid => rhs; rw [hK_pred, sumRange_succ]
      have hKm1_succ : (K - 1) + 1 = K := by omega
      have hscaleK : scaleJ K = 1 := by
        unfold scaleJ
        have : 2 * K - 2 * K = 0 := by omega
        rw [this]
        exact fallZ_zero_right (2 * K - 1)
      rw [hKm1_succ, hscaleK, Int.mul_one] at hid
      have hiso :
          freeToClassical (wignerRay 1) (2 * K) * (fallZ d K * fallZ (d + 1) K) =
          ((2 * d : Nat) : Int) * factZ (2 * K - 1) -
            sumRange (K - 1) (fun u =>
              freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1) *
                (fallZ d (u + 1) * fallZ (d + 1) (u + 1))) := by
        omega
      have hlhs_lb : powZ (M_nat : Int) (2 * K) ≤
          (Int.natAbs (freeToClassical (wignerRay 1) (2 * K) * (fallZ d K * fallZ (d + 1) K)) : Int) := by
        have h1 := fallZ_lower_bound d K (by omega)
        have h2 := fallZ_lower_bound (d + 1) K (by omega)
        rw [hM_eq] at h1
        have hM2 : powZ (M_nat : Int) K ≤ powZ ((d + 1 - K + 1 : Nat) : Int) K :=
          powZ_mono_base (by omega) (by omega) K
        have hprod_lb : powZ (M_nat : Int) (2 * K) ≤ fallZ d K * fallZ (d + 1) K := by
          have h2K_add : 2 * K = K + K := by omega
          rw [h2K_add, powZ_add]
          exact Int.mul_le_mul h1 (Int.le_trans hM2 h2)
            (powZ_nonneg (by omega) K) (fallZ_upper_bound d K).1
        have hprod_nonneg : 0 ≤ fallZ d K * fallZ (d + 1) K :=
          Int.mul_nonneg (fallZ_upper_bound d K).1 (fallZ_upper_bound (d + 1) K).1
        rw [Int.natAbs_mul, Int.ofNat_mul, Int.natAbs_of_nonneg hprod_nonneg]
        have hbK_abs : (1 : Int) ≤ (Int.natAbs (freeToClassical (wignerRay 1) (2 * K)) : Int) := by omega
        have := Int.mul_le_mul hbK_abs hprod_lb (powZ_nonneg (by omega) (2 * K)) (by omega)
        simpa using this
      have hpow_mul_2M : ∀ r : Nat, powZ (2 * (M_nat : Int)) r = powZ 2 r * powZ (M_nat : Int) r := by
        intro r
        induction r with
        | zero => simp [powZ]
        | succ r' ihr =>
          simp only [powZ, ihr, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      have hpow_d1_ub : ∀ j : Nat, j ≤ K - 1 →
          fallZ d j * fallZ (d + 1) j ≤ powZ 2 (2 * K - 2) * powZ (M_nat : Int) (2 * K - 2) := by
        intro j hj
        have hf_d := (fallZ_upper_bound d j).2
        have hf_d1 := (fallZ_upper_bound (d + 1) j).2
        have hd_le_d1 : powZ (d : Int) j ≤ powZ ((d + 1 : Nat) : Int) j :=
          powZ_mono_base (by omega) (by omega) j
        have hprod1 : fallZ d j * fallZ (d + 1) j ≤
            powZ ((d + 1 : Nat) : Int) (j + j) := by
          rw [powZ_add]
          exact Int.mul_le_mul (Int.le_trans hf_d hd_le_d1) hf_d1
            (fallZ_upper_bound (d + 1) j).1 (powZ_nonneg (by omega) j)
        have hprod2 : powZ ((d + 1 : Nat) : Int) (j + j) ≤ powZ ((d + 1 : Nat) : Int) (2 * K - 2) :=
          powZ_mono_exp (by omega) (by omega)
        have hprod3 : powZ ((d + 1 : Nat) : Int) (2 * K - 2) ≤ powZ (2 * (M_nat : Int)) (2 * K - 2) :=
          powZ_mono_base (by omega) hd1_le (2 * K - 2)
        rw [hpow_mul_2M] at hprod3
        exact Int.le_trans hprod1 (Int.le_trans hprod2 hprod3)
      have hsum_abs_ub :
          (Int.natAbs (sumRange (K - 1) (fun u =>
            freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1) *
              (fallZ d (u + 1) * fallZ (d + 1) (u + 1)))) : Int) ≤
          C_low * (powZ 2 (2 * K - 2) * powZ (M_nat : Int) (2 * K - 2)) := by
        have hsign : ∀ s : Int, (s = 1 ∨ s = -1) →
            s * sumRange (K - 1) (fun u =>
              freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1) *
                (fallZ d (u + 1) * fallZ (d + 1) (u + 1))) ≤
            C_low * (powZ 2 (2 * K - 2) * powZ (M_nat : Int) (2 * K - 2)) := by
          intro s hs
          unfold C_low
          rw [← sumRange_mul_left, ← sumRange_mul_right]
          apply sumRange_le
          intro u hu
          have hj_le : u + 1 ≤ K - 1 := Nat.succ_le_of_lt hu
          have hfall_nonneg : 0 ≤ fallZ d (u + 1) * fallZ (d + 1) (u + 1) :=
            Int.mul_nonneg (fallZ_upper_bound d (u + 1)).1 (fallZ_upper_bound (d + 1) (u + 1)).1
          have hc_abs : s * (freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1)) ≤
              (Int.natAbs (freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1)) : Int) := by
            have h1 := Int.le_natAbs (a := freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1))
            have h2 := neg_le_natAbs (freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1))
            rcases hs with rfl | rfl <;> omega
          rw [← Int.mul_assoc s]
          have hst1 := Int.mul_le_mul_of_nonneg_right hc_abs hfall_nonneg
          have hc_nn : 0 ≤ (Int.natAbs (freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1)) : Int) := by omega
          have hst2 := Int.mul_le_mul_of_nonneg_left (hpow_d1_ub (u + 1) hj_le) hc_nn
          exact Int.le_trans hst1 hst2
        have hp := hsign 1 (Or.inl rfl)
        have hn := hsign (-1) (Or.inr rfl)
        omega
      have hterm1_ub :
          ((2 * d : Nat) : Int) * factZ (2 * K - 1) ≤
          4 * factZ (2 * K - 1) * powZ (M_nat : Int) (2 * K - 2) := by
        have h2d_le : ((2 * d : Nat) : Int) ≤ 4 * (M_nat : Int) := by omega
        have hM_le_pow : (M_nat : Int) ≤ powZ (M_nat : Int) (2 * K - 2) := by
          have hexp : 1 ≤ 2 * K - 2 := by omega
          simpa [powZ] using powZ_mono_exp (t := (M_nat : Int)) (by omega) hexp
        have h1 : ((2 * d : Nat) : Int) ≤ 4 * powZ (M_nat : Int) (2 * K - 2) := by omega
        have h2 := Int.mul_le_mul_of_nonneg_right h1 (Int.le_trans (by omega) (factZ_pos (2 * K - 1)))
        simpa [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using h2
      have ht1_nonneg : 0 ≤ ((2 * d : Nat) : Int) * factZ (2 * K - 1) :=
        Int.mul_nonneg (by omega) (Int.le_trans (by omega) (factZ_pos (2 * K - 1)))
      have hexpand : Coef * powZ (M_nat : Int) (2 * K - 2) =
          4 * factZ (2 * K - 1) * powZ (M_nat : Int) (2 * K - 2) +
            C_low * (powZ 2 (2 * K - 2) * powZ (M_nat : Int) (2 * K - 2)) := by
        unfold Coef
        rw [Int.add_mul, Int.mul_assoc C_low]
      have hrhs_ub :
          (Int.natAbs (((2 * d : Nat) : Int) * factZ (2 * K - 1) -
            sumRange (K - 1) (fun u =>
              freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1) *
                (fallZ d (u + 1) * fallZ (d + 1) (u + 1)))) : Int) ≤
          Coef * powZ (M_nat : Int) (2 * K - 2) := by
        have htri := natAbs_sub_ub (((2 * d : Nat) : Int) * factZ (2 * K - 1))
          (sumRange (K - 1) (fun u =>
            freeToClassical (wignerRay 1) (2 * (u + 1)) * scaleJ (u + 1) *
              (fallZ d (u + 1) * fallZ (d + 1) (u + 1))))
        rw [Int.natAbs_of_nonneg ht1_nonneg] at htri
        have hsum_add := Int.add_le_add hterm1_ub hsum_abs_ub
        rw [← hexpand] at hsum_add
        exact Int.le_trans htri hsum_add
      rw [hiso] at hlhs_lb
      have hcontra := Int.le_trans hlhs_lb hrhs_ub
      have hpow_split : powZ (M_nat : Int) (2 * K) =
          ((M_nat : Int) * (M_nat : Int)) * powZ (M_nat : Int) (2 * K - 2) := by
        have h2K_eq : 2 + (2 * K - 2) = 2 * K := by omega
        conv => lhs; rw [← h2K_eq]
        rw [powZ_add]
        simp [powZ, Int.mul_assoc]
      have hCoef_toNat : (Int.toNat Coef : Int) = Coef := Int.toNat_of_nonneg (by omega)
      have hM_gt_Coef : Coef < (M_nat : Int) * (M_nat : Int) := by
        have hM_gt : Coef < (M_nat : Int) := by omega
        have hM_ge1 : (1 : Int) ≤ (M_nat : Int) := by omega
        have := Int.mul_le_mul hM_ge1 (Int.le_refl (M_nat : Int)) (by omega) (by omega)
        omega
      have hpow_pos : 0 < powZ (M_nat : Int) (2 * K - 2) := by
        have := powZ_pos (a := (M_nat : Int)) (by omega) (2 * K - 2)
        omega
      have hstrict := Int.mul_lt_mul_of_pos_right hM_gt_Coef hpow_pos
      rw [← hpow_split] at hstrict
      omega

/-!
## 4. Master Refutation of Subclaim 1: Neither Direction Is a Low-Order Rational Combination
-/

theorem not_low_order_rational_combination (D : Nat) :
    (∃ n : Nat, 2 * D < n ∧
      ∀ P Q : Nat → Int, (∃ k, k ≤ D ∧ Q k ≠ 0) →
        ∃ t : Int, 1 ≤ t ∧ evalPolyZ D Q t ≠ 0 ∧
          classicalToFree (gaussRay t) n * evalPolyZ D Q t ≠ evalPolyZ D P t) ∧
    (∃ n : Nat, 2 * D < n ∧
      ∀ P Q : Nat → Int, (∃ k, k ≤ D ∧ Q k ≠ 0) →
        ∃ t : Int, 1 ≤ t ∧ evalPolyZ D Q t ≠ 0 ∧
          freeToClassical (wignerRay t) n * evalPolyZ D Q t ≠ evalPolyZ D P t) := by
  rcases gaussRay_classicalToFree_unbounded D with ⟨d1, hd1, ha1⟩
  rcases wignerRay_freeToClassical_unbounded D with ⟨d2, hd2, hb2⟩
  refine ⟨⟨2 * d1, by omega, ?_⟩, ⟨2 * d2, by omega, ?_⟩⟩
  · intro P Q hQ
    rcases monomial_not_low_degree_rational hd1 ha1 P Q hQ with ⟨t, ht1, hQt, hneq⟩
    refine ⟨t, ht1, hQt, ?_⟩
    rw [classicalToFree_gaussRay (2 * d1) t (by omega)]
    have hev : (2 * d1) % 2 = 0 := by omega
    have hdiv : (2 * d1) / 2 = d1 := by omega
    simp only [hev, hdiv, ite_true]
    exact hneq
  · intro P Q hQ
    rcases monomial_not_low_degree_rational hd2 hb2 P Q hQ with ⟨t, ht1, hQt, hneq⟩
    refine ⟨t, ht1, hQt, ?_⟩
    rw [freeToClassical_wignerRay (2 * d2) t (by omega)]
    have hev : (2 * d2) % 2 = 0 := by omega
    have hdiv : (2 * d2) / 2 = d2 := by omega
    simp only [hev, hdiv, ite_true]
    exact hneq

end Conjecture00000004763
