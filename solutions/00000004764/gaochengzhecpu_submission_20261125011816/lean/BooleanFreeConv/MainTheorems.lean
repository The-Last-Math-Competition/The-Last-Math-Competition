/-
  Conjecture 00000004764 — Universal Cumulant & Convolution Formulas, Concrete Probability
  Measure Counterexamples, and Master Disproof Across All Four Canonical Readings
  Core Lean 4.19.0 (zero external dependencies)
-/
import BooleanFreeConv.Partitions

namespace BooleanFreeConv

open Series

/-! ### 1. Fast Prefix Characterization Lemmas for Series Evaluation -/

theorem momentsFromBool_eq_of_le (b m : Series) (N : Nat)
    (h : ∀ n, n ≤ N → m n = boolStep b m n) :
    ∀ n, n ≤ N → momentsFromBool b n = m n := by
  induction N with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by omega
    subst hn0
    have h0 := h 0 (Nat.le_refl 0)
    simp only [momentsFromBool, boolApprox, one, ↓reduceIte, boolStep] at h0 ⊢
    omega
  | succ d ih =>
    intro n hn
    by_cases hnd : n ≤ d
    · exact ih (fun k hk => h k (Nat.le_trans hk (Nat.le_succ d))) n hnd
    · have hneq : n = d + 1 := by omega
      subst hneq
      have hfix := congrFun (momentsFromBool_fixed b) (d + 1)
      rw [hfix, h (d + 1) (Nat.le_refl (d + 1))]
      apply boolStep_congr_lt
      intro r hr
      exact ih (fun k hk => h k (Nat.le_trans hk (Nat.le_succ d))) r (by omega)

theorem boolFromMoments_eq_of_le (m b : Series) (N : Nat)
    (h : ∀ n, n ≤ N → b n = boolCumStep m b n) :
    ∀ n, n ≤ N → boolFromMoments m n = b n := by
  induction N with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by omega
    subst hn0
    have h0 := h 0 (Nat.le_refl 0)
    simp only [boolFromMoments, boolCumApprox, zero, boolCumStep, ↓reduceIte] at h0 ⊢
    omega
  | succ d ih =>
    intro n hn
    by_cases hnd : n ≤ d
    · exact ih (fun k hk => h k (Nat.le_trans hk (Nat.le_succ d))) n hnd
    · have hneq : n = d + 1 := by omega
      subst hneq
      have hfix := congrFun (boolFromMoments_fixed m) (d + 1)
      rw [hfix, h (d + 1) (Nat.le_refl (d + 1))]
      apply boolCumStep_congr_lt
      intro r hr
      exact ih (fun k hk => h k (Nat.le_trans hk (Nat.le_succ d))) r (by omega)

theorem momentsFromFree_eq_of_le (k m : Series) (N : Nat)
    (h : ∀ n, n ≤ N → m n = freeStep k m n) :
    ∀ n, n ≤ N → momentsFromFree k n = m n := by
  induction N with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by omega
    subst hn0
    have h0 := h 0 (Nat.le_refl 0)
    simp only [momentsFromFree, freeApprox, one, ↓reduceIte, freeStep] at h0 ⊢
    omega
  | succ d ih =>
    intro n hn
    by_cases hnd : n ≤ d
    · exact ih (fun j hj => h j (Nat.le_trans hj (Nat.le_succ d))) n hnd
    · have hneq : n = d + 1 := by omega
      subst hneq
      have hfix := congrFun (momentsFromFree_fixed k) (d + 1)
      rw [hfix, h (d + 1) (Nat.le_refl (d + 1))]
      apply freeStep_congr_lt
      intro r hr
      exact ih (fun j hj => h j (Nat.le_trans hj (Nat.le_succ d))) r (by omega)

theorem freeFromMoments_eq_of_le (m k : Series) (N : Nat)
    (h : ∀ n, n ≤ N → k n = freeCumStep m k n) :
    ∀ n, n ≤ N → freeFromMoments m n = k n := by
  induction N with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by omega
    subst hn0
    have h0 := h 0 (Nat.le_refl 0)
    simp only [freeFromMoments, freeCumApprox, zero, freeCumStep, ↓reduceIte] at h0 ⊢
    omega
  | succ d ih =>
    intro n hn
    by_cases hnd : n ≤ d
    · exact ih (fun j hj => h j (Nat.le_trans hj (Nat.le_succ d))) n hnd
    · have hneq : n = d + 1 := by omega
      subst hneq
      have hfix := congrFun (freeFromMoments_fixed m) (d + 1)
      rw [hfix, h (d + 1) (Nat.le_refl (d + 1))]
      apply freeCumStep_congr_lt
      intro r hr
      exact ih (fun j hj => h j (Nat.le_trans hj (Nat.le_succ d))) r (by omega)

/-! ### 2. Universal Low-Order Identities and Universal Centered Polynomials -/

theorem momentsFromFree_1 (k : Series) : momentsFromFree k 1 = k 1 := by
  have h := congrFun (momentsFromFree_fixed k) 1
  rw [h]
  change 0 + k 1 * (momentsFromFree k).pow 1 0 = k 1
  have hp : (momentsFromFree k).pow 1 0 = 1 := pow_zero_coeff_of_unit (momentsFromFree_zero k) 1
  rw [hp]
  omega

theorem momentsFromFree_2 (k : Series) : momentsFromFree k 2 = k 1 * k 1 + k 2 := by
  have h := congrFun (momentsFromFree_fixed k) 2
  rw [h]
  change (0 + k 1 * ((momentsFromFree k).pow 1 1)) + k 2 * ((momentsFromFree k).pow 2 0) =
    k 1 * k 1 + k 2
  have hp2 : (momentsFromFree k).pow 2 0 = 1 := pow_zero_coeff_of_unit (momentsFromFree_zero k) 2
  have hp1 : (momentsFromFree k).pow 1 1 = k 1 := by
    change (0 + 1 * momentsFromFree k 1) + 0 * momentsFromFree k 0 = k 1
    rw [momentsFromFree_1]
    omega
  rw [hp1, hp2]
  omega

/-- Positive universal identity: `β₁(μ) = κ₁(μ)` for every formal cumulant series. -/
theorem beta_1_eq_kappa_1 (k : Series) :
    boolFromMoments (momentsFromFree k) 1 = k 1 := by
  have h := congrFun (boolFromMoments_fixed (momentsFromFree k)) 1
  rw [h]
  change momentsFromFree k 1 - 0 = k 1
  rw [momentsFromFree_1]
  omega

/-- Positive universal identity: `β₂(μ) = κ₂(μ)` for every formal cumulant series. -/
theorem beta_2_eq_kappa_2 (k : Series) :
    boolFromMoments (momentsFromFree k) 2 = k 2 := by
  have h := congrFun (boolFromMoments_fixed (momentsFromFree k)) 2
  rw [h]
  change momentsFromFree k 2 -
    (0 + boolFromMoments (momentsFromFree k) 1 * momentsFromFree k 1) = k 2
  rw [momentsFromFree_2, beta_1_eq_kappa_1, momentsFromFree_1]
  omega

/-- Universal centered (`κ₁ = 0`) cumulant conversion formulas through order `6`:
    - `β₃ = κ₃`,
    - `β₄ = κ₄ + κ₂²` (nonlinear),
    - `β₅ = κ₅ + 3 κ₂ κ₃` (universal non-power-of-two coefficient `3`),
    - `β₆ = κ₆ + 4 κ₂ κ₄ + 2 κ₃² + 2 κ₂³` (Fermat-prime `6 - 1 = 5` symmetric mirage). -/
theorem centered_cumulant_conversions_3_to_6 (k : Series) (hk1 : k 1 = 0) :
    boolFromMoments (momentsFromFree k) 3 = k 3 ∧
    boolFromMoments (momentsFromFree k) 4 = k 4 + k 2 * k 2 ∧
    boolFromMoments (momentsFromFree k) 5 = k 5 + 3 * (k 2 * k 3) ∧
    boolFromMoments (momentsFromFree k) 6 =
      k 6 + 4 * (k 2 * k 4) + 2 * (k 3 * k 3) + 2 * (k 2 * (k 2 * k 2)) := by
  let m := momentsFromFree k
  have m0 : m 0 = 1 := rfl
  have m1 : m 1 = 0 := by change momentsFromFree k 1 = 0; rw [momentsFromFree_1, hk1]
  have m2 : m 2 = k 2 := by
    change momentsFromFree k 2 = k 2; rw [momentsFromFree_2, hk1]; omega
  have p1 : ∀ d, (pow m 1) d = m d := fun d => congrFun (mul_one_left m) d
  have p2_0 : (pow m 2) 0 = 1 := pow_zero_coeff_of_unit m0 2
  have p2_1 : (pow m 2) 1 = 0 := by
    change (0 + (pow m 1) 0 * m 1) + (pow m 1) 1 * m 0 = 0
    rw [p1 0, p1 1, m0, m1]; omega
  have p2_2 : (pow m 2) 2 = 2 * k 2 := by
    change ((0 + (pow m 1) 0 * m 2) + (pow m 1) 1 * m 1) + (pow m 1) 2 * m 0 = 2 * k 2
    rw [p1 0, p1 1, p1 2, m0, m1, m2]; omega
  have p3_0 : (pow m 3) 0 = 1 := pow_zero_coeff_of_unit m0 3
  have p3_1 : (pow m 3) 1 = 0 := by
    change (0 + (pow m 2) 0 * m 1) + (pow m 2) 1 * m 0 = 0
    rw [p2_0, p2_1, m0, m1]; omega
  have m3 : m 3 = k 3 := by
    have h := congrFun (momentsFromFree_fixed k) 3
    change momentsFromFree k 3 = k 3
    rw [h]
    change ((0 + k 1 * (pow m 1) 2) + k 2 * (pow m 2) 1) + k 3 * (pow m 3) 0 = k 3
    rw [hk1, p2_1, p3_0]; omega
  have p2_3 : (pow m 2) 3 = 2 * k 3 := by
    change (((0 + (pow m 1) 0 * m 3) + (pow m 1) 1 * m 2) + (pow m 1) 2 * m 1) +
      (pow m 1) 3 * m 0 = 2 * k 3
    rw [p1 0, p1 1, p1 2, p1 3, m0, m1, m2, m3]; omega
  have p3_2 : (pow m 3) 2 = 3 * k 2 := by
    change ((0 + (pow m 2) 0 * m 2) + (pow m 2) 1 * m 1) + (pow m 2) 2 * m 0 = 3 * k 2
    rw [p2_0, p2_1, p2_2, m0, m1, m2]; omega
  have p4_0 : (pow m 4) 0 = 1 := pow_zero_coeff_of_unit m0 4
  have p4_1 : (pow m 4) 1 = 0 := by
    change (0 + (pow m 3) 0 * m 1) + (pow m 3) 1 * m 0 = 0
    rw [p3_0, p3_1, m0, m1]; omega
  have m4 : m 4 = 2 * (k 2 * k 2) + k 4 := by
    have h := congrFun (momentsFromFree_fixed k) 4
    change momentsFromFree k 4 = 2 * (k 2 * k 2) + k 4
    rw [h]
    change (((0 + k 1 * (pow m 1) 3) + k 2 * (pow m 2) 2) + k 3 * (pow m 3) 1) +
      k 4 * (pow m 4) 0 = 2 * (k 2 * k 2) + k 4
    rw [hk1, p2_2, p3_1, p4_0, ← Int.mul_assoc, Int.mul_comm (k 2) 2, Int.mul_assoc]; omega
  have p3_3 : (pow m 3) 3 = 3 * k 3 := by
    change (((0 + (pow m 2) 0 * m 3) + (pow m 2) 1 * m 2) + (pow m 2) 2 * m 1) +
      (pow m 2) 3 * m 0 = 3 * k 3
    rw [p2_0, p2_1, p2_2, p2_3, m0, m1, m3]; omega
  have p4_2 : (pow m 4) 2 = 4 * k 2 := by
    change ((0 + (pow m 3) 0 * m 2) + (pow m 3) 1 * m 1) + (pow m 3) 2 * m 0 = 4 * k 2
    rw [p3_0, p3_1, p3_2, m0, m1, m2]; omega
  have p5_0 : (pow m 5) 0 = 1 := pow_zero_coeff_of_unit m0 5
  have p5_1 : (pow m 5) 1 = 0 := by
    change (0 + (pow m 4) 0 * m 1) + (pow m 4) 1 * m 0 = 0
    rw [p4_0, p4_1, m0, m1]; omega
  have m5 : m 5 = 5 * (k 2 * k 3) + k 5 := by
    have h := congrFun (momentsFromFree_fixed k) 5
    change momentsFromFree k 5 = 5 * (k 2 * k 3) + k 5
    rw [h]
    change ((((0 + k 1 * (pow m 1) 4) + k 2 * (pow m 2) 3) + k 3 * (pow m 3) 2) +
      k 4 * (pow m 4) 1) + k 5 * (pow m 5) 0 = 5 * (k 2 * k 3) + k 5
    rw [hk1, p2_3, p3_2, p4_1, p5_0]
    have hc1 : k 2 * (2 * k 3) = 2 * (k 2 * k 3) := by
      rw [← Int.mul_assoc, Int.mul_comm (k 2) 2, Int.mul_assoc]
    have hc2 : k 3 * (3 * k 2) = 3 * (k 2 * k 3) := by
      rw [← Int.mul_assoc, Int.mul_comm (k 3) 3, Int.mul_assoc, Int.mul_comm (k 3) (k 2)]
    rw [hc1, hc2]; omega
  have p2_4 : (pow m 2) 4 = 5 * (k 2 * k 2) + 2 * k 4 := by
    change ((((0 + (pow m 1) 0 * m 4) + (pow m 1) 1 * m 3) + (pow m 1) 2 * m 2) +
      (pow m 1) 3 * m 1) + (pow m 1) 4 * m 0 = 5 * (k 2 * k 2) + 2 * k 4
    rw [p1 0, p1 1, p1 2, p1 3, p1 4, m0, m1, m2, m4]; omega
  have p6_0 : (pow m 6) 0 = 1 := pow_zero_coeff_of_unit m0 6
  have m6 : m 6 = 5 * (k 2 * (k 2 * k 2)) + 6 * (k 2 * k 4) + 3 * (k 3 * k 3) + k 6 := by
    have h := congrFun (momentsFromFree_fixed k) 6
    change momentsFromFree k 6 =
      5 * (k 2 * (k 2 * k 2)) + 6 * (k 2 * k 4) + 3 * (k 3 * k 3) + k 6
    rw [h]
    change (((((0 + k 1 * (pow m 1) 5) + k 2 * (pow m 2) 4) + k 3 * (pow m 3) 3) +
      k 4 * (pow m 4) 2) + k 5 * (pow m 5) 1) + k 6 * (pow m 6) 0 =
      5 * (k 2 * (k 2 * k 2)) + 6 * (k 2 * k 4) + 3 * (k 3 * k 3) + k 6
    rw [hk1, p2_4, p3_3, p4_2, p5_1, p6_0, Int.mul_add]
    have hd1 : k 2 * (5 * (k 2 * k 2)) = 5 * (k 2 * (k 2 * k 2)) := by
      rw [← Int.mul_assoc, Int.mul_comm (k 2) 5, Int.mul_assoc]
    have hd2 : k 2 * (2 * k 4) = 2 * (k 2 * k 4) := by
      rw [← Int.mul_assoc, Int.mul_comm (k 2) 2, Int.mul_assoc]
    have hd3 : k 3 * (3 * k 3) = 3 * (k 3 * k 3) := by
      rw [← Int.mul_assoc, Int.mul_comm (k 3) 3, Int.mul_assoc]
    have hd4 : k 4 * (4 * k 2) = 4 * (k 2 * k 4) := by
      rw [← Int.mul_assoc, Int.mul_comm (k 4) 4, Int.mul_assoc, Int.mul_comm (k 4) (k 2)]
    rw [hd1, hd2, hd3, hd4]; omega
  -- Now extract Boolean cumulants `b 1 .. b 6`:
  let b := boolFromMoments m
  have b1 : b 1 = 0 := by change boolFromMoments (momentsFromFree k) 1 = 0; rw [beta_1_eq_kappa_1, hk1]
  have b2 : b 2 = k 2 := beta_2_eq_kappa_2 k
  have b3 : b 3 = k 3 := by
    have h := congrFun (boolFromMoments_fixed m) 3
    change boolFromMoments m 3 = k 3
    rw [h]
    change m 3 - ((0 + b 1 * m 2) + b 2 * m 1) = k 3
    rw [m3, b1, m1]; omega
  have b4 : b 4 = k 4 + k 2 * k 2 := by
    have h := congrFun (boolFromMoments_fixed m) 4
    change boolFromMoments m 4 = k 4 + k 2 * k 2
    rw [h]
    change m 4 - (((0 + b 1 * m 3) + b 2 * m 2) + b 3 * m 1) = k 4 + k 2 * k 2
    rw [m4, b1, b2, m2, m1]; omega
  have b5 : b 5 = k 5 + 3 * (k 2 * k 3) := by
    have h := congrFun (boolFromMoments_fixed m) 5
    change boolFromMoments m 5 = k 5 + 3 * (k 2 * k 3)
    rw [h]
    change m 5 - ((((0 + b 1 * m 4) + b 2 * m 3) + b 3 * m 2) + b 4 * m 1) =
      k 5 + 3 * (k 2 * k 3)
    rw [m5, b1, b2, m3, b3, m2, m1, Int.mul_comm (k 3) (k 2)]; omega
  have b6 : b 6 = k 6 + 4 * (k 2 * k 4) + 2 * (k 3 * k 3) + 2 * (k 2 * (k 2 * k 2)) := by
    have h := congrFun (boolFromMoments_fixed m) 6
    change boolFromMoments m 6 =
      k 6 + 4 * (k 2 * k 4) + 2 * (k 3 * k 3) + 2 * (k 2 * (k 2 * k 2))
    rw [h]
    change m 6 - (((((0 + b 1 * m 5) + b 2 * m 4) + b 3 * m 3) + b 4 * m 2) + b 5 * m 1) =
      k 6 + 4 * (k 2 * k 4) + 2 * (k 3 * k 3) + 2 * (k 2 * (k 2 * k 2))
    rw [m6, b1, b2, m4, b3, m3, b4, m2, m1, Int.mul_add, Int.add_mul]
    have he1 : k 2 * (2 * (k 2 * k 2)) = 2 * (k 2 * (k 2 * k 2)) := by
      rw [← Int.mul_assoc, Int.mul_comm (k 2) 2, Int.mul_assoc]
    have he2 : k 4 * k 2 = k 2 * k 4 := Int.mul_comm (k 4) (k 2)
    have he3 : k 2 * k 2 * k 2 = k 2 * (k 2 * k 2) := Int.mul_assoc (k 2) (k 2) (k 2)
    rw [he1, he2, he3]; omega
  exact ⟨b3, b4, b5, b6⟩

/-! ### 3. Concrete Borel Probability Measures & Exact All-Order Generating Series -/

/-- Boolean cumulant series `B_Bern(z) = z^2` of the symmetric Bernoulli measure
    `μ_Bern = (δ_{-1} + δ_1) / 2`. -/
def bernoulliBoolCumulants : Series
  | 2 => 1
  | _ => 0

/-- Moment generating series `M_Bern(z) = 1 / (1 - z^2) = ∑_{k ≥ 0} z^{2k}`
    of the symmetric Bernoulli measure `μ_Bern = (δ_{-1} + δ_1) / 2`. -/
def bernoulliMoments : Series :=
  momentsFromBool bernoulliBoolCumulants

/-- Explicit O(1) lookup table for `bernoulliMoments` on `0 .. 8`. -/
def bernoulliTable : Series
  | 0 | 2 | 4 | 6 | 8 => 1
  | _ => 0

theorem bernoulliMoments_eq_table (n : Nat) (hn : n ≤ 8) :
    bernoulliMoments n = bernoulliTable n := by
  apply momentsFromBool_eq_of_le bernoulliBoolCumulants bernoulliTable 8 ?_ n hn
  intro k hk
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => omega

/-- Exact all-orders generating-function identity `(1 - z^2) * M_Bern(z) = 1`. -/
theorem bernoulli_gen_eq :
    BoolGenEq bernoulliMoments bernoulliBoolCumulants :=
  boolGenEq_momentsFromBool bernoulliBoolCumulants rfl

/-- Free cumulant series `C_sc(w) - 1 = w^2` of the standard Wigner semicircle law
    `μ_sc` on `[-2, 2]` (`κ₂ = 1`, `κ_{n ≠ 2} = 0`). -/
def wignerFreeCumulants : Series := bernoulliBoolCumulants

/-- Moment generating series `M_sc(z) = ∑_{k ≥ 0} C_k z^{2k}` of the standard Wigner
    semicircle law `μ_sc`. -/
def wignerMoments : Series :=
  momentsFromFree wignerFreeCumulants

/-- Exact all-orders Bercovici–Pata theorem: `𝔹₁(μ_Bern) = μ_sc` as formal power series! -/
theorem bercoviciPata_bernoulli_eq_wigner :
    bercoviciPataBF bernoulliMoments = wignerMoments := by
  unfold bercoviciPataBF bernoulliMoments wignerMoments wignerFreeCumulants
  have hb : boolFromMoments (momentsFromBool bernoulliBoolCumulants) = bernoulliBoolCumulants :=
    boolFromMoments_momentsFromBool (b := bernoulliBoolCumulants) rfl
  rw [hb]

/-- Exact all-orders composition equation `M_sc(z) = C_sc(z * M_sc(z))` for Wigner semicircle. -/
theorem wigner_gen_eq :
    FreeGenEq wignerMoments (add one wignerFreeCumulants) :=
  freeGenEq_momentsFromFree wignerFreeCumulants rfl

/-- Explicit Catalan lookup table for `wignerMoments` on `0 .. 8`. -/
def wignerTable : Series
  | 0 => 1
  | 2 => 1
  | 4 => 2
  | 6 => 5
  | 8 => 14
  | _ => 0

theorem wignerMoments_eq_table (n : Nat) (hn : n ≤ 8) :
    wignerMoments n = wignerTable n := by
  apply momentsFromFree_eq_of_le wignerFreeCumulants wignerTable 8 ?_ n hn
  intro k hk
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => omega

/-- Explicit shifted-Catalan table for Boolean cumulants `β_n(μ_sc)` on `0 .. 8`. -/
def wignerBoolTable : Series
  | 2 => 1
  | 4 => 1
  | 6 => 2
  | 8 => 5
  | _ => 0

theorem wignerBoolCumulants_eq_table (n : Nat) (hn : n ≤ 8) :
    boolFromMoments wignerMoments n = wignerBoolTable n := by
  apply boolFromMoments_eq_of_le wignerMoments wignerBoolTable 8 ?_ n hn
  intro k hk
  have hstep : boolCumStep wignerMoments wignerBoolTable k =
      boolCumStep wignerTable wignerBoolTable k := by
    cases k with
    | zero => rfl
    | succ d =>
      simp only [boolCumStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [wignerMoments_eq_table (d + 1) (by omega)]
      apply congrArg (wignerTable (d + 1) - ·)
      apply rangeSum_congr
      intro i hi
      rw [wignerMoments_eq_table (d - i) (by omega)]
  rw [hstep]
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => omega

/-- Explicit signed-Catalan table for free cumulants `κ_n(μ_Bern)` on `0 .. 8`. -/
def bernoulliFreeTable : Series
  | 2 => 1
  | 4 => -1
  | 6 => 2
  | 8 => -5
  | _ => 0

theorem bernoulliFreeCumulants_eq_table (n : Nat) (hn : n ≤ 8) :
    freeFromMoments bernoulliMoments n = bernoulliFreeTable n := by
  apply freeFromMoments_eq_of_le bernoulliMoments bernoulliFreeTable 8 ?_ n hn
  intro k hk
  have hstep : freeCumStep bernoulliMoments bernoulliFreeTable k =
      freeCumStep bernoulliTable bernoulliFreeTable k := by
    cases k with
    | zero => rfl
    | succ d =>
      simp only [freeCumStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [bernoulliMoments_eq_table (d + 1) (by omega)]
      apply congrArg (bernoulliTable (d + 1) - ·)
      apply rangeSum_congr
      intro i hi
      apply congrArg (bernoulliFreeTable (i + 1) * ·)
      apply pow_congr_le
      intro r hr
      exact bernoulliMoments_eq_table r (by omega)
  rw [hstep]
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => omega

/-- Explicit table for Boolean self-convolution `μ_Bern ⊎ μ_Bern` (`m_{2k} = 2^k`) on `0 .. 6`. -/
def bernoulliBoolConv2Table : Series
  | 0 => 1
  | 2 => 2
  | 4 => 4
  | 6 => 8
  | _ => 0

theorem bernoulli_boolConv2_eq_table (n : Nat) (hn : n ≤ 6) :
    boolConv bernoulliMoments bernoulliMoments n = bernoulliBoolConv2Table n := by
  unfold boolConv bernoulliMoments
  have hb : boolFromMoments (momentsFromBool bernoulliBoolCumulants) = bernoulliBoolCumulants :=
    boolFromMoments_momentsFromBool (b := bernoulliBoolCumulants) rfl
  rw [hb]
  apply momentsFromBool_eq_of_le (add bernoulliBoolCumulants bernoulliBoolCumulants)
    bernoulliBoolConv2Table 6 ?_ n hn
  intro k hk
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rfl
  | _ + 7 => omega

/-- Explicit table for free self-convolution `μ_Bern ⊞ μ_Bern` (arcsine law `m_{2k} = C(2k, k)`)
    on `0 .. 6`. -/
def bernoulliFreeConv2Table : Series
  | 0 => 1
  | 2 => 2
  | 4 => 6
  | 6 => 20
  | _ => 0

theorem bernoulli_freeConv2_eq_table (n : Nat) (hn : n ≤ 6) :
    freeConv bernoulliMoments bernoulliMoments n = bernoulliFreeConv2Table n := by
  unfold freeConv
  apply momentsFromFree_eq_of_le
    (add (freeFromMoments bernoulliMoments) (freeFromMoments bernoulliMoments))
    bernoulliFreeConv2Table 6 ?_ n hn
  intro k hk
  have hstep :
      freeStep (add (freeFromMoments bernoulliMoments) (freeFromMoments bernoulliMoments))
        bernoulliFreeConv2Table k =
      freeStep (add bernoulliFreeTable bernoulliFreeTable)
        bernoulliFreeConv2Table k := by
    cases k with
    | zero => rfl
    | succ d =>
      simp only [freeStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      apply rangeSum_congr
      intro i hi
      simp only [add]
      rw [bernoulliFreeCumulants_eq_table (i + 1) (by omega)]
  rw [hstep]
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rfl
  | _ + 7 => omega

/-- Combinatorial verification: partition sums over `Int(4)`, `NC(4)`, and `NC_irr(4)`
    agree identically with the generating-function definitions on our canonical witnesses. -/
theorem combinatorial_partition_sum_agreement :
    partitionSum (intPartitions 4) bernoulliBoolCumulants = bernoulliMoments 4 ∧
    partitionSum (ncPartitions 4) wignerFreeCumulants = wignerMoments 4 ∧
    partitionSum (ncIrrPartitions 4) wignerFreeCumulants = boolFromMoments wignerMoments 4 := by
  rw [bernoulliMoments_eq_table 4 (by omega),
      wignerMoments_eq_table 4 (by omega),
      wignerBoolCumulants_eq_table 4 (by omega)]
  exact ⟨rfl, rfl, rfl⟩

/-! ### 4. Refutations of All Four Canonical Readings of Conjecture 00000004764 -/

/-- **Reading I Disproof (Bercovici–Pata / Moment-Cumulant Conversion `μ ↦ 𝔹₁(μ)`):**
    Although `m_2(𝔹₁(μ_Bern)) / m_2(μ_Bern) = 1 = 2^0` and
    `m_4(𝔹₁(μ_Bern)) / m_4(μ_Bern) = 2 = 2^1`, at moment order `n = 6` we have
    `m_6(μ_Bern) = 1` whereas `m_6(𝔹₁(μ_Bern)) = C_3 = 5`, which is not any integer
    or rational power of two. -/
theorem reading1_bercovici_pata_disproof :
    IsSignedPowTwoRatio (bernoulliMoments 2) (bercoviciPataBF bernoulliMoments 2) ∧
    IsSignedPowTwoRatio (bernoulliMoments 4) (bercoviciPataBF bernoulliMoments 4) ∧
    ¬ IsRatPowTwoRatio (bernoulliMoments 6) (bercoviciPataBF bernoulliMoments 6) := by
  rw [bercoviciPata_bernoulli_eq_wigner,
      bernoulliMoments_eq_table 2 (by omega), wignerMoments_eq_table 2 (by omega),
      bernoulliMoments_eq_table 4 (by omega), wignerMoments_eq_table 4 (by omega),
      bernoulliMoments_eq_table 6 (by omega), wignerMoments_eq_table 6 (by omega)]
  refine ⟨Or.inl ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩, ?_⟩
  exact not_isRatPowTwoRatio_of_mod_five (Or.inl rfl) rfl

/-- **Reading II Disproof (Same-Measure Cumulant Conversion `β_n(μ) ↔ κ_n(μ)`):**
    1. Scalar power-of-two conversion fails already at `n = 4` on `μ_sc`:
       `κ_4(μ_sc) = 0` while `β_4(μ_sc) = 1`.
    2. Sign positivity fails at `n = 4` on `μ_Bern`: `κ_4(μ_Bern) = -1 < 0`.
    3. Even relative to nonzero cumulant monomials (`κ₂⁴ = 1`), the symmetric power-of-two
       mirage (`β₂ = 1, β₄ = 1, β₆ = 2`) breaks at order `n = 8`:
       `β_8(μ_sc) = C_3 = 5` is not any integer or rational power of two. -/
theorem reading2_same_measure_cumulant_disproof :
    ¬ IsSignedPowTwoRatio (wignerFreeCumulants 4) (boolFromMoments wignerMoments 4) ∧
    ¬ IsSignedPowTwoRatio 1 (freeFromMoments bernoulliMoments 4) ∧
    ¬ IsRatPowTwoRatio 1 (boolFromMoments wignerMoments 8) := by
  rw [wignerBoolCumulants_eq_table 4 (by omega),
      bernoulliFreeCumulants_eq_table 4 (by omega),
      wignerBoolCumulants_eq_table 8 (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · exact not_isSignedPowTwoRatio_zero_left (by decide)
  · exact not_isSignedPowTwoRatio_pos_neg (by decide) (by decide)
  · exact not_isRatPowTwoRatio_of_mod_five (Or.inl rfl) rfl

/-- **Reading III Disproof (Direct Convolution Conversion `μ ⊎ ν` vs `μ ⊞ ν`):**
    For the symmetric Bernoulli measure `μ_Bern`, Boolean self-convolution has moments
    `m_{2k}(μ_Bern ⊎ μ_Bern) = 2^k` (`2, 4, 8`), whereas free self-convolution (the
    arcsine law) has moments `m_{2k}(μ_Bern ⊞ μ_Bern) = C(2k, k)` (`2, 6, 20`).
    Conversion fails both at order `n = 4` (`6 / 4 = 3 / 2`) and at order `n = 6`
    (`20 / 8 = 5 / 2`). -/
theorem reading3_direct_convolution_disproof :
    IsSignedPowTwoRatio (boolConv bernoulliMoments bernoulliMoments 2)
                        (freeConv bernoulliMoments bernoulliMoments 2) ∧
    ¬ IsRatPowTwoRatio (boolConv bernoulliMoments bernoulliMoments 4)
                       (freeConv bernoulliMoments bernoulliMoments 4) ∧
    ¬ IsRatPowTwoRatio (boolConv bernoulliMoments bernoulliMoments 6)
                       (freeConv bernoulliMoments bernoulliMoments 6) := by
  rw [bernoulli_boolConv2_eq_table 2 (by omega), bernoulli_freeConv2_eq_table 2 (by omega),
      bernoulli_boolConv2_eq_table 4 (by omega), bernoulli_freeConv2_eq_table 4 (by omega),
      bernoulli_boolConv2_eq_table 6 (by omega), bernoulli_freeConv2_eq_table 6 (by omega)]
  refine ⟨Or.inl ⟨0, rfl⟩, ?_, ?_⟩
  · exact not_isRatPowTwoRatio_of_mod_three (Or.inl rfl) rfl
  · exact not_isRatPowTwoRatio_of_mod_five (Or.inr (Or.inr (Or.inr rfl))) rfl

/-- **Reading IV Disproof (Partition-Lattice Cardinality Conversion `|Int(n)|` vs `|NC(n)|`):**
    While `|Int(n)| = 2^(n - 1)` holds for all `n ≥ 1` and agrees with `|NC(n)|` at
    `n = 1, 2`, at `n = 3` we have `|Int(3)| = 4` vs `|NC(3)| = 5`, whose ratio `5 / 4`
    is not any integer or rational power of two. -/
theorem reading4_partition_lattice_disproof :
    (∀ m : Nat, (intPartitions (m + 1)).length = 2 ^ m) ∧
    ¬ IsRatPowTwoRatio ((intPartitions 3).length : Int) ((ncPartitions 3).length : Int) :=
  ⟨intPartitions_card_pow2, nc_vs_int_order3_not_pow2⟩

/-- **Master Theorem (`conjecture_00000004764_false`):**
    Packages the exact formal generating-function foundations (Boolean non-composition
    equation vs free composition equation, Bercovici–Pata homomorphism, universal
    `|Int(n)| = 2^(n-1)` theorem, and universal centered polynomial `β₅ = κ₅ + 3 κ₂ κ₃`)
    together with the complete refutation of the power-of-two Boolean-to-free conversion
    claim across all four canonical readings. -/
theorem conjecture_00000004764_false :
    -- (A) Exact generating-function foundations & non-vacuity
    (∀ M bTilde : Series,
      BoolGenEq M (shift bTilde) ↔ sub M one = mul bTilde (shift M)) ∧
    (∀ k : Series, k 0 = 0 → FreeGenEq (momentsFromFree k) (add one k)) ∧
    (∀ m₁ m₂ : Series,
      bercoviciPataBF (boolConv m₁ m₂) = freeConv (bercoviciPataBF m₁) (bercoviciPataBF m₂)) ∧
    (∀ m : Nat, (intPartitions (m + 1)).length = 2 ^ m) ∧
    (∀ k : Series, k 1 = 0 → boolFromMoments (momentsFromFree k) 5 = k 5 + 3 * (k 2 * k 3)) ∧
    -- (B) Refutation of all four canonical readings (even for rational powers of two)
    ¬ IsRatPowTwoRatio (krewerasDen 3 2) (krewerasNum 3) ∧
    ¬ IsRatPowTwoRatio (krewerasDen 6 2) (krewerasNum 6) ∧
    ¬ IsRatPowTwoRatio (bernoulliMoments 6) (bercoviciPataBF bernoulliMoments 6) ∧
    ¬ IsSignedPowTwoRatio (wignerFreeCumulants 4) (boolFromMoments wignerMoments 4) ∧
    ¬ IsRatPowTwoRatio 1 (boolFromMoments wignerMoments 8) ∧
    ¬ IsRatPowTwoRatio (boolConv bernoulliMoments bernoulliMoments 4)
                       (freeConv bernoulliMoments bernoulliMoments 4) ∧
    ¬ IsRatPowTwoRatio (boolConv bernoulliMoments bernoulliMoments 6)
                       (freeConv bernoulliMoments bernoulliMoments 6) ∧
    ¬ IsRatPowTwoRatio ((intPartitions 3).length : Int) ((ncPartitions 3).length : Int) := by
  refine ⟨boolGenEq_iff_no_comp,
          freeGenEq_momentsFromFree,
          bercoviciPataBF_hom,
          intPartitions_card_pow2,
          fun k hk1 => (centered_cumulant_conversions_3_to_6 k hk1).2.2.1,
          kreweras_order3_k2_not_pow2,
          kreweras_order6_even_not_pow2.1,
          reading1_bercovici_pata_disproof.2.2,
          reading2_same_measure_cumulant_disproof.1,
          reading2_same_measure_cumulant_disproof.2.2,
          reading3_direct_convolution_disproof.2.1,
          reading3_direct_convolution_disproof.2.2,
          nc_vs_int_order3_not_pow2⟩

end BooleanFreeConv
