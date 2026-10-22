import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Conjecture5512

/-- Mean-field drift of tail coordinate k+1 for the two-choice model
    with unit exponential service rate and arrival load rho. -/
def drift (rho : ℝ) (q : ℕ → ℝ) (k : ℕ) : ℝ :=
  rho * (q k ^ 2 - q (k + 1) ^ 2) - (q (k + 1) - q (k + 2))

def FixedPoint (rho : ℝ) (q : ℕ → ℝ) : Prop :=
  0 < rho ∧ rho < 1 ∧ q 0 = 1 ∧
  (∀ k, 0 ≤ q k) ∧ (∀ k, q (k + 1) ≤ q k) ∧
  Tendsto q atTop (𝓝 0) ∧ ∀ k, drift rho q k = 0

/-- Every genuine finite power tail has a positive eventual polynomial
    lower envelope. This necessary condition is all that we refute. -/
def PolynomialTail (q : ℕ → ℝ) : Prop :=
  ∃ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
    ∀ n ≥ N, c ≤ (n : ℝ) ^ m * q n

def PowerTailConjecture : Prop :=
  ∀ (rho : ℝ) (q : ℕ → ℝ), FixedPoint rho q → PolynomialTail q

def tail : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 / 2) * tail n ^ 2

@[simp] theorem tail_zero : tail 0 = 1 := rfl
theorem tail_succ (n : ℕ) : tail (n + 1) = (1 / 2) * tail n ^ 2 := rfl

theorem tail_bounds (n : ℕ) : 0 < tail n ∧ tail n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [tail_succ]
    constructor
    · exact mul_pos (by norm_num) (sq_pos_of_pos ih.1)
    · nlinarith [sq_nonneg (tail n)]

theorem tail_decreasing (n : ℕ) : tail (n + 1) ≤ tail n := by
  rw [tail_succ]
  obtain ⟨hpos, hle⟩ := tail_bounds n
  nlinarith

theorem tail_geometric_bound (n : ℕ) : tail n ≤ (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [tail_succ, pow_succ (1 / 2 : ℝ) n]
    obtain ⟨hp, hle⟩ := tail_bounds n
    have hsq : tail n ^ 2 ≤ tail n := by nlinarith
    nlinarith

theorem tail_closed_form (n : ℕ) : tail n = (1 / 2 : ℝ) ^ (2 ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [tail_succ, ih, ← pow_mul, ← pow_succ']
    congr 1
    have h : 0 < 2 ^ n := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega

theorem weighted_tail_tendsto_zero (m : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ m * tail n) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg n) m) (le_of_lt (tail_bounds n).1)
  · intro n
    exact mul_le_mul_of_nonneg_left (tail_geometric_bound n)
      (pow_nonneg (Nat.cast_nonneg n) m)
  · exact tendsto_pow_const_mul_const_pow_of_lt_one m (by norm_num) (by norm_num)

theorem tail_tendsto_zero : Tendsto tail atTop (𝓝 0) := by
  simpa using weighted_tail_tendsto_zero 0

theorem tail_fixed_point : FixedPoint (1 / 2) tail := by
  refine ⟨by norm_num, by norm_num, rfl, fun n => le_of_lt (tail_bounds n).1,
    tail_decreasing, tail_tendsto_zero, ?_⟩
  intro k
  simp only [drift, show k + 2 = (k + 1) + 1 by omega, tail_succ]
  ring

theorem fixed_point_recurrence {rho : ℝ} {q : ℕ → ℝ} (h : FixedPoint rho q)
    (n : ℕ) : q (n + 1) = rho * q n ^ 2 := by
  obtain ⟨_, _, _, _, _, hlim, hdrift⟩ := h
  let flux := fun k => rho * q k ^ 2 - q (k + 1)
  have hstep (k : ℕ) : flux (k + 1) = flux k := by
    have := hdrift k
    dsimp [flux]
    simp only [drift, show k + 2 = (k + 1) + 1 by omega] at this
    linarith
  have hconst (k : ℕ) : flux k = flux 0 := by
    induction k with
    | zero => rfl
    | succ k ih => exact (hstep k).trans ih
  have hf : Tendsto flux atTop (𝓝 0) := by
    have hshift : Tendsto (fun k => q (k + 1)) atTop (𝓝 0) :=
      hlim.comp (tendsto_add_atTop_nat 1)
    convert (tendsto_const_nhds.mul (hlim.pow 2)).sub hshift using 1; simp
  have hc : Tendsto flux atTop (𝓝 (flux 0)) :=
    tendsto_const_nhds.congr (fun k => (hconst k).symm)
  have hzero : flux 0 = 0 := tendsto_nhds_unique hc hf
  have hn := (hconst n).trans hzero
  dsimp [flux] at hn
  linarith

theorem fixed_point_unique {q : ℕ → ℝ} (hq : FixedPoint (1 / 2) q) : q = tail := by
  funext n
  induction n with
  | zero => exact hq.2.2.1
  | succ n ih => rw [fixed_point_recurrence hq, ih, tail_succ]

def mass (n : ℕ) : ℝ := tail n - tail (n + 1)

theorem mass_nonnegative (n : ℕ) : 0 ≤ mass n := sub_nonneg.mpr (tail_decreasing n)

theorem mass_partial_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, mass k) = 1 - tail n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; unfold mass; ring

theorem mass_hasSum : HasSum mass 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg mass_nonnegative 1).mpr
  simp only [mass_partial_sum]
  convert tendsto_const_nhds.sub tail_tendsto_zero using 1; simp

theorem mass_shift_partial_sum (n k : ℕ) :
    (∑ j ∈ Finset.range k, mass (n + j)) = tail n - tail (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold mass
    rw [show n + (k + 1) = n + k + 1 by omega]
    ring

/-- The proposed tail is exactly the survival tail of the normalized mass. -/
theorem tail_is_survival (n : ℕ) : HasSum (fun k => mass (n + k)) (tail n) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => mass_nonnegative (n + k)) _).mpr
  simp only [mass_shift_partial_sum]
  have htail : Tendsto (fun k => tail (n + k)) atTop (𝓝 0) := by
    simpa [Nat.add_comm] using tail_tendsto_zero.comp (tendsto_add_atTop_nat n)
  convert tendsto_const_nhds.sub htail using 1; simp

theorem no_polynomial_tail : ¬ PolynomialTail tail := by
  rintro ⟨m, c, hc, N, hN⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ m * tail n < c :=
    (weighted_tail_tendsto_zero m).eventually (gt_mem_nhds hc)
  obtain ⟨n, hnN, hn⟩ := (hsmall.and (eventually_ge_atTop N)).exists
  exact (not_lt_of_ge (hN n hn)) hnN

theorem not_power_tail_conjecture : ¬ PowerTailConjecture := by
  intro h
  exact no_polynomial_tail (h (1 / 2) tail tail_fixed_point)

/-- The exact family at fixed load one half, with arbitrary selection count. -/
def tailD (d : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (1 / 2) * tailD d k ^ d

def driftD (d : ℕ) (rho : ℝ) (q : ℕ → ℝ) (k : ℕ) : ℝ :=
  rho * (q k ^ d - q (k + 1) ^ d) - (q (k + 1) - q (k + 2))

theorem tailD_bounds (d k : ℕ) : 0 < tailD d k ∧ tailD d k ≤ 1 := by
  induction k with
  | zero => simp [tailD]
  | succ k ih =>
    change 0 < (1 / 2 : ℝ) * tailD d k ^ d ∧ (1 / 2 : ℝ) * tailD d k ^ d ≤ 1
    constructor
    · exact mul_pos (by norm_num) (pow_pos ih.1 d)
    · have := pow_le_one₀ (le_of_lt ih.1) ih.2 (n := d)
      linarith

theorem unit_pow_le_self {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) {d : ℕ}
    (hd : 1 ≤ d) : x ^ d ≤ x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  rw [pow_succ]
  simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hx hx1 (n := k)) hx

theorem tailD_decreasing {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    tailD d (k + 1) ≤ tailD d k := by
  change (1 / 2 : ℝ) * tailD d k ^ d ≤ tailD d k
  have h := unit_pow_le_self (le_of_lt (tailD_bounds d k).1) (tailD_bounds d k).2 hd
  have hp := pow_nonneg (le_of_lt (tailD_bounds d k).1) d
  linarith

theorem tailD_geometric_bound {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    tailD d k ≤ (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp [tailD]
  | succ k ih =>
    change (1 / 2 : ℝ) * tailD d k ^ d ≤ (1 / 2 : ℝ) ^ (k + 1)
    rw [pow_succ]
    have h := unit_pow_le_self (le_of_lt (tailD_bounds d k).1) (tailD_bounds d k).2 hd
    linarith

theorem tailD_tendsto_zero {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (tailD d) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => le_of_lt (tailD_bounds d k).1) (tailD_geometric_bound hd)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem tailD_drift_zero (d k : ℕ) : driftD d (1 / 2) (tailD d) k = 0 := by
  simp only [driftD, show k + 2 = (k + 1) + 1 by omega, tailD]
  ring

def massD (d k : ℕ) : ℝ := tailD d k - tailD d (k + 1)

theorem massD_nonnegative {d : ℕ} (hd : 1 ≤ d) (k : ℕ) : 0 ≤ massD d k :=
  sub_nonneg.mpr (tailD_decreasing hd k)

theorem massD_shift_partial_sum (d n k : ℕ) :
    (∑ j ∈ Finset.range k, massD d (n + j)) = tailD d n - tailD d (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold massD
    rw [show n + (k + 1) = n + k + 1 by omega]
    ring

theorem tailD_is_survival {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    HasSum (fun k => massD d (n + k)) (tailD d n) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => massD_nonnegative hd (n + k)) _).mpr
  simp only [massD_shift_partial_sum]
  have htail : Tendsto (fun k => tailD d (n + k)) atTop (𝓝 0) := by
    simpa [Nat.add_comm] using (tailD_tendsto_zero hd).comp (tendsto_add_atTop_nat n)
  convert tendsto_const_nhds.sub htail using 1; simp

theorem massD_hasSum {d : ℕ} (hd : 1 ≤ d) : HasSum (massD d) 1 := by
  simpa [tailD] using tailD_is_survival hd 0

def DChoiceFixedPoint (d : ℕ) (q : ℕ → ℝ) : Prop :=
  q 0 = 1 ∧ (∀ k, 0 < q k ∧ q k ≤ 1) ∧
  (∀ k, q (k + 1) ≤ q k) ∧ Tendsto q atTop (𝓝 0) ∧
  (∀ k, driftD d (1 / 2) q k = 0) ∧
  HasSum (fun k => q k - q (k + 1)) 1 ∧
  ∀ n, HasSum (fun k => q (n + k) - q (n + k + 1)) (q n)

theorem tailD_fixed_point {d : ℕ} (hd : 1 ≤ d) : DChoiceFixedPoint d (tailD d) := by
  exact ⟨rfl, tailD_bounds d, tailD_decreasing hd, tailD_tendsto_zero hd,
    tailD_drift_zero d, massD_hasSum hd, tailD_is_survival hd⟩

theorem tailD_at_two (d : ℕ) : tailD d 2 = (1 / 2 : ℝ) ^ (d + 1) := by
  simp [tailD, pow_succ, mul_comm]

theorem selection_count_weighted_tendsto_zero (m : ℕ) :
    Tendsto (fun d : ℕ => (d : ℝ) ^ m * tailD d 2) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_lt_one m
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)
  simpa [tailD_at_two, pow_succ, mul_assoc] using h

theorem no_selection_count_power_tail : ¬ PolynomialTail (fun d => tailD d 2) := by
  rintro ⟨m, c, hc, N, hN⟩
  have hsmall : ∀ᶠ d : ℕ in atTop, (d : ℝ) ^ m * tailD d 2 < c :=
    (selection_count_weighted_tendsto_zero m).eventually (gt_mem_nhds hc)
  obtain ⟨d, hdc, hdN⟩ := (hsmall.and (eventually_ge_atTop N)).exists
  exact (not_lt_of_ge (hN d hdN)) hdc

#print axioms tail_fixed_point
#print axioms fixed_point_unique
#print axioms tail_closed_form
#print axioms mass_hasSum
#print axioms tail_is_survival
#print axioms weighted_tail_tendsto_zero
#print axioms not_power_tail_conjecture
#print axioms tailD_fixed_point
#print axioms no_selection_count_power_tail

end Conjecture5512
