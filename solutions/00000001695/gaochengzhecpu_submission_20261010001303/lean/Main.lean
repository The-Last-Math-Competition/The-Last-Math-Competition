import Mathlib.Data.Real.Irrational
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Conjecture1695

def BadlyApproximable (a : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ p : ℤ, ∀ q : ℕ, 0 < q → c / (q : ℝ) ^ 2 ≤ |a - p / q|

theorem sqrt_two_badly_approximable : BadlyApproximable (Real.sqrt 2) := by
  refine ⟨1 / 5, by norm_num, ?_⟩
  intro p q hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 2 < 2 := by nlinarith
  have hD : (2 * (q : ℤ) ^ 2 - p ^ 2) ≠ 0 := by
    intro h
    have hr : (2 : ℝ) * (q : ℝ) ^ 2 - (p : ℝ) ^ 2 = 0 := by exact_mod_cast h
    have hrat : ((p : ℝ) / q) ^ 2 = 2 := by
      field_simp
      nlinarith
    have hroots : Real.sqrt 2 = (p : ℝ) / q ∨ Real.sqrt 2 = -((p : ℝ) / q) :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (by linarith [hsq, hrat])
    rcases hroots with hp | hp
    · exact (irrational_iff_ne_rational _).mp irrational_sqrt_two p q (by simpa using hp)
    · exact (irrational_iff_ne_rational _).mp irrational_sqrt_two (-p) q
        (by simpa only [Int.cast_neg, Int.cast_natCast, neg_div] using hp)
  have hInt : (1 : ℝ) ≤ |2 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2| := by
    exact_mod_cast Int.one_le_abs hD
  by_cases hd : 1 ≤ |Real.sqrt 2 - (p : ℝ) / q|
  · have hsmall : (1 / 5 : ℝ) / (q : ℝ) ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hq0)).mpr
      nlinarith
    exact hsmall.trans hd
  · have hd' : |Real.sqrt 2 - (p : ℝ) / q| < 1 := lt_of_not_ge hd
    have hratio : |(p : ℝ) / q| < 3 := by
      have ht := abs_add_le ((p : ℝ) / q - Real.sqrt 2) (Real.sqrt 2)
      rw [sub_add_cancel, abs_sub_comm, abs_of_nonneg hs0] at ht
      linarith
    have hsum : |Real.sqrt 2 + (p : ℝ) / q| < 5 := by
      have ht := abs_add_le (Real.sqrt 2) ((p : ℝ) / q)
      rw [abs_of_nonneg hs0] at ht
      linarith
    have hfactor :
        |2 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2| =
          |Real.sqrt 2 - (p : ℝ) / q| * |Real.sqrt 2 + (p : ℝ) / q| * (q : ℝ) ^ 2 := by
      have hf : 2 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2 =
          (Real.sqrt 2 - (p : ℝ) / q) * (Real.sqrt 2 + (p : ℝ) / q) * (q : ℝ) ^ 2 := by
        calc
          2 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2 =
              (Real.sqrt 2) ^ 2 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2 := by rw [hsq]
          _ = _ := by field_simp; ring_nf; rw [hsq]
      rw [hf, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (q : ℝ))]
    rw [hfactor] at hInt
    apply (div_le_iff₀ (sq_pos_of_pos hq0)).mpr
    have hnonneg := abs_nonneg (Real.sqrt 2 - (p : ℝ) / q)
    nlinarith [mul_le_mul_of_nonneg_left hsum.le
      (mul_nonneg hnonneg (sq_nonneg (q : ℝ)))]

def rotation (x : UnitAddCircle) : UnitAddCircle := x + (Real.sqrt 2 : ℝ)

def observable (_ : UnitAddCircle) : ℝ := 1

theorem rotation_preserves_measure : MeasurePreserving rotation volume volume :=
  measurePreserving_add_right volume (Real.sqrt 2 : UnitAddCircle)

theorem phase_iterates (p : ℕ) (x : UnitAddCircle) :
    rotation^[p] x = x + p • (Real.sqrt 2 : UnitAddCircle) := by
  induction p with
  | zero => simp
  | succ p hp =>
    rw [Function.iterate_succ_apply', hp]
    simp [rotation, add_nsmul, add_assoc]

def primeAverage (N : ℕ) (x : UnitAddCircle) : ℝ :=
  (∑ p ∈ (N + 1).primesBelow, observable (rotation^[p] x)) / N

theorem actual_average (N : ℕ) (x : UnitAddCircle) :
    primeAverage N x = (N.primeCounting : ℝ) / N := by
  simp [primeAverage, observable, Nat.primesBelow_card_eq_primeCounting', Nat.primeCounting]

theorem actual_integral : (∫ x : UnitAddCircle, observable x) = 1 := by
  simp [observable, integral_const, Measure.real, UnitAddCircle.measure_univ]

/-- The elementary sieve with a=2; no prime-number theorem is used. -/
theorem prime_count_bound (N : ℕ) (hN : 2 ≤ N) :
    2 * N.primeCounting ≤ N + 4 := by
  have h := Nat.primeCounting'_add_le (a := 2) (k := 3) (by omega) (by omega) (N - 2)
  have hthree : Nat.primeCounting' 3 = 1 := by decide
  have htot : Nat.totient 2 = 1 := by decide
  rw [hthree, htot] at h
  have heq : 3 + (N - 2) = N + 1 := by omega
  rw [heq] at h
  change N.primeCounting ≤ _ at h
  omega

theorem error_lower_bound (N : ℕ) (hN : 16 ≤ N) (x : UnitAddCircle) :
    (1 / 4 : ℝ) ≤ |primeAverage N x - ∫ y : UnitAddCircle, observable y| := by
  rw [actual_average, actual_integral]
  have hcount : (2 : ℝ) * N.primeCounting ≤ N + 4 := by
    exact_mod_cast prime_count_bound N (by omega)
  have hNR : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (0 : ℝ) < N := by linarith
  have hratio : (N.primeCounting : ℝ) / N ≤ 3 / 4 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  rw [abs_of_nonpos (by linarith)]
  linarith

def claimedRate (C : ℝ) (N : ℕ) : ℝ :=
  C * (Real.log (Real.log N) / (Real.sqrt N * Real.log N))

theorem claimed_rate_le (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hN : 2 ≤ N) :
    claimedRate C N ≤ C / Real.sqrt N := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn0
  have hl : 0 < Real.log N := Real.log_pos hNR
  have hll := Real.log_le_self hl.le
  unfold claimedRate
  calc
    C * (Real.log (Real.log N) / (Real.sqrt N * Real.log N)) ≤
        C * (Real.log N / (Real.sqrt N * Real.log N)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hll (mul_nonneg hs.le hl.le)) hC
    _ = C / Real.sqrt N := by field_simp; ring

/-- Every nonnegative proposed constant fails at arbitrarily large N. -/
theorem arbitrarily_large_failure (C : ℝ) (hC : 0 ≤ C) (N₀ : ℕ) (x : UnitAddCircle) :
    ∃ N : ℕ, N₀ ≤ N ∧ 16 ≤ N ∧
      claimedRate C N < |primeAverage N x - ∫ y : UnitAddCircle, observable y| := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((4 * C + 1) ^ 2 + N₀ + 16)
  have hN₀nonneg : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have hN0 : N₀ ≤ N := by
    exact_mod_cast (by nlinarith [sq_nonneg (4 * C + 1)] : (N₀ : ℝ) ≤ N)
  have hN16 : 16 ≤ N := by
    exact_mod_cast (by nlinarith [sq_nonneg (4 * C + 1)] : (16 : ℝ) ≤ N)
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hnpos
  have hsq : (4 * C) ^ 2 < (N : ℝ) := by nlinarith
  have hs : 4 * C < Real.sqrt N := (Real.lt_sqrt (by linarith)).mpr hsq
  have hsmall : C / Real.sqrt N < (1 / 4 : ℝ) := by
    apply (div_lt_iff₀ hspos).mpr
    linarith
  exact ⟨N, hN0, hN16, (claimed_rate_le C hC N (by omega)).trans_lt
    (hsmall.trans_le (error_lower_bound N hN16 x))⟩

theorem counterexample :
    BadlyApproximable (Real.sqrt 2) ∧
    MeasurePreserving rotation volume volume ∧
    ∀ C : ℝ, 0 ≤ C → ∀ N₀ : ℕ, ∀ x : UnitAddCircle,
      ∃ N : ℕ, N₀ ≤ N ∧ 16 ≤ N ∧
        claimedRate C N < |primeAverage N x - ∫ y : UnitAddCircle, observable y| :=
  ⟨sqrt_two_badly_approximable, rotation_preserves_measure, arbitrarily_large_failure⟩

#print axioms sqrt_two_badly_approximable
#print axioms counterexample

end Conjecture1695
