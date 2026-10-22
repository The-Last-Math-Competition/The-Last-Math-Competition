import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Eval.Defs

open scoped BigOperators
open Filter

namespace TLMC1042

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

noncomputable def affinePolynomial (a b : K) : Polynomial K :=
  Polynomial.C a * Polynomial.X + Polynomial.C b

omit [Fintype K] [DecidableEq K] in
theorem affine_eval (a b x : K) : (affinePolynomial K a b).eval x = a * x + b := by
  simp [affinePolynomial]

omit [Fintype K] [DecidableEq K] in
theorem affinePolynomial_injective : Function.Injective (fun ab : K × K =>
    affinePolynomial K ab.1 ab.2) := by
  intro ab cd h
  have h0 := congrArg (fun p : Polynomial K => p.coeff 0) h
  have h1 := congrArg (fun p : Polynomial K => p.coeff 1) h
  simp [affinePolynomial] at h0 h1
  exact Prod.ext h1 h0

omit [Fintype K] [DecidableEq K] in
theorem all_degree_le_one (p : Polynomial K) (hp : p.natDegree ≤ 1) :
    ∃ a b, p = affinePolynomial K a b := by
  exact ⟨p.coeff 1, p.coeff 0, Polynomial.eq_X_add_C_of_natDegree_le_one hp⟩

omit [Fintype K] [DecidableEq K] in
theorem affine_degree_le_one (a b : K) : (affinePolynomial K a b).natDegree ≤ 1 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact le_trans Polynomial.natDegree_mul_le (by simp)
  · simp

/-- The coefficient-pair enumeration is a bijection onto exactly the requested polynomials. -/
noncomputable def affineEquiv : (K × K) ≃ {p : Polynomial K // p.natDegree ≤ 1} where
  toFun ab := ⟨affinePolynomial K ab.1 ab.2, affine_degree_le_one K ab.1 ab.2⟩
  invFun p := (p.val.coeff 1, p.val.coeff 0)
  left_inv ab := by simp [affinePolynomial]
  right_inv p := by
    apply Subtype.ext
    exact (Polynomial.eq_X_add_C_of_natDegree_le_one p.property).symm

noncomputable def valueCount (a b : K) : ℕ :=
  (Finset.univ.image (fun x : K => a * x + b)).card

theorem valueCount_zero (b : K) : valueCount K 0 b = 1 := by
  classical
  have hi : Finset.univ.image (fun _ : K => b) = {b} := by
    ext y
    simp [eq_comm]
  simpa [valueCount] using congrArg Finset.card hi

theorem valueCount_ne_zero (a b : K) (ha : a ≠ 0) :
    valueCount K a b = Fintype.card K := by
  have hsurj : Function.Surjective (fun x : K => a * x + b) := by
    intro y
    refine ⟨(y - b) / a, ?_⟩
    field_simp
    ring
  have hi : Finset.univ.image (fun x : K => a * x + b) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  simp [valueCount, hi]

theorem valueCount_eq (a b : K) :
    valueCount K a b = if a = 0 then 1 else Fintype.card K := by
  split_ifs with h
  · subst a; exact valueCount_zero K b
  · exact valueCount_ne_zero K a b h

noncomputable def moment (k : ℕ) : ℝ :=
  (∑ ab : K × K, (valueCount K ab.1 ab.2 : ℝ) ^ k) /
    (Fintype.card (K × K) : ℝ)

noncomputable def variance : ℝ := moment K 2 - (moment K 1) ^ 2

theorem sum_power (k : ℕ) :
    (∑ ab : K × K, (valueCount K ab.1 ab.2 : ℝ) ^ k) =
      (Fintype.card K : ℝ) *
        (1 + ((Fintype.card K : ℝ) - 1) * (Fintype.card K : ℝ) ^ k) := by
  simp_rw [Fintype.sum_prod_type, valueCount_eq]
  simp only [Nat.cast_ite, Nat.cast_one]
  simp_rw [ite_pow, one_pow]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  have he (a : K) : (if a = 0 then (1 : ℝ) else (Fintype.card K : ℝ) ^ k) =
      (Fintype.card K : ℝ) ^ k + (if a = 0 then 1 - (Fintype.card K : ℝ) ^ k else 0) := by
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp
  ring

theorem variance_formula :
    variance K = ((Fintype.card K : ℝ) - 1) ^ 3 / (Fintype.card K : ℝ) ^ 2 := by
  have hq : (Fintype.card K : ℝ) ≠ 0 := by positivity
  simp only [variance, moment, sum_power, Fintype.card_prod, Nat.cast_mul]
  field_simp
  ring

/-- The moment formula is the standard uniform mean squared deviation. -/
theorem variance_is_mean_squared_deviation :
    variance K =
      (∑ ab : K × K, ((valueCount K ab.1 ab.2 : ℝ) - moment K 1) ^ 2) /
        (Fintype.card (K × K) : ℝ) := by
  have hc : (Fintype.card (K × K) : ℝ) ≠ 0 := by positivity
  have he (x : ℝ) : (x - moment K 1) ^ 2 =
      x ^ 2 - 2 * moment K 1 * x + (moment K 1) ^ 2 := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [variance, moment, pow_one]
  field_simp
  ring

noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

instance nthPrime_fact (n : ℕ) : Fact (Nat.Prime (nthPrime n)) :=
  ⟨Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n⟩

theorem nthPrime_tendsto : Tendsto nthPrime atTop atTop :=
  (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop

noncomputable def primeVariance (n : ℕ) : ℝ := variance (ZMod (nthPrime n))

theorem primeVariance_formula (n : ℕ) :
    primeVariance n = ((nthPrime n : ℝ) - 1) ^ 3 / (nthPrime n : ℝ) ^ 2 := by
  simpa [primeVariance] using variance_formula (ZMod (nthPrime n))

theorem primeVariance_normalized (n : ℕ) :
    primeVariance n / (nthPrime n : ℝ) = (1 - (nthPrime n : ℝ)⁻¹) ^ 3 := by
  have hp : Nat.Prime (nthPrime n) := (nthPrime_fact n).out
  have hq : (nthPrime n : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [primeVariance_formula]
  field_simp

theorem normalized_variance_limit :
    Tendsto (fun n => primeVariance n / (nthPrime n : ℝ)) atTop (nhds 1) := by
  have hq : Tendsto (fun n => (nthPrime n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp nthPrime_tendsto
  have hi : Tendsto (fun n => (nthPrime n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hq
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).sub hi).pow 3
  simpa [primeVariance_normalized] using hlim

theorem wrong_constant : (1 : ℝ) ≠ 1 - 1 / Real.exp 1 := by
  have he : (1 : ℝ) / Real.exp 1 ≠ 0 := one_div_ne_zero (Real.exp_ne_zero _)
  intro h
  apply he
  linarith

theorem refutes_normalized_prediction :
    ¬ Tendsto (fun n => primeVariance n / (nthPrime n : ℝ)) atTop
      (nhds (1 - 1 / Real.exp 1)) := by
  intro h
  exact wrong_constant (tendsto_nhds_unique normalized_variance_limit h)

theorem prediction_positive : 0 < (1 - 1 / Real.exp 1 : ℝ) := by
  apply sub_pos.mpr
  apply (div_lt_one (Real.exp_pos 1)).mpr
  exact Real.one_lt_exp_iff.mpr zero_lt_one

/-- Refutation of the literal asymptotic equivalence, on the fixed d=1 slice. -/
theorem refutes_asymptotic_equivalence :
    ¬ Tendsto (fun n => primeVariance n /
        ((nthPrime n : ℝ) * (1 - 1 / Real.exp 1))) atTop (nhds 1) := by
  intro h
  apply refutes_normalized_prediction
  have hm := h.mul_const (1 - 1 / Real.exp 1)
  simp only [one_mul] at hm
  apply hm.congr
  intro n
  have hc : (1 - 1 / Real.exp 1 : ℝ) ≠ 0 := ne_of_gt prediction_positive
  rw [div_mul_eq_div_div, div_mul_cancel₀ _ hc]

end TLMC1042
