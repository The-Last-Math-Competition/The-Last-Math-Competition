import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace TLMC1149

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The finite shifted factorial (q;q)_n, over the rational numbers. -/
def qFactorial (q : ℚ) (n : ℕ) : ℚ :=
  ∏ j ∈ Finset.range n, (1 - q ^ (j + 1))

/-- The standard Gaussian coefficient at q=5; zero outside 0 <= k <= n. -/
def gaussian5 (n k : ℕ) : ℚ :=
  if k ≤ n then qFactorial 5 n / (qFactorial 5 k * qFactorial 5 (n - k)) else 0

theorem qFactorial_five_ne_zero (n : ℕ) : qFactorial 5 n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  have h : (1 : ℚ) < 5 ^ (j + 1) := one_lt_pow₀ (by norm_num) (by omega)
  linarith

theorem gaussian5_denominator_ne_zero (n k : ℕ) :
    qFactorial 5 k * qFactorial 5 (n - k) ≠ 0 :=
  mul_ne_zero (qFactorial_five_ne_zero k) (qFactorial_five_ne_zero (n-k))

theorem no_half_integral_norm (x : ℚ_[2]) :
    ‖x‖ ≠ (2 : ℝ) ^ (-(1 : ℝ) / 2) := by
  intro h
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at h
    exact (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)) h.symm
  rw [Padic.norm_eq_zpow_neg_valuation hx, ← Real.rpow_intCast] at h
  have he := (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)).mp h
  have he' : (2 : ℝ) * (x.valuation : ℝ) = 1 := by
    push_cast at he
    linarith
  have hi : (2 : ℤ) * x.valuation = 1 := by exact_mod_cast he'
  omega

noncomputable def gaussianPadic (n k : ℕ) : ℚ_[2] := (gaussian5 n k : ℚ_[2])

theorem gaussianPadic_ne_half_norm (n k : ℕ) :
    ‖gaussianPadic n k‖ ≠ (2 : ℝ) ^ (-(1 : ℝ) / 2) :=
  no_half_integral_norm _

theorem gaussianAlgCl_ne_half_norm (n k : ℕ) :
    ‖(gaussianPadic n k : PadicAlgCl 2)‖ ≠ (2 : ℝ) ^ (-(1 : ℝ) / 2) := by
  rw [PadicAlgCl.norm_extends]
  exact gaussianPadic_ne_half_norm n k

/-- Even a sequence of arbitrary Q_2 elements cannot meet the required norm law. -/
theorem no_requested_padic_sequence :
    ¬ ∃ a : ℕ → ℚ_[2], ∀ m : ℕ, 1 ≤ m →
      ‖a m‖ = (2 : ℝ) ^ (-(m : ℝ) / 2) := by
  rintro ⟨a, ha⟩
  exact no_half_integral_norm (a 1) (by simpa using ha 1 (by omega))

/-- Thus any choice of natural upper/lower indices for Gaussian coefficients fails. -/
theorem no_requested_gaussian_series :
    ¬ ∃ n k : ℕ → ℕ, ∀ m : ℕ, 1 ≤ m →
      ‖(gaussianPadic (n m) (k m) : PadicAlgCl 2)‖ =
        (2 : ℝ) ^ (-(m : ℝ) / 2) := by
  rintro ⟨n, k, h⟩
  exact gaussianAlgCl_ne_half_norm (n 1) (k 1) (by simpa using h 1 (by omega))

/-- The minimal-model parameter pair (2,5) obeys 2 <= p < q and coprimality. -/
theorem legal_parameters : (2 : ℕ) ≤ 2 ∧ (2 : ℕ) < 5 ∧ Nat.Coprime 2 5 := by
  norm_num

theorem counterexample :
    ((2 : ℕ) ≤ 2 ∧ (2 : ℕ) < 5 ∧ Nat.Coprime 2 5) ∧
    ¬ ∃ n k : ℕ → ℕ, ∀ m : ℕ, 1 ≤ m →
      ‖(gaussianPadic (n m) (k m) : PadicAlgCl 2)‖ =
        (2 : ℝ) ^ (-(m : ℝ) / 2) :=
  ⟨legal_parameters, no_requested_gaussian_series⟩

end TLMC1149
