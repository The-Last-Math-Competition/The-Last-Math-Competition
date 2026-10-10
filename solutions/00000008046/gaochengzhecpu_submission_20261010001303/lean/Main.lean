import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace Conjecture8046
open Set MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The characteristic function of the compact semialgebraic interval [0,1]. -/
def f (x : ℝ) : ℂ := if 0 ≤ x ∧ x ≤ 1 then 1 else 0

/-- A finite Boolean combination of real polynomial equalities and inequalities
describes the entire graph, including its boundary values. -/
theorem graph_description (x y z : ℝ) :
    f x = (⟨y,z⟩ : ℂ) ↔
      (0 ≤ x ∧ x ≤ 1 ∧ y = 1 ∧ z = 0) ∨
      ((x < 0 ∨ 1 < x) ∧ y = 0 ∧ z = 0) := by
  by_cases hx : 0 ≤ x ∧ x ≤ 1
  · simp only [f, if_pos hx, Complex.ext_iff, Complex.one_re, Complex.one_im]
    constructor
    · rintro ⟨hy,hz⟩
      exact Or.inl ⟨hx.1,hx.2,hy.symm,hz.symm⟩
    · rintro (⟨_,_,hy,hz⟩ | ⟨he,_,_⟩)
      · exact ⟨hy.symm,hz.symm⟩
      · rcases he with he | he <;> linarith [hx.1,hx.2]
  · have he : x < 0 ∨ 1 < x := by
      by_contra hn
      apply hx
      push_neg at hn
      exact hn
    simp only [f, if_neg hx, Complex.ext_iff, Complex.zero_re, Complex.zero_im]
    constructor
    · rintro ⟨hy,hz⟩
      exact Or.inr ⟨he,hy.symm,hz.symm⟩
    · rintro (⟨h0,h1,_,_⟩ | ⟨_,hy,hz⟩)
      · exact (hx ⟨h0,h1⟩).elim
      · exact ⟨hy.symm,hz.symm⟩

theorem support_eq : Function.support f = Icc (0 : ℝ) 1 := by
  ext x
  simp [Function.mem_support, f]

theorem compact_support : HasCompactSupport f := by
  change IsCompact (closure (Function.support f))
  rw [support_eq, isClosed_Icc.closure_eq]
  exact isCompact_Icc

theorem integral_formula (ξ : ℝ) (hξ : ξ ≠ 0) :
    Real.fourierIntegral f ξ =
      (Complex.exp (-2 * Real.pi * ξ * Complex.I) - 1) /
        (-2 * Real.pi * ξ * Complex.I) := by
  rw [Real.fourierIntegral_real_eq_integral_exp_smul]
  have hint : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) • f v) =
      (Icc (0 : ℝ) 1).indicator
        (fun v => Complex.exp ((-2 * Real.pi * ξ * Complex.I) * v)) := by
    funext v
    by_cases hv : 0 ≤ v ∧ v ≤ 1
    · simp [f, hv, Set.indicator_of_mem hv]
      congr 1
      ring
    · simp [f, hv, Set.indicator_of_not_mem hv]
  rw [hint, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hc : (-2 * Real.pi * ξ * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Complex.ofReal_ne_zero.mpr hξ))
      Complex.I_ne_zero
  rw [integral_exp_mul_complex hc]
  norm_num

def frequency (n : ℕ) : ℝ := n + 1 / 2

theorem frequency_pos (n : ℕ) : 0 < frequency n := by
  unfold frequency
  positivity

theorem exponential_at_frequency (n : ℕ) :
    Complex.exp (-2 * Real.pi * frequency n * Complex.I) = -1 := by
  have he : (-2 * Real.pi * frequency n * Complex.I : ℂ) =
      -(n : ℂ) * (2 * Real.pi * Complex.I) - Real.pi * Complex.I := by
    simp only [frequency, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [he, Complex.exp_sub_pi_mul_I, neg_mul, Complex.exp_neg,
    Complex.exp_nat_mul_two_pi_mul_I]
  norm_num

theorem fourier_at_frequency (n : ℕ) :
    Real.fourierIntegral f (frequency n) =
      -Complex.I / ((Real.pi * frequency n : ℝ) : ℂ) := by
  rw [integral_formula _ (frequency_pos n).ne', exponential_at_frequency]
  have hf : (frequency n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (frequency_pos n).ne'
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

theorem norm_fourier_at_frequency (n : ℕ) :
    ‖Real.fourierIntegral f (frequency n)‖ = 1 / (Real.pi * frequency n) := by
  rw [fourier_at_frequency, norm_div]
  simp [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos (frequency_pos n)]

theorem no_exponential_bound (C c R : ℝ) (hc : 0 < c) :
    ¬ ∀ ξ : ℝ, R ≤ ξ → ‖Real.fourierIntegral f ξ‖ ≤ C * Real.exp (-c * ξ) := by
  intro hbound
  have hlim : Tendsto (fun x : ℝ => (Real.pi * C) * (x * Real.exp (-c * x)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc))
  have hevent : ∀ᶠ x : ℝ in atTop,
      (Real.pi * C) * (x * Real.exp (-c * x)) < 1 :=
    hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨M,hM⟩ := eventually_atTop.mp hevent
  obtain ⟨n,hn⟩ := exists_nat_gt (max R M)
  have hR : R ≤ frequency n := by
    have := le_max_left R M
    unfold frequency
    linarith
  have hM' : M ≤ frequency n := by
    have := le_max_right R M
    unfold frequency
    linarith
  have hb := hbound (frequency n) hR
  rw [norm_fourier_at_frequency] at hb
  have hp : 0 < Real.pi * frequency n := mul_pos Real.pi_pos (frequency_pos n)
  have hone := (div_le_iff₀ hp).mp hb
  have hsmall := hM (frequency n) hM'
  nlinarith

#print axioms graph_description
#print axioms compact_support
#print axioms integral_formula
#print axioms norm_fourier_at_frequency
#print axioms no_exponential_bound
end
end Conjecture8046
