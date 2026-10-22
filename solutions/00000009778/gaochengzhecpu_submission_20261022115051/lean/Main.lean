import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology Interval

noncomputable section
namespace Conjecture9778

/- These are genuine interval-integral maps on functions. The Hilbert-space
   extension, adjoint theorem, spectral exhaustion and ordered singular-value
   identification are supplied by the explicitly cited primary theorem.
   No assertion that these pointwise definitions alone establish that theorem
   is made. -/
def volterra (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0)..x, f t
def backwardIntegral (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in x..1, f t

def frequency (n : ℕ) : ℝ := Real.pi * ((n : ℝ) + 1/2)
def cosineMode (n : ℕ) (x : ℝ) : ℝ := Real.cos (frequency n * x)

theorem frequency_pos (n : ℕ) : 0 < frequency n := by
  unfold frequency
  positivity

theorem frequency_cos_zero (n : ℕ) : Real.cos (frequency n) = 0 := by
  rw [show frequency n = (n : ℝ) * Real.pi + Real.pi/2 by unfold frequency; ring,
    Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]

theorem cosineMode_nonzero (n : ℕ) : cosineMode n 0 = 1 := by simp [cosineMode]

theorem genuine_volterra_cosine (n : ℕ) (x : ℝ) :
    volterra (cosineMode n) x = Real.sin (frequency n * x) / frequency n := by
  apply (eq_div_iff (frequency_pos n).ne').mpr
  have h := intervalIntegral.mul_integral_comp_mul_left (f := Real.cos)
    (a := 0) (b := x) (frequency n)
  rw [mul_zero, integral_cos, Real.sin_zero, sub_zero] at h
  change (∫ t in (0)..x, Real.cos (frequency n * t)) * frequency n = _
  exact (mul_comm _ _).trans h

theorem genuine_gram_cosine (n : ℕ) (x : ℝ) :
    backwardIntegral (volterra (cosineMode n)) x = cosineMode n x / frequency n ^ 2 := by
  unfold backwardIntegral
  simp_rw [genuine_volterra_cosine]
  rw [intervalIntegral.integral_div]
  have h := intervalIntegral.mul_integral_comp_mul_left (f := Real.sin)
    (a := x) (b := 1) (frequency n)
  rw [mul_one, integral_sin, frequency_cos_zero, sub_zero] at h
  have hi : (∫ t in x..1, Real.sin (frequency n * t)) =
      Real.cos (frequency n * x) / frequency n := by
    apply (eq_div_iff (frequency_pos n).ne').mpr
    simpa [mul_comm] using h
  rw [hi]
  unfold cosineMode
  ring

/- This is explicitly a reference formula, not a definition of singular
   values. The final theorems quantify over arbitrary sequences satisfying
   the cited exact Gram spectral theorem. -/
def referenceFormula (a : ℝ) (n : ℕ) : ℝ := 1 / (Real.pi * ((n : ℝ) + a))

theorem gram_formula_positive_root (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 ≤ s)
    (hgram : s^2 = 4 / (((2*(n : ℝ)-1)^2) * Real.pi^2)) :
    s = referenceFormula (-1/2) n := by
  have hp : 0 < (n : ℝ) - 1/2 := by
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hf : 0 ≤ referenceFormula (-1/2) n := by
    unfold referenceFormula
    exact le_of_lt (one_div_pos.mpr (mul_pos Real.pi_pos (by linarith)))
  apply (sq_eq_sq₀ hs hf).mp
  rw [hgram]
  have htwo : 2*(n : ℝ)-1 ≠ 0 := by linarith
  have hform : referenceFormula (-1/2) n = 2/(Real.pi*(2*(n : ℝ)-1)) := by
    unfold referenceFormula
    rw [show Real.pi*((n : ℝ)+(-1/2)) = (Real.pi*(2*(n : ℝ)-1))/2 by ring]
    field_simp
  rw [hform]
  field_simp [Real.pi_ne_zero, htwo]
  ring

theorem reference_second_coefficient (a : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)^2 *
      (referenceFormula a n - 1/(Real.pi*(n : ℝ)))) atTop (𝓝 (-a/Real.pi)) := by
  have ht : Tendsto (fun n : ℕ => (-a/Real.pi) * ((n : ℝ)/((n : ℝ)+a)))
      atTop (𝓝 (-a/Real.pi)) := by
    simpa using (tendsto_natCast_div_add_atTop a).const_mul (-a/Real.pi)
  apply ht.congr'
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 (-a))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnr : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by
    have := le_max_left (0 : ℝ) (-a)
    linarith
  have hna : (n : ℝ)+a ≠ 0 := by
    have := le_max_right (0 : ℝ) (-a)
    linarith
  unfold referenceFormula
  field_simp [Real.pi_ne_zero, hn0, hna]
  ring

theorem sequence_second_coefficient (s : ℕ → ℝ) (a : ℝ)
    (hs : s =ᶠ[atTop] referenceFormula a) :
    Tendsto (fun n : ℕ => (n : ℝ)^2 *
      (s n - 1/(Real.pi*(n : ℝ)))) atTop (𝓝 (-a/Real.pi)) := by
  apply (reference_second_coefficient a).congr'
  filter_upwards [hs] with n hn
  rw [hn]

/- A standard necessary finite-order consequence of a complete expansion
   containing only odd powers: after n^-1 and c*n^-3 the remainder is o(n^-3).
   The full infinite expansion is not replaced by this weaker condition. -/
def OddExpansionThroughThree (s : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, Tendsto (fun n : ℕ => (n : ℝ)^3 *
    (s n - 1/(Real.pi*(n : ℝ)) - c/(n : ℝ)^3)) atTop (𝓝 0)

theorem odd_expansion_forces_zero_second (s : ℕ → ℝ)
    (hs : OddExpansionThroughThree s) :
    Tendsto (fun n : ℕ => (n : ℝ)^2 *
      (s n - 1/(Real.pi*(n : ℝ)))) atTop (𝓝 0) := by
  obtain ⟨c,hc⟩ := hs
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inverse_atTop_nhds_zero_nat
  have hg : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ((n : ℝ)^3 *
      (s n - 1/(Real.pi*(n : ℝ)) - c/(n : ℝ)^3)) + c*(n : ℝ)⁻¹)
      atTop (𝓝 0) := by
    simpa using (hi.mul hc).add (hi.const_mul c)
  apply hg.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnr, Real.pi_ne_zero]
  ring

theorem no_odd_expansion_of_exact_reference (s : ℕ → ℝ) (a : ℝ) (ha : a ≠ 0)
    (hs : s =ᶠ[atTop] referenceFormula a) : ¬ OddExpansionThroughThree s := by
  intro hodd
  have heq := tendsto_nhds_unique (sequence_second_coefficient s a hs)
    (odd_expansion_forces_zero_second s hodd)
  exact (div_ne_zero (neg_ne_zero.mpr ha) Real.pi_ne_zero) heq

theorem half_integer_offset_ne_zero (k : ℤ) : (k : ℝ) - 1/2 ≠ 0 := by
  intro h
  have hreal : ((2*k : ℤ) : ℝ) = 1 := by push_cast; linarith
  have hint : 2*k = 1 := by exact_mod_cast hreal
  omega

theorem integer_reindex_still_no_odd (s : ℕ → ℝ) (k : ℤ)
    (hs : s =ᶠ[atTop] referenceFormula ((k : ℝ)-1/2)) :
    ¬ OddExpansionThroughThree s :=
  no_odd_expansion_of_exact_reference s _ (half_integer_offset_ne_zero k) hs

theorem gram_spectrum_second_coefficient (s : ℕ → ℝ)
    (hnonneg : ∀ n, 1 ≤ n → 0 ≤ s n)
    (hgram : ∀ n, 1 ≤ n → (s n)^2 =
      4 / (((2*(n : ℝ)-1)^2) * Real.pi^2)) :
    Tendsto (fun n : ℕ => (n : ℝ)^2 *
      (s n - 1/(Real.pi*(n : ℝ)))) atTop (𝓝 (1/(2*Real.pi))) := by
  have hs : s =ᶠ[atTop] referenceFormula (-1/2) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact gram_formula_positive_root n hn (s n) (hnonneg n hn) (hgram n hn)
  have hc : -(-1/2 : ℝ)/Real.pi = 1/(2*Real.pi) := by ring
  simpa only [hc] using sequence_second_coefficient s (-1/2) hs

/- Opmeer, Example 31, gives the actual ordered Gram spectral values.
   Nonnegative singular values are their positive square roots. This theorem
   derives the contradiction from precisely that public spectral identity,
   without adding it as a global assumption or defining it to hold. -/
theorem gram_spectrum_refutes_odd_expansion (s : ℕ → ℝ)
    (hnonneg : ∀ n, 1 ≤ n → 0 ≤ s n)
    (hgram : ∀ n, 1 ≤ n → (s n)^2 =
      4 / (((2*(n : ℝ)-1)^2) * Real.pi^2)) :
    ¬ OddExpansionThroughThree s := by
  apply no_odd_expansion_of_exact_reference s (-1/2) (by norm_num)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact gram_formula_positive_root n hn (s n) (hnonneg n hn) (hgram n hn)

#print axioms genuine_volterra_cosine
#print axioms genuine_gram_cosine
#print axioms gram_formula_positive_root
#print axioms reference_second_coefficient
#print axioms odd_expansion_forces_zero_second
#print axioms integer_reindex_still_no_odd
#print axioms gram_spectrum_second_coefficient
#print axioms gram_spectrum_refutes_odd_expansion

end Conjecture9778
