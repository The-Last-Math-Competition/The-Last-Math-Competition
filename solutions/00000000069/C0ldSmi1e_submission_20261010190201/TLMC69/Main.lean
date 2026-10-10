import TLMC69.Approximation

noncomputable section
open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology
namespace TLMC69

lemma l1Error_nonneg (p : ℝ[X]) : 0 ≤ l1Error p :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => abs_nonneg _)

lemma errors_nonempty (n : ℕ) : {e : ℝ | ∃ p : ℝ[X], p.natDegree ≤ n ∧ e = l1Error p}.Nonempty :=
  ⟨l1Error 0, 0, by simp, rfl⟩

lemma errors_bddBelow (n : ℕ) : BddBelow {e : ℝ | ∃ p : ℝ[X], p.natDegree ≤ n ∧ e = l1Error p} := by
  refine ⟨0, ?_⟩
  rintro e ⟨p, _, rfl⟩
  exact l1Error_nonneg p

lemma bestError_nonneg (n : ℕ) : 0 ≤ bestError n := by
  apply le_csInf (errors_nonempty n)
  rintro e ⟨p, _, rfl⟩
  exact l1Error_nonneg p

lemma bestError_le (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) : bestError n ≤ l1Error p :=
  csInf_le (errors_bddBelow n) ⟨p, hp, rfl⟩

lemma approximant_error_bound (n : ℕ) : l1Error (approximant n) ≤ 128 / (2*n+1)^2 := by
  rw [approximant_error_exact]
  have hM := mass_lower n
  have hJ := moment_upper n
  have hN : (0:ℝ) < 2*n+1 := by positivity
  apply (div_le_div_of_nonneg_left (moment_nonneg n) (by positivity) hM).trans
  calc
    moment n / ((2*(n:ℝ)+1)^3/64) ≤ (2*(2*n+1)) / ((2*n+1)^3/64) :=
      div_le_div_of_nonneg_right hJ (by positivity)
    _ = 128/(2*n+1)^2 := by field_simp; ring

/-- An explicit bound on the actual degree-constrained L¹ infimum. -/
theorem bestError_subsequence_bound (n : ℕ) :
    bestError (8*n+2) ≤ 128 / (2*n+1)^2 :=
  (bestError_le _ (approximant n) (approximant_degree n)).trans (approximant_error_bound n)

lemma scaled_bound (n : ℕ) : (8*n+2 : ℝ) * bestError (8*n+2) ≤ 512 / (2*n+1) := by
  have hN : (0:ℝ) < 2*n+1 := by positivity
  calc
    (8*n+2 : ℝ) * bestError (8*n+2) ≤ (8*n+2) * (128/(2*n+1)^2) :=
      mul_le_mul_of_nonneg_left (bestError_subsequence_bound n) (by positivity)
    _ ≤ (4*(2*n+1)) * (128/(2*n+1)^2) := by
      apply mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = 512/(2*n+1) := by field_simp; ring

/-- The degree times best L¹ error tends to zero on a cofinal subsequence. -/
theorem scaled_subsequence_tendsto_zero :
    Tendsto (fun n : ℕ => (8*n+2 : ℝ) * bestError (8*n+2)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => mul_nonneg (by positivity) (bestError_nonneg _)) scaled_bound
  have hN : Tendsto (fun n : ℕ => (2*n+1:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n; have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact hN.const_div_atTop 512

/-- No nonzero constant can be the limit required by a B/n rate. -/
theorem no_nonzero_scaled_limit (B : ℝ) (hB : B ≠ 0) :
    ¬ Tendsto (fun n : ℕ => (n:ℝ) * bestError n) atTop (𝓝 B) := by
  intro h
  have hseq : Tendsto (fun n : ℕ => 8*n+2) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 8*n+2; omega) tendsto_id
  have hb := h.comp hseq
  have hb' : Tendsto (fun n : ℕ => (8*n+2:ℝ)*bestError (8*n+2)) atTop (𝓝 B) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hb
  exact hB (tendsto_nhds_unique hb' scaled_subsequence_tendsto_zero)

/-- Standard ratio definition of E_n ~ B/n; the comparison constant is nonzero. -/
def HasInverseLinearRate (B : ℝ) : Prop :=
  B ≠ 0 ∧ Tendsto (fun n : ℕ => bestError n / (B / n)) atTop (𝓝 1)

/-- Refutation of the necessary approximation-rate clause of conjecture 00000000069. -/
theorem conjecture69_disproof : ¬ ∃ B : ℝ, HasInverseLinearRate B := by
  rintro ⟨B, hB, hrate⟩
  apply no_nonzero_scaled_limit B hB
  have h := hrate.mul_const B
  have he : (fun n : ℕ => (bestError n / (B / n)) * B) =
      (fun n : ℕ => (n:ℝ) * bestError n) := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp
      ring
  rw [he, one_mul] at h
  exact h

#print axioms conjecture69_disproof
#print axioms bestError_subsequence_bound
#print axioms approximant_error_exact

end TLMC69
