import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open scoped Matrix
open Matrix Polynomial

namespace Conjecture5131

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The closed ball of radius `e` for the induced infinity matrix norm. -/
def Budget {n : ℕ} (E : Mat n) (e : ℝ) : Prop :=
  ∀ i, (∑ j, ‖E i j‖) ≤ e

/-- Standard eigenvector equation, with a nonzero eigenvector. -/
def Eigen {n : ℕ} (A : Mat n) (z : ℂ) : Prop :=
  ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = z • v

/-- Closed perturbational pseudospectrum for the induced infinity norm. -/
def Pseudo {n : ℕ} (A : Mat n) (e : ℝ) : Set ℂ :=
  {z | ∃ E : Mat n, Budget E e ∧ Eigen (A + E) z}

theorem eigen_bound_two {E : Mat 2} {e : ℝ} {z : ℂ}
    (hE : Budget E e) (hz : Eigen E z) : ‖z‖ ≤ e := by
  obtain ⟨v, hv, heq⟩ := hz
  have hrow (i : Fin 2) : ‖E i 0‖ + ‖E i 1‖ ≤ e := by
    simpa [Fin.sum_univ_two] using hE i
  have hcoord (i : Fin 2) : E i 0 * v 0 + E i 1 * v 1 = z * v i := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun heq i
  have hnz : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext i
    fin_cases i <;> simp_all
  have hmax : ∃ i : Fin 2, 0 < ‖v i‖ ∧ ‖v 0‖ ≤ ‖v i‖ ∧ ‖v 1‖ ≤ ‖v i‖ := by
    by_cases h : ‖v 0‖ ≤ ‖v 1‖
    · refine ⟨1, ?_, h, le_rfl⟩
      rcases hnz with h0 | h1
      · exact lt_of_lt_of_le (norm_pos_iff.mpr h0) h
      · exact norm_pos_iff.mpr h1
    · refine ⟨0, ?_, le_rfl, le_of_lt (lt_of_not_ge h)⟩
      rcases hnz with h0 | h1
      · exact norm_pos_iff.mpr h0
      · exact lt_trans (norm_pos_iff.mpr h1) (lt_of_not_ge h)
  obtain ⟨i, hi, h0, h1⟩ := hmax
  have hnorm : ‖z‖ * ‖v i‖ ≤ e * ‖v i‖ := calc
    ‖z‖ * ‖v i‖ = ‖E i 0 * v 0 + E i 1 * v 1‖ := by
      rw [hcoord, norm_mul]
    _ ≤ ‖E i 0 * v 0‖ + ‖E i 1 * v 1‖ := norm_add_le _ _
    _ = ‖E i 0‖ * ‖v 0‖ + ‖E i 1‖ * ‖v 1‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖E i 0‖ * ‖v i‖ + ‖E i 1‖ * ‖v i‖ :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (norm_nonneg _))
        (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    _ = (‖E i 0‖ + ‖E i 1‖) * ‖v i‖ := by ring
    _ ≤ e * ‖v i‖ := mul_le_mul_of_nonneg_right (hrow i) (le_of_lt hi)
  exact (mul_le_mul_right hi).mp hnorm

theorem diagonal_witness (z : ℂ) :
    Budget (Matrix.diagonal fun _ : Fin 2 => z) ‖z‖ ∧
      Eigen (Matrix.diagonal fun _ : Fin 2 => z) z := by
  constructor
  · intro i
    fin_cases i <;> simp [Fin.sum_univ_two, Matrix.diagonal]
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.diagonal]

theorem zero_pseudospectrum (e : ℝ) :
    Pseudo (0 : Mat 2) e = {z : ℂ | ‖z‖ ≤ e} := by
  ext z
  constructor
  · rintro ⟨E, hE, hz⟩
    exact eigen_bound_two hE (by simpa using hz)
  · intro hz
    obtain ⟨hE, hEig⟩ := diagonal_witness z
    refine ⟨Matrix.diagonal (fun _ : Fin 2 => z), ?_, ?_⟩
    · exact fun i => (hE i).trans hz
    · simpa using hEig

theorem sharp_response {e : ℝ} (he : 0 ≤ e) :
    (∀ z ∈ Pseudo (0 : Mat 2) e, ‖z‖ ≤ e) ∧
      ∃ z ∈ Pseudo (0 : Mat 2) e, ‖z‖ = e := by
  rw [zero_pseudospectrum]
  refine ⟨fun _ hz => hz, (e : ℂ), ?_, ?_⟩ <;>
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]

theorem zero_charpoly : (0 : Mat 2).charpoly = (X : ℂ[X]) ^ 2 := by
  simp [Matrix.charpoly, Matrix.det_fin_two, Matrix.charmatrix, Matrix.scalar,
    Matrix.diagonal, pow_two]

theorem zero_multiplicity : rootMultiplicity (0 : ℂ) (0 : Mat 2).charpoly = 2 := by
  rw [zero_charpoly]
  simpa using (rootMultiplicity_X_sub_C_pow (0 : ℂ) 2)

theorem zero_area {e : ℝ} (he : 0 ≤ e) :
    (MeasureTheory.volume (Pseudo (0 : Mat 2) e)).toReal = Real.pi * e ^ 2 := by
  have hset : Pseudo (0 : Mat 2) e = Metric.closedBall (0 : ℂ) e := by
    rw [zero_pseudospectrum]
    ext z
    simp [Metric.mem_closedBall, dist_zero_right]
  rw [hset, Complex.volume_closedBall]
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow, he, mul_comm]

/-- The necessary lower bound in the proposed area power law. Restricting
    to a single algebraic eigenvalue removes any question of contributions
    from other spectral clusters. -/
def MultiplicityAreaLaw : Prop :=
  ∀ (n : ℕ) (A : Mat n) (a : ℂ), 0 < n →
    A.charpoly = (X - C a) ^ n →
    ∃ c : ℝ, 0 < c ∧ ∃ d : ℝ, 0 < d ∧
      ∀ t : ℝ, 0 < t → t < d →
        c * t ^ 2 ≤ (MeasureTheory.volume (Pseudo A (t ^ n))).toReal

theorem not_multiplicity_area_law : ¬ MultiplicityAreaLaw := by
  intro h
  have hpoly : (0 : Mat 2).charpoly = (X - C (0 : ℂ)) ^ 2 := by
    simpa using zero_charpoly
  obtain ⟨c, hc, d, hd, hscale⟩ := h 2 0 0 (by decide) hpoly
  have hpi : 0 < Real.pi + 1 := by have := Real.pi_pos; linarith
  let t := min d (min 1 (c / (Real.pi + 1))) / 2
  have hp : 0 < min d (min 1 (c / (Real.pi + 1))) :=
    lt_min hd (lt_min (by norm_num) (div_pos hc hpi))
  have ht : 0 < t := by dsimp [t]; linarith
  have htd : t < d := by
    dsimp [t]
    have := min_le_left d (min 1 (c / (Real.pi + 1)))
    linarith
  have ht1 : t < 1 := by
    dsimp [t]
    have := (min_le_right d (min 1 (c / (Real.pi + 1)))).trans
      (min_le_left 1 (c / (Real.pi + 1)))
    linarith
  have htc : t < c / (Real.pi + 1) := by
    dsimp [t]
    have := (min_le_right d (min 1 (c / (Real.pi + 1)))).trans
      (min_le_right 1 (c / (Real.pi + 1)))
    linarith
  have hsmall : Real.pi * t ^ 2 < c := by
    have hprod := (lt_div_iff₀ hpi).mp htc
    have hsq : t ^ 2 < t := by nlinarith
    have := mul_lt_mul_of_pos_left hsq Real.pi_pos
    nlinarith
  have harea := hscale t ht htd
  rw [zero_area (sq_nonneg t)] at harea
  have heq : Real.pi * (t ^ 2) ^ 2 = (Real.pi * t ^ 2) * t ^ 2 := by ring
  rw [heq] at harea
  have hc_le : c ≤ Real.pi * t ^ 2 := (mul_le_mul_right (sq_pos_of_pos ht)).mp harea
  linarith

/-- The lower half of a sharp `epsilon^(1/m)` response law, using
    `epsilon = t^m` to avoid fractional powers. Any two-sided Theta law
    or positive leading asymptotic constant implies this statement. -/
def MultiplicityResponseLaw : Prop :=
  ∀ (n : ℕ) (A : Mat n) (a : ℂ) (m : ℕ),
    0 < m → rootMultiplicity a A.charpoly = m →
    ∃ c : ℝ, 0 < c ∧ ∃ d : ℝ, 0 < d ∧
      ∀ t : ℝ, 0 < t → t < d →
        ∃ z ∈ Pseudo A (t ^ m), c * t ≤ ‖z - a‖

theorem not_multiplicity_response_law : ¬ MultiplicityResponseLaw := by
  intro h
  obtain ⟨c, hc, d, hd, hscale⟩ := h 2 0 0 2 (by decide) zero_multiplicity
  let t := min c d / 2
  have hp : 0 < min c d := lt_min hc hd
  have ht : 0 < t := by dsimp [t]; linarith
  have htc : t < c := by dsimp [t]; have := min_le_left c d; linarith
  have htd : t < d := by dsimp [t]; have := min_le_right c d; linarith
  obtain ⟨z, hz, hlow⟩ := hscale t ht htd
  rw [zero_pseudospectrum] at hz
  simp only [Set.mem_setOf_eq] at hz
  simp only [sub_zero] at hlow
  nlinarith

#print axioms zero_pseudospectrum
#print axioms sharp_response
#print axioms zero_multiplicity
#print axioms zero_area
#print axioms not_multiplicity_area_law
#print axioms not_multiplicity_response_law

end Conjecture5131
