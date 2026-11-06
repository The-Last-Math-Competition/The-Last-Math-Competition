import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Matrix
open scoped Matrix.L2OpNorm
noncomputable section
namespace Conjecture2362
set_option maxHeartbeats 1200000
set_option maxRecDepth 2000

abbrev M := Matrix (Fin 2) (Fin 2) ℂ

def E : M := !![0,1;0,0]
def P : M := !![0,0;0,1]
def jordan (N : ℝ) : M := 1 + (N : ℂ) • E

theorem E_sq : E * E = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [E, Matrix.mul_apply, Fin.sum_univ_two]

theorem E_star_mul : Eᴴ * E = P := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [E, P, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_star : Pᴴ = P := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P]

theorem P_sq : P * P = P := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_ne_zero : P ≠ 0 := by
  intro h
  have hh := congrArg (fun A : M => A 1 1) h
  norm_num [P] at hh

theorem E_norm : ‖E‖ = 1 := by
  have hP := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [P_star, P_sq] at hP
  have hPpos := norm_pos_iff.mpr P_ne_zero
  have hP1 : ‖P‖ = 1 := by nlinarith
  have hE := Matrix.l2_opNorm_conjTranspose_mul_self E
  rw [E_star_mul, hP1] at hE
  have hE0 := norm_nonneg E
  nlinarith

def inverseResolvent (N : ℝ) (z : ℂ) : M :=
  (z - 1)⁻¹ • 1 + ((N : ℂ) / (z - 1)^2) • E

theorem inverseResolvent_mul (N : ℝ) (z : ℂ) (hz : z ≠ 1) :
    inverseResolvent N z * (algebraMap ℂ M z - jordan N) = 1 := by
  have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseResolvent, jordan, E, Matrix.mul_apply, Fin.sum_univ_two,
      Algebra.algebraMap_eq_smul_one]
  all_goals field_simp [hne] <;> ring

theorem resolvent_isUnit (N : ℝ) (z : ℂ) (hz : z ≠ 1) :
    IsUnit (algebraMap ℂ M z - jordan N) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse (inverseResolvent_mul N z hz))

theorem resolvent_formula (N : ℝ) (z : ℂ) (hz : z ≠ 1) :
    resolvent (jordan N) z = inverseResolvent N z := by
  rw [resolvent, ← Matrix.nonsing_inv_eq_ringInverse]
  exact Matrix.inv_eq_left_inv (inverseResolvent_mul N z hz)

theorem spectrum_subset (N : ℝ) : spectrum ℂ (jordan N) ⊆ {1} := by
  intro z hz
  by_contra h
  exact (spectrum.mem_iff.mp hz) (resolvent_isUnit N z h)

def g (z : ℂ) : ℂ := z / (1 + z)^3
def rationalValue (A : M) : M := A * ((1 + A)⁻¹)^3

theorem denominator_nonzero {z : ℂ} (hz : 0 ≤ z.re) : 1 + z ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
  linarith

theorem g_holomorphic : DifferentiableOn ℂ g {z : ℂ | 0 < z.re} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  exact differentiableAt_id.div
    ((differentiableAt_const (1 : ℂ)).add differentiableAt_id |>.pow 3)
    (pow_ne_zero 3 (denominator_nonzero (le_of_lt hz)))

theorem norm_one_add_bounds (z : ℂ) (hz : 0 ≤ z.re) :
    1 ≤ ‖1 + z‖ ∧ ‖z‖ ≤ ‖1 + z‖ ∧ 1 + ‖z‖^2 ≤ ‖1 + z‖^2 := by
  have heq : ‖1 + z‖^2 = 1 + ‖z‖^2 + 2*z.re := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_one,
      one_mul, Complex.conj_re]
  have h0 := norm_nonneg z
  have h1 := norm_nonneg (1 + z)
  constructor
  · nlinarith
  constructor
  · nlinarith
  · linarith

/-- Standard H_0^infinity decay with exponent one, stronger than sup norm <=1. -/
theorem g_decay (z : ℂ) (hz : 0 ≤ z.re) :
    ‖g z‖ ≤ ‖z‖ / (1 + ‖z‖^2) := by
  have h := norm_one_add_bounds z hz
  have hd : 0 < ‖1 + z‖ := norm_pos_iff.mpr (denominator_nonzero hz)
  rw [g, norm_div, norm_pow]
  apply div_le_div_of_nonneg_left (norm_nonneg z) (by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr h.1) (sq_nonneg ‖1+z‖)]

theorem g_bounded (z : ℂ) (hz : 0 ≤ z.re) : ‖g z‖ ≤ 1 := by
  have h := g_decay z hz
  have hr : ‖z‖ / (1 + ‖z‖^2) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 1 + ‖z‖^2)).mpr
    nlinarith [sq_nonneg (‖z‖ - 1)]
  exact h.trans hr

def inversePlus (N : ℝ) : M := (1/2 : ℂ) • 1 - ((N : ℂ)/4) • E

theorem inversePlus_mul (N : ℝ) : inversePlus N * (1 + jordan N) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inversePlus, jordan, E, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem plus_inverse_formula (N : ℝ) : (1 + jordan N)⁻¹ = inversePlus N :=
  Matrix.inv_eq_left_inv (inversePlus_mul N)

theorem rationalValue_formula (N : ℝ) :
    rationalValue (jordan N) = (1/8 : ℂ) • 1 - ((N : ℂ)/16) • E := by
  rw [rationalValue, plus_inverse_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inversePlus, jordan, E, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem rationalValue_lower (N : ℝ) (hN : 0 ≤ N) :
    N/16 - 1/8 ≤ ‖rationalValue (jordan N)‖ := by
  have h := norm_sub_le ((1/8 : ℂ) • (1 : M)) (rationalValue (jordan N))
  have heq : (1/8 : ℂ) • (1 : M) - rationalValue (jordan N) = ((N : ℂ)/16) • E := by
    rw [rationalValue_formula]
    abel
  rw [heq] at h
  norm_num [norm_smul, E_norm, CStarRing.norm_one, norm_div, Complex.norm_real,
    abs_of_nonneg hN] at h
  linarith

def closedSector (ω : ℝ) : Set ℂ := {z | |Complex.arg z| ≤ ω}

/-- The standard bounded-operator sectorial resolvent condition; matrices
carry the genuine Euclidean operator norm, not an entrywise matrix norm. -/
def Sectorial {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] (ω : ℝ) (A : B) : Prop :=
  0 ≤ ω ∧ ω < Real.pi ∧ spectrum ℂ A ⊆ closedSector ω ∧
  ∀ θ : ℝ, ω < θ → θ < Real.pi → ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : ℂ, z ∉ closedSector θ →
      IsUnit (algebraMap ℂ B z - A) ∧ ‖z • resolvent A z‖ ≤ C

theorem outside_sector_geometry (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi)
    (z : ℂ) (hz : z ∉ closedSector θ) :
    0 < min 1 (1 - Real.cos θ) ∧
    min 1 (1 - Real.cos θ) ≤ ‖z - 1‖ := by
  have hc : Real.cos θ < 1 := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hθπ.le hθ
    simpa using hh
  have hδ : 0 < min 1 (1 - Real.cos θ) := lt_min (by norm_num) (by linarith)
  have hcos : Real.cos (Complex.arg z) ≤ Real.cos θ := by
    have ha : θ ≤ |Complex.arg z| := le_of_lt (lt_of_not_ge hz)
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi hθ.le (Complex.abs_arg_le_pi z) ha
    simpa only [Real.cos_abs] using hh
  have hre : z.re ≤ ‖z‖ * Real.cos θ := by
    have hh := mul_le_mul_of_nonneg_left hcos (norm_nonneg z)
    simpa only [Complex.norm_mul_cos_arg] using hh
  have heq : ‖z - 1‖^2 = ‖z‖^2 + 1 - 2*z.re := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one,
      map_one, mul_one]
  have hd0 := norm_nonneg (z - 1)
  have hr0 := norm_nonneg z
  refine ⟨hδ, ?_⟩
  by_cases hc0 : 0 ≤ Real.cos θ
  · have hmin : min 1 (1 - Real.cos θ) = 1 - Real.cos θ := min_eq_right (by linarith)
    rw [hmin]
    have hp : 0 ≤ Real.cos θ * (1 - Real.cos θ) := mul_nonneg hc0 (by linarith)
    have hs := sq_nonneg (‖z‖ - Real.cos θ)
    nlinarith
  · have hre0 : z.re ≤ 0 := hre.trans (mul_nonpos_of_nonneg_of_nonpos hr0 (le_of_not_ge hc0))
    have hd1 : 1 ≤ ‖z-1‖ := by nlinarith [sq_nonneg ‖z‖]
    exact (min_le_left _ _).trans hd1

theorem norm_resolvent_bound (N : ℝ) (hN : 0 ≤ N) (z : ℂ) (hz : z ≠ 1) :
    ‖z • resolvent (jordan N) z‖ ≤
      ‖z‖ / ‖z-1‖ + N * (‖z‖ / ‖z-1‖^2) := by
  rw [norm_smul, resolvent_formula N z hz]
  have hh := norm_add_le ((z-1)⁻¹ • (1 : M)) (((N : ℂ)/(z-1)^2) • E)
  have h := mul_le_mul_of_nonneg_left hh (norm_nonneg z)
  norm_num [inverseResolvent, norm_smul, norm_inv, norm_div, norm_pow,
    CStarRing.norm_one, E_norm, Complex.norm_real, abs_of_nonneg hN] at h ⊢
  convert h using 1; ring

theorem jordan_sectorial_zero (N : ℝ) (hN : 0 ≤ N) : Sectorial 0 (jordan N) := by
  refine ⟨le_refl 0, Real.pi_pos, ?_, ?_⟩
  · intro z hz
    have hz1 : z = 1 := spectrum_subset N hz
    simp [hz1, closedSector]
  · intro θ hθ hθπ
    let δ : ℝ := min 1 (1 - Real.cos θ)
    have hc : Real.cos θ < 1 := by
      have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hθπ.le hθ
      simpa using hh
    have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
    refine ⟨(1 + 1/δ) * (1 + N/δ), by positivity, ?_⟩
    intro z hz
    have hgeom := outside_sector_geometry θ hθ hθπ z hz
    have hdδ : δ ≤ ‖z-1‖ := hgeom.2
    have hd : 0 < ‖z-1‖ := lt_of_lt_of_le hδ hdδ
    have hz1 : z ≠ 1 := by intro heq; simp [heq] at hd
    refine ⟨resolvent_isUnit N z hz1, ?_⟩
    have hr : ‖z‖ ≤ ‖z-1‖ + 1 := by
      have hh := norm_add_le (z-1) (1 : ℂ)
      simpa using hh
    have hinv : 1 / ‖z-1‖ ≤ 1/δ := one_div_le_one_div_of_le hδ hdδ
    have hratio : ‖z‖ / ‖z-1‖ ≤ 1 + 1/δ := by
      calc
        _ ≤ (‖z-1‖ + 1) / ‖z-1‖ := div_le_div_of_nonneg_right hr hd.le
        _ = 1 + 1/‖z-1‖ := by field_simp
        _ ≤ 1 + 1/δ := add_le_add_left hinv 1
    have hratio2 : ‖z‖ / ‖z-1‖^2 ≤ (1 + 1/δ) / δ := by
      calc
        _ = (‖z‖ / ‖z-1‖) * (1/‖z-1‖) := by ring
        _ ≤ (1 + 1/δ) * (1/δ) := mul_le_mul hratio hinv (by positivity) (by positivity)
        _ = (1 + 1/δ) / δ := by ring
    apply (norm_resolvent_bound N hN z hz1).trans
    have hh := add_le_add hratio (mul_le_mul_of_nonneg_left hratio2 hN)
    convert hh using 1; ring


theorem rationalValue_unbounded (C : ℝ) :
    ∃ N : ℝ, 0 ≤ N ∧ Sectorial 0 (jordan N) ∧ C < ‖rationalValue (jordan N)‖ := by
  let N : ℝ := 16 * (max C 0 + 1)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨N, hN, jordan_sectorial_zero N hN, ?_⟩
  have h := rationalValue_lower N hN
  have hc := le_max_left C 0
  dsimp [N] at h
  linarith

abbrev H := EuclideanSpace ℂ (Fin 2)
abbrev B := H →L[ℂ] H

def Φ : M ≃⋆ₐ[ℂ] B := Matrix.toEuclideanCLM

theorem Φ_norm (A : M) : ‖Φ A‖ = ‖A‖ := (Matrix.cstar_norm_def A).symm

theorem map_inverse_unit (A : M) (hA : IsUnit A) :
    Φ (Ring.inverse A) = Ring.inverse (Φ A) := by
  rcases hA with ⟨u, rfl⟩
  rw [Ring.inverse_unit]
  have hh := Ring.inverse_unit (Units.map Φ.toMonoidHom u)
  exact hh.symm

theorem Φ_resolvent (A : M) (z : ℂ) (h : IsUnit (algebraMap ℂ M z - A)) :
    Φ (resolvent A z) = resolvent (Φ A) z := by
  unfold resolvent
  rw [map_inverse_unit _ h]
  congr 1
  simp [Algebra.algebraMap_eq_smul_one]

theorem Φ_sectorial {ω : ℝ} {A : M} (hA : Sectorial ω A) : Sectorial ω (Φ A) := by
  rcases hA with ⟨h0, hπ, hspec, hres⟩
  refine ⟨h0, hπ, ?_, ?_⟩
  · simpa only [AlgEquiv.spectrum_eq Φ A] using hspec
  · intro θ hθ hθπ
    obtain ⟨C, hC, hbound⟩ := hres θ hθ hθπ
    refine ⟨C, hC, ?_⟩
    intro z hz
    obtain ⟨hu, hb⟩ := hbound z hz
    refine ⟨?_, ?_⟩
    · have hh : IsUnit (Φ (algebraMap ℂ M z - A)) := hu.map Φ.toMonoidHom
      simpa only [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, map_one] using hh
    · rw [← Φ_resolvent A z hu, ← map_smul Φ]
      simpa only [Φ_norm] using hb

def operatorRationalValue (A : B) : B := A * (Ring.inverse (1 + A))^3

theorem plus_isUnit (N : ℝ) : IsUnit (1 + jordan N) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse (inversePlus_mul N))

theorem Φ_rationalValue (N : ℝ) :
    Φ (rationalValue (jordan N)) = operatorRationalValue (Φ (jordan N)) := by
  simp only [rationalValue, operatorRationalValue, map_mul, map_pow,
    Matrix.nonsing_inv_eq_ringInverse]
  rw [map_inverse_unit _ (plus_isUnit N)]
  simp

theorem bounded_operator_rational_test_unbounded (C : ℝ) :
    ∃ A : B, Sectorial 0 A ∧ C < ‖operatorRationalValue A‖ := by
  obtain ⟨N, _, hsec, hnorm⟩ := rationalValue_unbounded C
  refine ⟨Φ (jordan N), Φ_sectorial hsec, ?_⟩
  rw [← Φ_rationalValue, Φ_norm]
  exact hnorm

theorem no_angle_only_rational_test_bound :
    ¬ ∃ C : ℝ, ∀ A : B, Sectorial 0 A → ‖operatorRationalValue A‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨A, hsec, hnorm⟩ := bounded_operator_rational_test_unbounded C
  exact (not_le_of_gt hnorm) (hC A hsec)

def openSector (θ : ℝ) : Set ℂ := {z | z ≠ 0 ∧ |Complex.arg z| < θ}

theorem openSector_halfPlane : openSector (Real.pi/2) = {z : ℂ | 0 < z.re} := by
  ext z
  simp only [openSector, Set.mem_setOf_eq, Complex.abs_arg_lt_pi_div_two_iff]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact h
    · exact (hne h).elim
  · intro h
    exact ⟨by intro hz; simp [hz] at h, Or.inl h⟩

theorem g_is_H0_infty_test :
    DifferentiableOn ℂ g (openSector (Real.pi/2)) ∧
    (∀ z ∈ openSector (Real.pi/2), ‖g z‖ ≤ ‖z‖/(1+‖z‖^2)) ∧
    (∀ z ∈ openSector (Real.pi/2), ‖g z‖ ≤ 1) := by
  rw [openSector_halfPlane]
  exact ⟨g_holomorphic, fun z hz => g_decay z hz.le, fun z hz => g_bounded z hz.le⟩

theorem Sectorial.mono {D : Type*} [NormedRing D] [NormedAlgebra ℂ D]
    {A : D} {ω ν : ℝ} (h : Sectorial ω A) (hων : ω ≤ ν) (hν : ν < Real.pi) :
    Sectorial ν A := by
  rcases h with ⟨hω0, _, hspec, hres⟩
  refine ⟨hω0.trans hων, hν, ?_, ?_⟩
  · intro z hz
    exact (hspec hz).trans hων
  · intro θ hθ hθπ
    exact hres θ (lt_of_le_of_lt hων hθ) hθπ

theorem fixed_positive_angle_counterexample (C : ℝ) :
    ∃ A : B, Sectorial (Real.pi/3) A ∧ C < ‖operatorRationalValue A‖ := by
  obtain ⟨A, hsec, hnorm⟩ := bounded_operator_rational_test_unbounded C
  refine ⟨A, hsec.mono (by positivity) (by linarith [Real.pi_pos]), hnorm⟩

theorem no_fixed_positive_angle_bound :
    ¬ ∃ C : ℝ, ∀ A : B, Sectorial (Real.pi/3) A → ‖operatorRationalValue A‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨A, hsec, hnorm⟩ := fixed_positive_angle_counterexample C
  exact (not_le_of_gt hnorm) (hC A hsec)

theorem g_standard_decay (z : ℂ) (hz : 0 ≤ z.re) :
    ‖g z‖ ≤ 2 * ‖z‖ / (1+‖z‖)^2 := by
  apply (g_decay z hz).trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [norm_nonneg z, sq_nonneg (‖z‖-1)]

theorem Φ_plus_isUnit (N : ℝ) : IsUnit (1 + Φ (jordan N)) := by
  have hh : IsUnit (Φ (1 + jordan N)) := (plus_isUnit N).map Φ.toMonoidHom
  simpa only [map_add, map_one] using hh

#print axioms g_standard_decay
#print axioms Φ_plus_isUnit
#print axioms no_fixed_positive_angle_bound
#print axioms g_is_H0_infty_test
#print axioms g_holomorphic
#print axioms g_decay
#print axioms g_bounded
#print axioms jordan_sectorial_zero
#print axioms rationalValue_formula
#print axioms bounded_operator_rational_test_unbounded
#print axioms no_angle_only_rational_test_bound

end Conjecture2362
