import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

noncomputable section
namespace Conjecture6640

open Matrix

abbrev State := Fin 2
abbrev Vector := State → ℝ
abbrev Mat := Matrix State State ℝ

/-- Column-vector convention: p'(t)=Q p(t). -/
def IsGenerator (Q : Mat) : Prop :=
  (∀ i j, i ≠ j → 0 ≤ Q i j) ∧ ∀ j, ∑ i, Q i j = 0

def Probability (p : Vector) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

def Static (Q : Mat) : Set Vector := {p | Probability p ∧ Q *ᵥ p = 0}

def Reversible (Q : Mat) (p : Vector) : Prop :=
  Probability p ∧ ∀ i j, Q i j * p j = Q j i * p i

def generator (r : ℝ) : Mat := !![-r, r; r, -r]
def uniform : Vector := ![1 / 2, 1 / 2]

def transition (r t : ℝ) : Mat :=
  !![(1 + Real.exp (-2 * r * t)) / 2, (1 - Real.exp (-2 * r * t)) / 2;
     (1 - Real.exp (-2 * r * t)) / 2, (1 + Real.exp (-2 * r * t)) / 2]

theorem generator_valid {r : ℝ} (hr : 0 ≤ r) : IsGenerator (generator r) := by
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [generator] at * <;> assumption
  · intro j
    fin_cases j <;> simp [generator, Fin.sum_univ_two]

theorem uniform_probability : Probability uniform := by
  constructor
  · intro i
    fin_cases i <;> norm_num [uniform]
  · norm_num [uniform, Fin.sum_univ_two]

theorem generator_reversible (r : ℝ) : Reversible (generator r) uniform := by
  refine ⟨uniform_probability, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [generator, uniform]

theorem generator_symmetric (r : ℝ) : (generator r).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [generator]

theorem static_iff {r : ℝ} (hr : r ≠ 0) (p : Vector) :
    p ∈ Static (generator r) ↔ p = uniform := by
  constructor
  · rintro ⟨hp, hQ⟩
    have hs := hp.2
    have h0 := congrFun hQ 0
    simp [generator, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    have hdiff : p 0 = p 1 := by
      have : r * (p 1 - p 0) = 0 := by nlinarith [h0]
      have := (mul_eq_zero.mp this).resolve_left hr
      linarith
    simp only [Fin.sum_univ_two] at hs
    ext i
    fin_cases i <;> simp [uniform] <;> linarith
  · rintro rfl
    refine ⟨uniform_probability, ?_⟩
    ext i
    fin_cases i <;> simp [generator, uniform, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem kernel_iff {r : ℝ} (hr : r ≠ 0) (p : Vector) :
    generator r *ᵥ p = 0 ↔ p 0 = p 1 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [generator, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    have hm : r * (p 1 - p 0) = 0 := by nlinarith [h0]
    have := (mul_eq_zero.mp hm).resolve_left hr
    linarith
  · intro h
    ext i
    fin_cases i <;> simp [generator, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

theorem generator_spectrum (r mu : ℝ) :
    mu ∈ spectrum ℝ (generator r) ↔ mu = 0 ∨ mu = -2 * r := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  simp only [not_not]
  have hd : (algebraMap ℝ Mat mu - generator r).det = mu * (mu + 2 * r) := by
    simp [Matrix.det_fin_two, generator, Matrix.algebraMap_eq_diagonal]
    ring
  rw [hd, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; linarith
  · rintro (h | h)
    · exact Or.inl h
    · right; linarith

theorem generators_have_different_spectra :
    spectrum ℝ (generator 1) ≠ spectrum ℝ (generator 2) := by
  intro h
  have hm : (-2 : ℝ) ∈ spectrum ℝ (generator 1) := by
    rw [generator_spectrum]; norm_num
  rw [h, generator_spectrum] at hm
  norm_num at hm

theorem transition_zero (r : ℝ) : transition r 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [transition]

theorem transition_add (r s t : ℝ) :
    transition r (s + t) = transition r s * transition r t := by
  have he : Real.exp (-2 * r * (s + t)) =
      Real.exp (-2 * r * s) * Real.exp (-2 * r * t) := by
    rw [mul_add, Real.exp_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [transition, Matrix.mul_apply, Fin.sum_univ_two] <;>
    dsimp <;> rw [he] <;> ring

theorem transition_nonnegative {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) (i j : State) :
    0 ≤ transition r t i j := by
  have hpos := Real.exp_pos (-2 * r * t)
  have hle : Real.exp (-2 * r * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg hr ht]
  fin_cases i <;> fin_cases j <;> dsimp [transition] <;> linarith

theorem transition_column_sum (r t : ℝ) (j : State) :
    ∑ i, transition r t i j = 1 := by
  fin_cases j <;> simp [transition, Fin.sum_univ_two] <;> ring

theorem transition_master (r t : ℝ) (i j : State) :
    HasDerivAt (fun s => transition r s i j) ((generator r * transition r t) i j) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-2 * r * s))
      (Real.exp (-2 * r * t) * (-2 * r)) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (-2 * r)).exp
  fin_cases i <;> fin_cases j
  all_goals
    simp only [transition, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
  · convert (hasDerivAt_const t (1 : ℝ)).add he |>.div_const 2 using 1
    simp [generator, transition, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · convert (hasDerivAt_const t (1 : ℝ)).sub he |>.div_const 2 using 1
    simp [generator, transition, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · convert (hasDerivAt_const t (1 : ℝ)).sub he |>.div_const 2 using 1
    simp [generator, transition, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · convert (hasDerivAt_const t (1 : ℝ)).add he |>.div_const 2 using 1
    simp [generator, transition, Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem flow_master (r t : ℝ) (p : Vector) (i : State) :
    HasDerivAt (fun s => (transition r s *ᵥ p) i)
      ((generator r *ᵥ (transition r t *ᵥ p)) i) t := by
  have h := ((transition_master r t i 0).mul_const (p 0)).add
    ((transition_master r t i 1).mul_const (p 1))
  rw [Matrix.mulVec_mulVec]
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h

theorem flow_probability {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) (p : Vector)
    (hp : Probability p) : Probability (transition r t *ᵥ p) := by
  constructor
  · intro i
    change 0 ≤ ∑ j, transition r t i j * p j
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (transition_nonnegative hr ht i j) (hp.1 j)
  · calc
      ∑ i, (transition r t *ᵥ p) i = ∑ j, (∑ i, transition r t i j) * p j := by
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = ∑ j, p j := by simp only [transition_column_sum, one_mul]
      _ = 1 := hp.2

theorem transition_uniform (r t : ℝ) : transition r t *ᵥ uniform = uniform := by
  ext i
  fin_cases i <;> simp [transition, uniform, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem flow_initial (r : ℝ) (p : Vector) : transition r 0 *ᵥ p = p := by
  rw [transition_zero, Matrix.one_mulVec]

theorem transition_symmetric (r t : ℝ) : (transition r t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [transition]

theorem transition_spectrum (r t mu : ℝ) :
    mu ∈ spectrum ℝ (transition r t) ↔ mu = 1 ∨ mu = Real.exp (-2 * r * t) := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  simp only [not_not]
  have hd : (algebraMap ℝ Mat mu - transition r t).det =
      (mu - 1) * (mu - Real.exp (-2 * r * t)) := by
    simp [Matrix.det_fin_two, transition, Matrix.algebraMap_eq_diagonal]
    ring
  rw [hd, mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem transitions_have_different_spectra {t : ℝ} (ht : 0 < t) :
    spectrum ℝ (transition 1 t) ≠ spectrum ℝ (transition 2 t) := by
  intro h
  have hm : Real.exp (-2 * 1 * t) ∈ spectrum ℝ (transition 1 t) := by
    rw [transition_spectrum]; exact Or.inr rfl
  rw [h, transition_spectrum] at hm
  rcases hm with hm | hm
  · have he : -2 * 1 * t = 0 := Real.exp_injective (hm.trans Real.exp_zero.symm)
    linarith
  · have he := Real.exp_injective hm
    linarith

/-- A genuine stochastic fundamental solution of the autonomous master equation. -/
def MasterSystem (Q : Mat) (P : ℝ → Mat) : Prop :=
  IsGenerator Q ∧ Q.IsHermitian ∧ P 0 = 1 ∧
  (∀ s t, P (s + t) = P s * P t) ∧
  (∀ t, 0 ≤ t → (∀ i j, 0 ≤ P t i j) ∧ ∀ j, ∑ i, P t i j = 1) ∧
  (∀ t i j, HasDerivAt (fun s => P s i j) ((Q * P t) i j) t)

theorem constructed_master_system {r : ℝ} (hr : 0 ≤ r) :
    MasterSystem (generator r) (transition r) := by
  refine ⟨generator_valid hr, generator_symmetric r, transition_zero r,
    transition_add r, ?_, transition_master r⟩
  intro t ht
  exact ⟨transition_nonnegative hr ht, transition_column_sum r t⟩

/-- The source existence claim, strengthened to distinct propagation spectra
at every positive time and detailed balance for the same probability vector. -/
def SeparationClaim : Prop :=
  ∃ (Q R : Mat) (P S : ℝ → Mat) (p : Vector),
    MasterSystem Q P ∧ MasterSystem R S ∧ Reversible Q p ∧ Reversible R p ∧
    Static Q = Static R ∧ (∀ v, Q *ᵥ v = 0 ↔ R *ᵥ v = 0) ∧
    spectrum ℝ Q ≠ spectrum ℝ R ∧
    ∀ t, 0 < t → spectrum ℝ (P t) ≠ spectrum ℝ (S t)

theorem conjecture_6640_true : SeparationClaim := by
  refine ⟨generator 1, generator 2, transition 1, transition 2, uniform,
    constructed_master_system (by norm_num), constructed_master_system (by norm_num),
    generator_reversible 1, generator_reversible 2, ?_, ?_,
    generators_have_different_spectra, ?_⟩
  · ext p
    rw [static_iff (by norm_num : (1 : ℝ) ≠ 0), static_iff (by norm_num : (2 : ℝ) ≠ 0)]
  · intro v
    rw [kernel_iff (by norm_num : (1 : ℝ) ≠ 0), kernel_iff (by norm_num : (2 : ℝ) ≠ 0)]
  · intro t ht
    exact transitions_have_different_spectra ht

#print axioms conjecture_6640_true
#print axioms flow_master
#print axioms flow_probability
#print axioms transition_spectrum

end Conjecture6640
