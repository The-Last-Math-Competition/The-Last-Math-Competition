import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Filter Topology Function NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace TLMC2692

/-- The usual basin of the fixed point a, defined by actual iterates and convergence. -/
def basin {A : Type*} [TopologicalSpace A] (f : A → A) (a : A) : Set A :=
  {x | Tendsto (fun n : ℕ => f^[n] x) atTop (𝓝 a)}

section Ring
variable {R : Type*} [NormedRing R]

def mulMap (a : R) : R → R := fun x => a * x

theorem iterate_mulMap (a x : R) (n : ℕ) : (mulMap a)^[n] x = a ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', mulMap, ih, pow_succ', mul_assoc]

theorem mulMap_lipschitz (a : R) : LipschitzWith ‖a‖₊ (mulMap a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [mulMap, dist_eq_norm, ← mul_sub, coe_nnnorm] using norm_mul_le a (x-y)

theorem mulMap_contracting (a : R) (ha : ‖a‖ < 1) :
    ContractingWith ‖a‖₊ (mulMap a) :=
  ⟨by exact_mod_cast ha, mulMap_lipschitz a⟩

theorem iterate_tendsto_zero (a : R) (ha : ‖a‖ < 1) (x : R) :
    Tendsto (fun n : ℕ => (mulMap a)^[n] x) atTop (𝓝 0) := by
  simpa only [iterate_mulMap, zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ha).mul_const x

theorem basin_mulMap (a : R) (ha : ‖a‖ < 1) : basin (mulMap a) 0 = univ := by
  ext x
  simp only [basin, mem_ofPred_eq, mem_univ, iff_true]
  exact iterate_tendsto_zero a ha x

variable [NormOneClass R]

theorem periodic_mulMap_iff (a : R) (ha : ‖a‖ < 1) (x : R) :
    x ∈ periodicPts (mulMap a) ↔ x = 0 := by
  constructor
  · rintro ⟨n, hn, hp⟩
    have hfix : a ^ n * x = x := by simpa only [IsPeriodicPt, IsFixedPt, iterate_mulMap] using hp
    have hle : ‖x‖ ≤ ‖a‖ ^ n * ‖x‖ := by
      calc
        ‖x‖ = ‖a ^ n * x‖ := congrArg norm hfix.symm
        _ ≤ ‖a ^ n‖ * ‖x‖ := norm_mul_le _ _
        _ ≤ ‖a‖ ^ n * ‖x‖ := mul_le_mul_of_nonneg_right (norm_pow_le a n) (norm_nonneg x)
    have hlt : ‖a‖ ^ n < 1 := pow_lt_one₀ (norm_nonneg a) ha (Nat.ne_of_gt hn)
    by_contra hx
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    nlinarith
  · rintro rfl
    exact ⟨1, by decide, by simp [IsPeriodicPt, IsFixedPt, mulMap]⟩

theorem periodic_mulMap (a : R) (ha : ‖a‖ < 1) :
    periodicPts (mulMap a) = {0} := by
  ext x
  simpa using periodic_mulMap_iff a ha x

omit [NormOneClass R] in
theorem boundary_mulMap (a : R) (ha : ‖a‖ < 1) :
    frontier (basin (mulMap a) 0) = ∅ := by
  rw [basin_mulMap a ha, frontier_univ]

theorem periodic_closure_mulMap (a : R) (ha : ‖a‖ < 1) :
    closure (periodicPts (mulMap a)) = {0} := by
  rw [periodic_mulMap a ha, closure_singleton]

theorem boundary_ne_periodic_closure (a : R) (ha : ‖a‖ < 1) :
    frontier (basin (mulMap a) 0) ≠ closure (periodicPts (mulMap a)) := by
  rw [boundary_mulMap a ha, periodic_closure_mulMap a ha]
  exact (singleton_ne_empty 0).symm
end Ring

instance prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Q5 := ℚ_[5]
abbrev Z5 := ℤ_[5]

def fieldMap : Q5 → Q5 := mulMap 5
def integerMap : Z5 → Z5 := mulMap 5

def fieldPolynomial : Polynomial Q5 := Polynomial.C 5 * Polynomial.X

theorem fieldPolynomial_eval (x : Q5) : fieldPolynomial.eval x = fieldMap x := by
  simp [fieldPolynomial, fieldMap, mulMap]

theorem field_derivative (x : Q5) : HasDerivAt fieldMap 5 x := by
  exact hasDerivAt_const_mul 5

theorem field_multiplier_nonzero : (5 : Q5) ≠ 0 := by norm_num

theorem field_multiplier_norm : ‖(5 : Q5)‖ = (1 / 5 : ℝ) := by
  simpa using (Padic.norm_p (p := 5))

theorem field_multiplier_attracting : ‖(5 : Q5)‖ < 1 := by
  rw [field_multiplier_norm]
  norm_num

theorem integer_multiplier_attracting : ‖(5 : Z5)‖ < 1 := by
  change ‖((5 : ℕ) : Z5)‖ < 1
  rw [PadicInt.norm_p (p := 5)]
  norm_num

theorem field_contracting : ContractingWith ‖(5 : Q5)‖₊ fieldMap :=
  mulMap_contracting 5 field_multiplier_attracting

theorem integer_contracting : ContractingWith ‖(5 : Z5)‖₊ integerMap :=
  mulMap_contracting 5 integer_multiplier_attracting

theorem field_basin : basin fieldMap 0 = univ :=
  basin_mulMap 5 field_multiplier_attracting

theorem integer_basin : basin integerMap 0 = univ :=
  basin_mulMap 5 integer_multiplier_attracting

theorem field_periodic : periodicPts fieldMap = {0} :=
  periodic_mulMap 5 field_multiplier_attracting

theorem integer_periodic : periodicPts integerMap = {0} :=
  periodic_mulMap 5 integer_multiplier_attracting

theorem field_counterexample :
    ContractingWith ‖(5 : Q5)‖₊ fieldMap ∧
    frontier (basin fieldMap 0) ≠ closure (periodicPts fieldMap) :=
  ⟨field_contracting, boundary_ne_periodic_closure 5 field_multiplier_attracting⟩

theorem integer_counterexample :
    ContractingWith ‖(5 : Z5)‖₊ integerMap ∧
    frontier (basin integerMap 0) ≠ closure (periodicPts integerMap) :=
  ⟨integer_contracting, boundary_ne_periodic_closure 5 integer_multiplier_attracting⟩

theorem no_universal_boundary_law :
    ¬ (∀ (f : Z5 → Z5) (K : ℝ≥0), ContractingWith K f → IsFixedPt f 0 →
      frontier (basin f 0) = closure (periodicPts f)) := by
  intro h
  exact integer_counterexample.2 (h integerMap _ integer_contracting (by simp [integerMap, mulMap, IsFixedPt]))

/-- The two maps commute with the actual inclusion of the p-adic unit ball. -/
theorem inclusion_commutes (x : Z5) : (integerMap x : Q5) = fieldMap (x : Q5) := by
  change ((5 : Z5) : Q5) * (x : Q5) = (5 : Q5) * (x : Q5)
  congr 1

def inclusion : Z5 → Q5 := fun z => z

def unitBall : Set Q5 := Metric.closedBall 0 1

theorem integer_image_basin :
    inclusion '' basin integerMap (0 : Z5) = unitBall := by
  rw [integer_basin]
  ext x
  simp only [mem_image, mem_univ, true_and, unitBall, Metric.mem_closedBall, dist_zero_right, inclusion]
  constructor
  · rintro ⟨z, rfl⟩
    exact z.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem unitBall_clopen : IsClopen unitBall :=
  IsUltrametricDist.isClopen_closedBall 0 (by norm_num)

theorem ambient_integer_basin_boundary :
    frontier (inclusion '' basin integerMap (0 : Z5)) = ∅ := by
  rw [integer_image_basin]
  exact isClopen_iff_frontier_eq_empty.mp unitBall_clopen

theorem ambient_integer_periodic_closure :
    closure (inclusion '' periodicPts integerMap) = {0} := by
  rw [integer_periodic]
  simp [inclusion]

theorem ambient_integer_counterexample :
    frontier (inclusion '' basin integerMap (0 : Z5)) ≠
      closure (inclusion '' periodicPts integerMap) := by
  rw [ambient_integer_basin_boundary, ambient_integer_periodic_closure]
  exact (singleton_ne_empty 0).symm

/-- No measure or ball-volume convention is needed to falsify the boundary clause.
The actual basin also has exactly the mass of the whole unit-ball phase space. -/
theorem integer_basin_measure [MeasurableSpace Z5] (μ : MeasureTheory.Measure Z5) :
    μ (basin integerMap 0) = μ univ := by rw [integer_basin]

end TLMC2692
