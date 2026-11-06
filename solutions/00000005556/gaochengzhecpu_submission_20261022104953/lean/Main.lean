import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.NormNum
import Mathlib.Data.ZMod.Basic

noncomputable section
open scoped Matrix
open Matrix Polynomial

namespace Conjecture5556

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem base_frobenius_identity : ∀ x : ZMod 3, x ^ 3 = x := by decide

/-- Over F_3, Witt Frobenius is the identity on Z_3. Thus a rank-one
    unit-root F-crystal is a free Z_3 line with a linear automorphism.
    We retain its actual extension to the Q_3 line and compatibility. -/
structure RankOneCrystal where
  integralFrob : ℤ_[3] ≃ₗ[ℤ_[3]] ℤ_[3]
  rationalFrob : ℚ_[3] ≃ₗ[ℚ_[3]] ℚ_[3]
  scalar_extension : ∀ x : ℤ_[3],
    (integralFrob x : ℚ_[3]) = rationalFrob (x : ℚ_[3])

def positiveCrystal : RankOneCrystal where
  integralFrob := LinearEquiv.refl _ _
  rationalFrob := LinearEquiv.refl _ _
  scalar_extension := fun _ => rfl

def negativeCrystal : RankOneCrystal where
  integralFrob := LinearEquiv.neg _
  rationalFrob := LinearEquiv.neg _
  scalar_extension := by intro x; simp [LinearEquiv.neg_apply]

def coefficient (C : RankOneCrystal) : ℚ_[3] := C.rationalFrob 1

/-- The standard unit-root condition, expressed in the actual p-adic field. -/
def UnitRoot (C : RankOneCrystal) : Prop :=
  ‖coefficient C‖ = 1 ∧ Padic.valuation (coefficient C) = 0

/-- Weil purity of weight zero for a rational Frobenius eigenvalue:
    every complex embedding of its number field Q has modulus one. -/
def PureWeightZero (C : RankOneCrystal) : Prop :=
  ∃ a : ℚ, coefficient C = (a : ℚ_[3]) ∧
    ∀ embedding : ℚ →+* ℂ, ‖embedding a‖ = 1

def frobeniusMatrix (C : RankOneCrystal) : Matrix (Fin 1) (Fin 1) ℚ_[3] :=
  fun _ _ => coefficient C

theorem matrix_represents_frobenius (C : RankOneCrystal) (v : Fin 1 → ℚ_[3]) :
    (frobeniusMatrix C).mulVec v = fun i => C.rationalFrob (v i) := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have h := C.rationalFrob.map_smul (v 0) (1 : ℚ_[3])
  simpa [frobeniusMatrix, coefficient, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
    smul_eq_mul, mul_comm] using h.symm

def characteristicPolynomial (C : RankOneCrystal) : ℚ_[3][X] :=
  (frobeniusMatrix C).charpoly

theorem characteristicPolynomial_formula (C : RankOneCrystal) :
    characteristicPolynomial C = X - Polynomial.C (coefficient C) := by
  simp [characteristicPolynomial, Matrix.charpoly, Matrix.det_fin_one,
    Matrix.charmatrix, Matrix.scalar, frobeniusMatrix, Matrix.diagonal]

/-- For a monic degree-one polynomial with nonzero constant coefficient,
    its lower Newton polygon is exactly the segment joining its two
    coefficient-valuation points. We use this actual geometric segment. -/
def newtonPolygon (C : RankOneCrystal) : Set (ℝ × ℝ) :=
  segment ℝ
    (0, (Padic.valuation ((characteristicPolynomial C).coeff 0) : ℝ))
    (1, (Padic.valuation ((characteristicPolynomial C).coeff 1) : ℝ))

@[simp] theorem coefficient_positive : coefficient positiveCrystal = 1 := rfl
@[simp] theorem coefficient_negative : coefficient negativeCrystal = -1 := rfl

theorem valuation_negative_one : Padic.valuation (-1 : ℚ_[3]) = 0 := by
  change Padic.valuation ((-1 : ℚ) : ℚ_[3]) = 0
  rw [Padic.valuation_ratCast, padicValRat.neg, padicValRat.one]

theorem positive_unit_root : UnitRoot positiveCrystal := by
  simp [UnitRoot]

theorem negative_unit_root : UnitRoot negativeCrystal := by
  simp [UnitRoot, valuation_negative_one]

theorem positive_pure_zero : PureWeightZero positiveCrystal := by
  refine ⟨1, by simp, ?_⟩
  intro embedding
  simp

theorem negative_pure_zero : PureWeightZero negativeCrystal := by
  refine ⟨-1, by simp, ?_⟩
  intro embedding
  simp

theorem same_newton_polygon : newtonPolygon positiveCrystal = newtonPolygon negativeCrystal := by
  simp [newtonPolygon, characteristicPolynomial_formula, valuation_negative_one, Polynomial.coeff_one]

theorem distinct_characteristic_polynomials :
    characteristicPolynomial positiveCrystal ≠ characteristicPolynomial negativeCrystal := by
  intro h
  have h0 := congrArg (fun p : ℚ_[3][X] => p.coeff 0) h
  simp [characteristicPolynomial_formula] at h0
  have htwo : (2 : ℚ_[3]) = 0 := by linear_combination -h0
  exact (by norm_num : (2 : ℚ_[3]) ≠ 0) htwo

theorem no_frobenius_conjugacy :
    ¬ ∃ f : ℚ_[3] ≃ₗ[ℚ_[3]] ℚ_[3],
      ∀ x, negativeCrystal.rationalFrob (f x) = f (positiveCrystal.rationalFrob x) := by
  rintro ⟨f, hf⟩
  have hx := hf 1
  change -(f 1) = f 1 at hx
  have htwo : (2 : ℚ_[3]) * f 1 = 0 := by linear_combination -hx
  have hzero : f 1 = 0 := (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have h10 : (1 : ℚ_[3]) = 0 := f.injective (hzero.trans f.map_zero.symm)
  exact one_ne_zero h10

def NewtonDeterminesCharacteristicPolynomial : Prop :=
  ∀ C D : RankOneCrystal, UnitRoot C → UnitRoot D →
    newtonPolygon C = newtonPolygon D →
    characteristicPolynomial C = characteristicPolynomial D

def PureWeightDeterminesCharacteristicPolynomial : Prop :=
  ∀ C D : RankOneCrystal, UnitRoot C → UnitRoot D →
    PureWeightZero C → PureWeightZero D →
    characteristicPolynomial C = characteristicPolynomial D

theorem not_newton_determines_characteristic_polynomial :
    ¬ NewtonDeterminesCharacteristicPolynomial := by
  intro h
  exact distinct_characteristic_polynomials
    (h positiveCrystal negativeCrystal positive_unit_root negative_unit_root same_newton_polygon)

theorem not_pure_weight_determines_characteristic_polynomial :
    ¬ PureWeightDeterminesCharacteristicPolynomial := by
  intro h
  exact distinct_characteristic_polynomials
    (h positiveCrystal negativeCrystal positive_unit_root negative_unit_root
      positive_pure_zero negative_pure_zero)

#print axioms matrix_represents_frobenius
#print axioms positive_unit_root
#print axioms negative_unit_root
#print axioms same_newton_polygon
#print axioms distinct_characteristic_polynomials
#print axioms no_frobenius_conjugacy
#print axioms not_newton_determines_characteristic_polynomial
#print axioms not_pure_weight_determines_characteristic_polynomial

end Conjecture5556
