import TraceTriangle
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis

namespace Quasitrace918

open scoped ComplexOrder

noncomputable instance matrixBaseOrder : PartialOrder A := CStarAlgebra.spectralOrder A

instance matrixBaseStarOrdered : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

-- CStarMatrix carries the operator C*-norm, unlike the raw Matrix norm.
abbrev MatrixA := CStarMatrix (Fin 2) (Fin 2) A

instance matrixA_complex_finite : FiniteDimensional ℂ MatrixA :=
  Module.Finite.equiv (CStarMatrix.ofMatrixₗ (m := Fin 2) (n := Fin 2) (A := A) (R := ℂ))

@[instance_reducible]
noncomputable def matrixA_cstar : CStarAlgebra MatrixA := inferInstance

noncomputable def matrixCoordinateLinear (i : Fin 3) : MatrixA →ₗ[ℂ] ℂ :=
  (coordinate i).toLinearMap.comp
    ((Matrix.traceLinearMap (Fin 2) ℂ A).comp
      (CStarMatrix.ofMatrixₗ (m := Fin 2) (n := Fin 2) (A := A) (R := ℂ)).symm.toLinearMap)

noncomputable def matrixCoordinate (i : Fin 3) : MatrixA →L[ℂ] ℂ where
  toLinearMap := matrixCoordinateLinear i
  cont := (matrixCoordinateLinear i).continuous_of_finiteDimensional

def matrixCorner (a : A) : MatrixA :=
  CStarMatrix.ofMatrix (Matrix.single (0 : Fin 2) (0 : Fin 2) a)

noncomputable def matrixCoordinateEntries (i : Fin 3) (X : MatrixA) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun r s => coordinate i (X r s)

theorem matrixCoordinate_apply (i : Fin 3) (X : MatrixA) :
    matrixCoordinate i X = coordinate i (X 0 0) + coordinate i (X 1 1) := by
  simp [matrixCoordinate, matrixCoordinateLinear, Matrix.trace, Fin.sum_univ_two]
  rfl

theorem matrixCoordinate_trace (i : Fin 3) (X : MatrixA) :
    matrixCoordinate i X = Matrix.trace (matrixCoordinateEntries i X) := by
  simp only [matrixCoordinate_apply, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
    matrixCoordinateEntries]

theorem matrixCoordinate_add (i : Fin 3) (X Y : MatrixA) :
    matrixCoordinate i (X + Y) = matrixCoordinate i X + matrixCoordinate i Y :=
  (matrixCoordinate i).map_add X Y

theorem matrixCoordinate_smul (i : Fin 3) (c : ℂ) (X : MatrixA) :
    matrixCoordinate i (c • X) = c * matrixCoordinate i X :=
  (matrixCoordinate i).map_smul c X

theorem matrixCoordinate_continuous (i : Fin 3) : Continuous (matrixCoordinate i) :=
  (matrixCoordinate i).continuous

theorem matrixCoordinate_star (i : Fin 3) (X : MatrixA) :
    matrixCoordinate i (star X) = star (matrixCoordinate i X) := by
  simp only [matrixCoordinate_apply, CStarMatrix.star_apply, coordinate_star, star_add]

theorem matrixCoordinate_tracial (i : Fin 3) (X Y : MatrixA) :
    matrixCoordinate i (X * Y) = matrixCoordinate i (Y * X) := by
  simp only [matrixCoordinate_apply, CStarMatrix.mul_apply, Fin.sum_univ_two,
    coordinate_add, coordinate_mul]
  ring

theorem matrixCoordinate_star_square (i : Fin 3) (X : MatrixA) :
    matrixCoordinate i (star X * X) =
      (star (coordinate i (X 0 0)) * coordinate i (X 0 0) +
       star (coordinate i (X 1 0)) * coordinate i (X 1 0)) +
      (star (coordinate i (X 0 1)) * coordinate i (X 0 1) +
       star (coordinate i (X 1 1)) * coordinate i (X 1 1)) := by
  simp only [matrixCoordinate_apply, CStarMatrix.mul_apply, Fin.sum_univ_two,
    coordinate_add, coordinate_mul, CStarMatrix.star_apply, coordinate_star]

theorem matrixCoordinate_positive (i : Fin 3) (X : MatrixA) :
    0 ≤ matrixCoordinate i (star X * X) := by
  rw [matrixCoordinate_star_square]
  exact add_nonneg
    (add_nonneg (star_mul_self_nonneg _) (star_mul_self_nonneg _))
    (add_nonneg (star_mul_self_nonneg _) (star_mul_self_nonneg _))

theorem matrixCoordinate_normSq (i : Fin 3) (X : MatrixA) :
    (matrixCoordinate i (star X * X)).re =
      (Complex.normSq (coordinate i (X 0 0)) + Complex.normSq (coordinate i (X 1 0))) +
      (Complex.normSq (coordinate i (X 0 1)) + Complex.normSq (coordinate i (X 1 1))) := by
  rw [matrixCoordinate_star_square]
  simp [Complex.normSq, Complex.mul_re]

theorem matrixCoordinate_star_square_imag (i : Fin 3) (X : MatrixA) :
    (matrixCoordinate i (star X * X)).im = 0 := by
  rw [matrixCoordinate_star_square]
  simp [Complex.mul_im]
  ring

theorem matrixCoordinate_cyclic_star_square (i : Fin 3) (X : MatrixA) :
    matrixCoordinate i (star X * X) = matrixCoordinate i (X * star X) :=
  matrixCoordinate_tracial i (star X) X

theorem matrixCoordinate_isSelfAdjoint (i : Fin 3) (X : MatrixA) (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (matrixCoordinate i X) := by
  change star (matrixCoordinate i X) = matrixCoordinate i X
  rw [← matrixCoordinate_star, hX.star_eq]

theorem matrixCoordinate_one (i : Fin 3) : matrixCoordinate i 1 = 2 := by
  simp only [matrixCoordinate_apply, CStarMatrix.one_apply_eq, coordinate_one]
  norm_num

theorem matrixCoordinate_corner (i : Fin 3) (a : A) :
    matrixCoordinate i (matrixCorner a) = coordinate i a := by
  simp [matrixCoordinate_apply, matrixCorner, coordinate_apply]

theorem matrixCorner_add (a b : A) : matrixCorner (a + b) = matrixCorner a + matrixCorner b := by
  apply CStarMatrix.ext
  intro r s
  fin_cases r <;> fin_cases s <;> simp [matrixCorner]

theorem matrixCorner_smul (c : ℂ) (a : A) : matrixCorner (c • a) = c • matrixCorner a := by
  apply CStarMatrix.ext
  intro r s
  simp [matrixCorner, Matrix.single_apply, CStarMatrix.smul_apply]

end Quasitrace918

#print Quasitrace918.MatrixA
#print axioms Quasitrace918.MatrixA
#print Quasitrace918.matrixBaseOrder
#print axioms Quasitrace918.matrixBaseOrder
#print Quasitrace918.matrixBaseStarOrdered
#print axioms Quasitrace918.matrixBaseStarOrdered
#print Quasitrace918.matrixA_complex_finite
#print axioms Quasitrace918.matrixA_complex_finite
#print Quasitrace918.matrixA_cstar
#print axioms Quasitrace918.matrixA_cstar
#print Quasitrace918.matrixCoordinateLinear
#print axioms Quasitrace918.matrixCoordinateLinear
#print Quasitrace918.matrixCoordinate
#print axioms Quasitrace918.matrixCoordinate
#print Quasitrace918.matrixCorner
#print axioms Quasitrace918.matrixCorner
#print Quasitrace918.matrixCoordinateEntries
#print axioms Quasitrace918.matrixCoordinateEntries
#check @Quasitrace918.matrixCoordinate_apply
#print axioms Quasitrace918.matrixCoordinate_apply
#check @Quasitrace918.matrixCoordinate_trace
#print axioms Quasitrace918.matrixCoordinate_trace
#check @Quasitrace918.matrixCoordinate_add
#print axioms Quasitrace918.matrixCoordinate_add
#check @Quasitrace918.matrixCoordinate_smul
#print axioms Quasitrace918.matrixCoordinate_smul
#check @Quasitrace918.matrixCoordinate_continuous
#print axioms Quasitrace918.matrixCoordinate_continuous
#check @Quasitrace918.matrixCoordinate_star
#print axioms Quasitrace918.matrixCoordinate_star
#check @Quasitrace918.matrixCoordinate_tracial
#print axioms Quasitrace918.matrixCoordinate_tracial
#check @Quasitrace918.matrixCoordinate_star_square
#print axioms Quasitrace918.matrixCoordinate_star_square
#check @Quasitrace918.matrixCoordinate_positive
#print axioms Quasitrace918.matrixCoordinate_positive
#check @Quasitrace918.matrixCoordinate_normSq
#print axioms Quasitrace918.matrixCoordinate_normSq
#check @Quasitrace918.matrixCoordinate_star_square_imag
#print axioms Quasitrace918.matrixCoordinate_star_square_imag
#check @Quasitrace918.matrixCoordinate_cyclic_star_square
#print axioms Quasitrace918.matrixCoordinate_cyclic_star_square
#check @Quasitrace918.matrixCoordinate_isSelfAdjoint
#print axioms Quasitrace918.matrixCoordinate_isSelfAdjoint
#check @Quasitrace918.matrixCoordinate_one
#print axioms Quasitrace918.matrixCoordinate_one
#check @Quasitrace918.matrixCoordinate_corner
#print axioms Quasitrace918.matrixCoordinate_corner
#check @Quasitrace918.matrixCorner_add
#print axioms Quasitrace918.matrixCorner_add
#check @Quasitrace918.matrixCorner_smul
#print axioms Quasitrace918.matrixCorner_smul
