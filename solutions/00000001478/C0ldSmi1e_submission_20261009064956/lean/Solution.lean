import NuclearNorm
import PolynomialCone
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Disproof of conjecture 00000001478 in its stated cone formulation. -/
namespace TLMC1478

noncomputable section

/-- A genuine real polynomial map to complex 2 x 2 x 2 tensors, recorded in
real and imaginary coordinate polynomials. The source dimension is arbitrary. -/
structure TensorPolynomialMap (n : ℕ) where
  re : Fin 2 → Fin 2 → Fin 2 → MvPolynomial (Fin n) ℝ
  im : Fin 2 → Fin 2 → Fin 2 → MvPolynomial (Fin n) ℝ

/-- Evaluation uses all sixteen real coordinates of the eight complex entries. -/
noncomputable def TensorPolynomialMap.eval {n : ℕ} (P : TensorPolynomialMap n)
    (x : Fin n → ℝ) : Tensor :=
  fun i j k => ⟨MvPolynomial.eval x (P.re i j k), MvPolynomial.eval x (P.im i j k)⟩

/-- Every complex-coefficient polynomial tensor map on real parameters is
represented by `TensorPolynomialMap`; the target field is not restricted. -/
theorem complex_polynomials_represented {n : ℕ}
    (p : Fin 2 → Fin 2 → Fin 2 → MvPolynomial (Fin n) ℂ) :
    ∃ P : TensorPolynomialMap n, ∀ x : Fin n → ℝ,
      P.eval x = fun i j k => MvPolynomial.eval (fun a => (x a : ℂ)) (p i j k) := by
  classical
  choose re im h using fun i j k => PolynomialCone.exists_real_imag_polynomials (p i j k)
  refine ⟨⟨re, im⟩, ?_⟩
  intro x
  funext i j k
  apply Complex.ext
  · exact (h i j k x).1.symm
  · exact (h i j k x).2.symm

/-- Only the ordinary nonnegative-scaling closure of a cone is needed. -/
def IsCone {n : ℕ} (C : Set (Fin n → ℝ)) : Prop :=
  (0 : Fin n → ℝ) ∈ C ∧ ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → (fun i => t * x i) ∈ C

/-- Even an intermediate set containing 0 and the unit basis tensor and contained
in the nuclear ball cannot be a polynomial image of a cone. -/
theorem no_polynomial_cone_image_between {B : Set Tensor}
    (hzero : (0 : Tensor) ∈ B) (hbasis : basisTensor ∈ B)
    (hbound : B ⊆ nuclearBall) :
    ¬ ∃ (n : ℕ) (C : Set (Fin n → ℝ)) (P : TensorPolynomialMap n),
      IsCone C ∧ P.eval '' C = B := by
  rintro ⟨n, C, P, hC, himage⟩
  have hconst : ∀ x ∈ C,
      MvPolynomial.eval x (P.re 0 0 0) = MvPolynomial.eval 0 (P.re 0 0 0) := by
    apply PolynomialCone.eval_eq_eval_zero_of_bounded_on_cone C hC.2 (P.re 0 0 0) 1
    intro x hx
    have hxB : P.eval x ∈ B := himage ▸ Set.mem_image_of_mem P.eval hx
    have hnorm := nuclearBall_coordinate_bound (hbound hxB) 0 0 0
    exact (Complex.abs_re_le_norm (P.eval x 0 0 0)).trans hnorm
  obtain ⟨x, hx, hx0⟩ := himage.symm ▸ hzero
  obtain ⟨y, hy, hy1⟩ := himage.symm ▸ hbasis
  have hxy : (P.eval x 0 0 0).re = (P.eval y 0 0 0).re :=
    (hconst x hx).trans (hconst y hy).symm
  rw [hx0, hy1] at hxy
  simp at hxy

/-- The nuclear-norm unit ball of the full complex 2 x 2 x 2 tensor space
is not the polynomial image of any cone in any finite real dimension. -/
theorem nuclearBall_not_polynomial_image_of_cone :
    ¬ ∃ (n : ℕ) (C : Set (Fin n → ℝ)) (P : TensorPolynomialMap n),
      IsCone C ∧ P.eval '' C = nuclearBall :=
  no_polynomial_cone_image_between zero_mem_nuclearBall basisTensor_mem_nuclearBall
    (Set.Subset.refl _)

/-- The obstruction also holds if the word 'minimal' is interpreted literally
as an attained minimum; no assumption of global attainment is needed. -/
theorem minimumNuclearBall_not_polynomial_image_of_cone :
    ¬ ∃ (n : ℕ) (C : Set (Fin n → ℝ)) (P : TensorPolynomialMap n),
      IsCone C ∧ P.eval '' C = minimumNuclearBall :=
  no_polynomial_cone_image_between zero_mem_minimumNuclearBall
    basisTensor_mem_minimumNuclearBall minimumNuclearBall_subset

/-- A homogeneous 4 x 4 symmetric positive-semidefinite matrix inequality.
The positivity predicate includes symmetry, as in Mathlib's real PSD definition. -/
def spectrahedralCone4 {n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ) : Set (Fin n → ℝ) :=
  {x | (L x).PosSemidef}

/-- Closure under nonnegative scaling is proved from the genuine PSD predicate. -/
theorem posSemidef_smul_nonneg {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) : (t • A).PosSemidef := by
  constructor
  · change (t • A).conjTranspose = t • A
    rw [Matrix.conjTranspose_smul]
    simpa using congrArg (fun M => t • M) hA.1
  · intro v
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul]
    exact mul_nonneg ht (hA.2 v)

theorem spectrahedralCone4_isCone {n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ) :
    IsCone (spectrahedralCone4 L) := by
  constructor
  · change (L 0).PosSemidef
    simpa only [map_zero] using (Matrix.PosSemidef.zero :
      (0 : Matrix (Fin 4) (Fin 4) ℝ).PosSemidef)
  · intro x hx t ht
    change (L (t • x)).PosSemidef
    rw [map_smul]
    exact posSemidef_smul_nonneg hx ht

/-- The necessary representation clause of the original conjecture is false,
including its requested matrix dimension 4. -/
theorem nuclearBall_not_polynomial_image_of_spectrahedralCone4 :
    ¬ ∃ (n : ℕ) (L : (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ)
      (P : TensorPolynomialMap n), P.eval '' spectrahedralCone4 L = nuclearBall := by
  rintro ⟨n, L, P, h⟩
  exact nuclearBall_not_polynomial_image_of_cone
    ⟨n, spectrahedralCone4 L, P, spectrahedralCone4_isCone L, h⟩

/-- The necessary polynomial-image-of-a-cone clause in both original languages
is false. This rules out any additional specifications of that cone, including
the stated generalized 4 x 4 matrix description and the claimed SDP consequence. -/
theorem conjecture00000001478_false :
    ¬ ∃ (n : ℕ) (C : Set (Fin n → ℝ)) (P : TensorPolynomialMap n),
      IsCone C ∧ P.eval '' C = nuclearBall :=
  nuclearBall_not_polynomial_image_of_cone

end

end TLMC1478
