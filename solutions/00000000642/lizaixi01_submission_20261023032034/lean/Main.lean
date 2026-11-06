import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace TLMC642
open Matrix
set_option maxRecDepth 2000

/-- The actual rational function field in the two independent LKB variables. -/
abbrev Polys := MvPolynomial (Fin 2) ℚ
abbrev K := FractionRing Polys
noncomputable def q : K := algebraMap Polys K (MvPolynomial.X 0)
noncomputable def t : K := algebraMap Polys K (MvPolynomial.X 1)

lemma q_ne_zero : q ≠ 0 := by
  intro h
  apply MvPolynomial.X_ne_zero (R := ℚ) (0 : Fin 2)
  apply IsFractionRing.injective Polys K
  exact h.trans (map_zero (algebraMap Polys K)).symm

lemma t_ne_zero : t ≠ 0 := by
  intro h
  apply MvPolynomial.X_ne_zero (R := ℚ) (1 : Fin 2)
  apply IsFractionRing.injective Polys K
  exact h.trans (map_zero (algebraMap Polys K)).symm

lemma determinant_factor_ne_one : t * q ^ 3 ≠ 1 := by
  intro h
  have h' : algebraMap Polys K (MvPolynomial.X 1 * MvPolynomial.X 0 ^ 3) =
      algebraMap Polys K 1 := by simpa [q,t] using h
  have hp := IsFractionRing.injective Polys K h'
  have he := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℚ))) hp
  norm_num at he

/-- Standard Artin presentations for two and three strands. -/
abbrev Braid2 := FreeGroup (Fin 1)
def braidRelator : FreeGroup (Fin 2) :=
  (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0) *
    (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹
abbrev Braid3 := PresentedGroup ({braidRelator} : Set (FreeGroup (Fin 2)))
def sigma (i : Fin 2) : Braid3 := PresentedGroup.of i

/-- Adding the third straight strand fixes the first Artin generator. -/
def include23 : Braid2 →* Braid3 := FreeGroup.lift (fun _ => sigma 0)
lemma include_generator : include23 (FreeGroup.of (0 : Fin 1)) = sigma 0 := by
  simp [include23]

/-- The positive elementary Markov stabilization, not merely conjugation. -/
def stabilize (b : Braid2) : Braid3 := include23 b * sigma 1
def PositiveStabilization (b : Braid2) (c : Braid3) : Prop := c = stabilize b

lemma identity_stabilizes : PositiveStabilization 1 (sigma 1) := by
  simp [PositiveStabilization,stabilize]

/-- Bigelow, Section 4.2, with ordered basis F12,F13,F23 and his sign of t. -/
noncomputable def matrixA (q t : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-t*q^2, 0, q^2-q; 0, 0, q; 0, 1, 1-q]
noncomputable def matrixB (q t : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, q, 0; 1, 1-q, 0; 0, (1-q)*q*t, -t*q^2]
noncomputable def matrix2 (q t : K) : Matrix (Fin 1) (Fin 1) K := fun _ _ => -t*q^2

lemma matrixA_det (q t : K) : (matrixA q t).det = t*q^3 := by
  simp [matrixA,Matrix.det_fin_three]
  ring
lemma matrixB_det (q t : K) : (matrixB q t).det = t*q^3 := by
  simp [matrixB,Matrix.det_fin_three]
  ring
lemma matrix2_det (q t : K) : (matrix2 q t).det = -t*q^2 := by
  simp [matrix2]

lemma braid_relation (q t : K) :
    matrixA q t * matrixB q t * matrixA q t =
      matrixB q t * matrixA q t * matrixB q t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixA,matrixB,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

noncomputable def AU : GeneralLinearGroup (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero (matrixA q t) (by
    rw [matrixA_det]; exact mul_ne_zero t_ne_zero (pow_ne_zero _ q_ne_zero))
noncomputable def BU : GeneralLinearGroup (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero (matrixB q t) (by
    rw [matrixB_det]; exact mul_ne_zero t_ne_zero (pow_ne_zero _ q_ne_zero))
noncomputable def U2 : GeneralLinearGroup (Fin 1) K :=
  GeneralLinearGroup.mkOfDetNeZero (matrix2 q t) (by
    rw [matrix2_det]; exact mul_ne_zero (neg_ne_zero.mpr t_ne_zero) (pow_ne_zero _ q_ne_zero))
noncomputable def generators3 (i : Fin 2) : GeneralLinearGroup (Fin 3) K :=
  if i=0 then AU else BU

lemma relator_valid :
    ∀ r ∈ ({braidRelator} : Set (FreeGroup (Fin 2))), FreeGroup.lift generators3 r=1 := by
  have h : AU*BU*AU=BU*AU*BU := by
    apply Units.ext
    simpa [GeneralLinearGroup.coe_mul,AU,BU] using braid_relation q t
  rintro r hr
  rw [Set.mem_singleton_iff] at hr
  subst r
  simp [braidRelator,generators3,h]

/-- Actual standard matrix representations, constructed by the Artin universal property. -/
noncomputable def krammer2 : Braid2 →* GeneralLinearGroup (Fin 1) K :=
  FreeGroup.lift (fun _ => U2)
noncomputable def krammer3 : Braid3 →* GeneralLinearGroup (Fin 3) K :=
  PresentedGroup.toGroup relator_valid

lemma generator2_image : krammer2 (FreeGroup.of (0 : Fin 1)) = U2 := by
  simp [krammer2]
lemma generator3_one_image : krammer3 (sigma 0) = AU := by
  simp [krammer3,sigma,PresentedGroup.toGroup.of,generators3]
lemma generator3_two_image : krammer3 (sigma 1) = BU := by
  simp [krammer3,sigma,PresentedGroup.toGroup.of,generators3]

noncomputable def determinant2 (b : Braid2) : K :=
  (↑(krammer2 b) : Matrix (Fin 1) (Fin 1) K).det
noncomputable def determinant3 (b : Braid3) : K :=
  (↑(krammer3 b) : Matrix (Fin 3) (Fin 3) K).det

lemma identity_determinant : determinant2 1 = 1 := by
  simp [determinant2]
lemma stabilization_determinant : determinant3 (stabilize 1) = t*q^3 := by
  simp [stabilize,determinant3,generator3_two_image,BU,matrixB_det]

theorem raw_determinant_changes : determinant2 1 ≠ determinant3 (stabilize 1) := by
  rw [identity_determinant,stabilization_determinant]
  exact Ne.symm determinant_factor_ne_one

/-- The literal determinant-level Markov invariance fails on an elementary move. -/
theorem not_positive_markov_invariant :
    ¬ ∀ (b : Braid2) (c : Braid3), PositiveStabilization b c →
      determinant2 b = determinant3 c := by
  intro h
  exact raw_determinant_changes (h 1 (stabilize 1) rfl)

/-- Determinants do not depend on the particular matrix bases of either representation. -/
lemma conjugation_determinant {n : ℕ} (P : GeneralLinearGroup (Fin n) K)
    (M : Matrix (Fin n) (Fin n) K) :
    ((↑P : Matrix (Fin n) (Fin n) K) * M * (↑(P⁻¹) : Matrix (Fin n) (Fin n) K)).det = M.det := by
  have h : (↑P : Matrix (Fin n) (Fin n) K).det *
      (↑(P⁻¹) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← Matrix.det_mul]
    simp
  rw [Matrix.det_mul,Matrix.det_mul]
  calc
    (↑P : Matrix (Fin n) (Fin n) K).det * M.det * (↑(P⁻¹) : Matrix (Fin n) (Fin n) K).det =
        ((↑P : Matrix (Fin n) (Fin n) K).det * (↑(P⁻¹) : Matrix (Fin n) (Fin n) K).det) * M.det := by ring
    _ = M.det := by rw [h,one_mul]

theorem determinant_changes_in_any_bases
    (P : GeneralLinearGroup (Fin 1) K) (Q : GeneralLinearGroup (Fin 3) K) :
    ((↑P : Matrix (Fin 1) (Fin 1) K) * (↑(krammer2 1) : Matrix (Fin 1) (Fin 1) K) * (↑(P⁻¹) : Matrix (Fin 1) (Fin 1) K)).det ≠
      ((↑Q : Matrix (Fin 3) (Fin 3) K) * (↑(krammer3 (stabilize 1)) : Matrix (Fin 3) (Fin 3) K) * (↑(Q⁻¹) : Matrix (Fin 3) (Fin 3) K)).det := by
  simp only [conjugation_determinant]
  exact raw_determinant_changes

end TLMC642
