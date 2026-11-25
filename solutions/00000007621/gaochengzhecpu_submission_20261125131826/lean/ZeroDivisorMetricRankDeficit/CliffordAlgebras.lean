/-
Copyright (c) 2026 The Last Math Competition Authors. All rights reserved.
 Exact zero-divisor classification for nondegenerate Clifford & matrix algebras
 Cl_{0,1}(K), Cl_{1,0}(K), Cl_{0,2}(K), Cl_{1,1}(K), and M_2(K) (all with metric nullity r = 0).
-/
import ZeroDivisorMetricRankDeficit.CliffordStep

namespace ZeroDivisorMetricRankDeficit

open AssocInvolAlg

/-!
## 1. Scalar Action & Norm-Conjugation Lemma on Commutative Base Steps

Both `Cl_{0,1}(K)` (`e₁² = -1`) and `Cl_{1,0}(K)` (`e₁² = +1`) are commutative `K`-algebras
whose involution `invl (a, b) = (a, -b)` satisfies `z * invl z = (N(z), 0)`.
Applying one further `.neg` Clifford step yields `Cl_{0,2}(K) ≅ ℍ_K` and `Cl_{1,1}(K) ≅ M₂(K)`
simultaneously via quaternion-type conjugation `(z, w) ↦ (invl z, -w)`.
-/

section HelperFieldIdentities

variable {K : Type u} [FieldOps K]

theorem field_add_add_add_comm (a b c d : K) : (a + b) + (c + d) = (a + c) + (b + d) :=
  (FieldOps.toAssocInvolAlg K).add_add_add_comm a b c d

theorem field_diff_sq (a b : K) : (a - b) * (a + b) = a * a - b * b := by
  rw [FieldOps.sub_eq_add_neg, FieldOps.right_distrib, FieldOps.left_distrib, FieldOps.left_distrib]
  rw [FieldOps.neg_mul, FieldOps.neg_mul]
  calc
    (a * a + a * b) + (-(b * a) + -(b * b))
      = a * a + (a * b + (-(a * b) + -(b * b))) := by
          rw [FieldOps.mul_comm b a, FieldOps.add_assoc (a * a)]
    _ = a * a + ((a * b + -(a * b)) + -(b * b)) := by
          rw [← FieldOps.add_assoc (a * b)]
    _ = a * a + (0 + -(b * b)) := by rw [FieldOps.add_neg_cancel]
    _ = a * a - b * b := by rw [FieldOps.zero_add, ← FieldOps.sub_eq_add_neg]

theorem field_sq_sub_sq_eq_zero_iff (a b : K) :
    a * a - b * b = 0 ↔ a = b ∨ a = -b := by
  rw [← field_diff_sq, FieldOps.mul_eq_zero, FieldOps.sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      apply FieldOps.add_right_cancel (c := b)
      rw [h, FieldOps.neg_add_cancel]
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (FieldOps.neg_add_cancel b)

end HelperFieldIdentities

/-!
## 2. `Cl_{0,1}(K)` (`n = 1, p = 0, q = 1, r = 0`, `Q(x) = -x²`)
-/

/-- `Cl_{0,1}(K)` with `e₁² = -1` (for `K = ℝ`, `Cl_{0,1}(ℝ) ≅ ℂ`). -/
def cl01Alg (K : Type u) [FieldOps K] : AssocInvolAlg (K × K) :=
  (FieldOps.toAssocInvolAlg K).cliffordStep .neg

/-- Squared norm `N(a + b e₁) = a² + b²` on `Cl_{0,1}(K)`. -/
def cl01NormSq {K : Type u} [FieldOps K] (z : K × K) : K :=
  z.1 * z.1 + z.2 * z.2

theorem cl01_mul_eq {K : Type u} [FieldOps K] (z w : K × K) :
    (cl01Alg K).mul z w = (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1) := by
  apply Prod.ext
  · dsimp only [cl01Alg, cliffordStep, signAct, FieldOps.toAssocInvolAlg]
    rw [FieldOps.sub_eq_add_neg]
  · rfl

theorem cl01_mul_comm {K : Type u} [FieldOps K] (z w : K × K) :
    (cl01Alg K).mul z w = (cl01Alg K).mul w z := by
  rw [cl01_mul_eq, cl01_mul_eq]
  apply Prod.ext <;> dsimp only
  · rw [FieldOps.mul_comm z.1 w.1, FieldOps.mul_comm z.2 w.2]
  · rw [FieldOps.mul_comm z.1 w.2, FieldOps.mul_comm z.2 w.1, FieldOps.add_comm]

theorem cl01_mul_invl {K : Type u} [FieldOps K] (z : K × K) :
    (cl01Alg K).mul z ((cl01Alg K).invl z) = (cl01NormSq z, 0) := by
  rw [cl01_mul_eq]
  dsimp only [cl01Alg, cliffordStep, FieldOps.toAssocInvolAlg, cl01NormSq]
  apply Prod.ext <;> dsimp only
  · rw [FieldOps.mul_neg, FieldOps.sub_eq_add_neg, FieldOps.neg_neg]
  · rw [FieldOps.mul_neg, FieldOps.mul_comm z.2 z.1, FieldOps.neg_add_cancel]

theorem cl01_scalar_mul {K : Type u} [FieldOps K] (s : K) (z : K × K) :
    (cl01Alg K).mul (s, 0) z = (s * z.1, s * z.2) := by
  rw [cl01_mul_eq]
  apply Prod.ext <;> dsimp only
  · rw [FieldOps.zero_mul, FieldOps.sub_zero]
  · rw [FieldOps.zero_mul, FieldOps.add_zero]

theorem cl01_hasTwoSidedInv_of_normSq_ne_zero {K : Type u} [FieldOps K] {z : K × K}
    (hN : cl01NormSq z ≠ 0) :
    HasTwoSidedInv (cl01Alg K).one (cl01Alg K).mul z := by
  let sInv : K := (cl01NormSq z)⁻¹
  let zInv : K × K := (cl01Alg K).mul (sInv, 0) ((cl01Alg K).invl z)
  refine ⟨zInv, ?_, ?_⟩
  · dsimp only [zInv]
    rw [cl01_mul_comm (sInv, 0), ← (cl01Alg K).mul_assoc, cl01_mul_invl,
        cl01_mul_comm (cl01NormSq z, 0), cl01_scalar_mul]
    apply Prod.ext <;> dsimp only [cl01Alg, cliffordStep, FieldOps.toAssocInvolAlg]
    · exact FieldOps.inv_mul_cancel hN
    · exact FieldOps.mul_zero sInv
  · dsimp only [zInv]
    rw [(cl01Alg K).mul_assoc, cl01_mul_comm ((cl01Alg K).invl z) z, cl01_mul_invl,
        cl01_scalar_mul]
    apply Prod.ext <;> dsimp only [cl01Alg, cliffordStep, FieldOps.toAssocInvolAlg]
    · exact FieldOps.inv_mul_cancel hN
    · exact FieldOps.mul_zero sInv

/-- Hypothesis that `x² + y² = 0 → x = 0 ∧ y = 0` (holds for `ℝ`, `ℚ`, and `𝔽_q` with `q ≡ 3 mod 4`). -/
def IsTwoSqAnisotropic (K : Type u) [FieldOps K] : Prop :=
  ∀ a b : K, a * a + b * b = 0 → a = 0 ∧ b = 0

/--
**Division Algebra Classification of `Cl_{0,1}(K)` (`n = 1, r = 0`):**
Whenever `-1` is not a square (`IsTwoSqAnisotropic K`), `Z(Cl_{0,1}(K)) = {(0, 0)}`
has dimension `0`.
-/
theorem cl01_isZeroDivisor_iff {K : Type u} [FieldOps K] (hAniso : IsTwoSqAnisotropic K)
    (z : K × K) :
    IsZeroDivisor (cl01Alg K).zero (cl01Alg K).mul z ↔ z = (0, 0) := by
  constructor
  · intro hZD
    by_cases hN : cl01NormSq z = 0
    · rcases hAniso z.1 z.2 hN with ⟨h1, h2⟩
      exact Prod.ext h1 h2
    · exfalso
      exact (cl01Alg K).not_isZeroDivisor_of_inv (cl01_hasTwoSidedInv_of_normSq_ne_zero hN) hZD
  · rintro rfl
    exact (cl01Alg K).zero_isZeroDivisor

theorem cl01_dichotomy {K : Type u} [FieldOps K] (hAniso : IsTwoSqAnisotropic K) :
    HasDichotomy (cl01Alg K) := by
  intro z
  by_cases hN : cl01NormSq z = 0
  · rcases hAniso z.1 z.2 hN with ⟨h1, h2⟩
    have hz : z = (0, 0) := Prod.ext h1 h2
    rw [hz]
    exact Or.inl (cl01Alg K).zero_isZeroDivisor
  · exact Or.inr (cl01_hasTwoSidedInv_of_normSq_ne_zero hN)

/-!
## 3. `Cl_{1,0}(K)` (`n = 1, p = 1, q = 0, r = 0`, `Q(x) = +x²`)
-/

/-- `Cl_{1,0}(K)` with `e₁² = +1` (for `K = ℝ`, `Cl_{1,0}(ℝ) ≅ ℝ ⊕ ℝ`). -/
def cl10Alg (K : Type u) [FieldOps K] : AssocInvolAlg (K × K) :=
  (FieldOps.toAssocInvolAlg K).cliffordStep .pos

/-- Split norm `N(a + b e₁) = a² - b²` on `Cl_{1,0}(K)`. -/
def cl10NormDiff {K : Type u} [FieldOps K] (z : K × K) : K :=
  z.1 * z.1 - z.2 * z.2

theorem cl10_mul_eq {K : Type u} [FieldOps K] (z w : K × K) :
    (cl10Alg K).mul z w = (z.1 * w.1 + z.2 * w.2, z.1 * w.2 + z.2 * w.1) := rfl

theorem cl10_mul_comm {K : Type u} [FieldOps K] (z w : K × K) :
    (cl10Alg K).mul z w = (cl10Alg K).mul w z := by
  rw [cl10_mul_eq, cl10_mul_eq]
  apply Prod.ext <;> dsimp only
  · rw [FieldOps.mul_comm z.1 w.1, FieldOps.mul_comm z.2 w.2]
  · rw [FieldOps.mul_comm z.1 w.2, FieldOps.mul_comm z.2 w.1, FieldOps.add_comm]

theorem cl10_mul_invl {K : Type u} [FieldOps K] (z : K × K) :
    (cl10Alg K).mul z ((cl10Alg K).invl z) = (cl10NormDiff z, 0) := by
  rw [cl10_mul_eq]
  dsimp only [cl10Alg, cliffordStep, FieldOps.toAssocInvolAlg, cl10NormDiff]
  apply Prod.ext <;> dsimp only
  · rw [FieldOps.mul_neg, ← FieldOps.sub_eq_add_neg]
  · rw [FieldOps.mul_neg, FieldOps.mul_comm z.2 z.1, FieldOps.neg_add_cancel]

theorem cl10_scalar_mul {K : Type u} [FieldOps K] (s : K) (z : K × K) :
    (cl10Alg K).mul (s, 0) z = (s * z.1, s * z.2) := by
  rw [cl10_mul_eq]
  apply Prod.ext <;> dsimp only
  · rw [FieldOps.zero_mul, FieldOps.add_zero]
  · rw [FieldOps.zero_mul, FieldOps.add_zero]

theorem cl10_hasTwoSidedInv_of_normDiff_ne_zero {K : Type u} [FieldOps K] {z : K × K}
    (hN : cl10NormDiff z ≠ 0) :
    HasTwoSidedInv (cl10Alg K).one (cl10Alg K).mul z := by
  let sInv : K := (cl10NormDiff z)⁻¹
  let zInv : K × K := (cl10Alg K).mul (sInv, 0) ((cl10Alg K).invl z)
  refine ⟨zInv, ?_, ?_⟩
  · dsimp only [zInv]
    rw [cl10_mul_comm (sInv, 0), ← (cl10Alg K).mul_assoc, cl10_mul_invl,
        cl10_mul_comm (cl10NormDiff z, 0), cl10_scalar_mul]
    apply Prod.ext <;> dsimp only [cl10Alg, cliffordStep, FieldOps.toAssocInvolAlg]
    · exact FieldOps.inv_mul_cancel hN
    · exact FieldOps.mul_zero sInv
  · dsimp only [zInv]
    rw [(cl10Alg K).mul_assoc, cl10_mul_comm ((cl10Alg K).invl z) z, cl10_mul_invl,
        cl10_scalar_mul]
    apply Prod.ext <;> dsimp only [cl10Alg, cliffordStep, FieldOps.toAssocInvolAlg]
    · exact FieldOps.inv_mul_cancel hN
    · exact FieldOps.mul_zero sInv

/--
**Split Classification of `Cl_{1,0}(K)` (`n = 1, r = 0`):**
Over every field `K`, `z = (a, b) ∈ Z(Cl_{1,0}(K))` iff `a = b ∨ a = -b` (`a² - b² = 0`).
Thus `Z(Cl_{1,0}(K))` is the union of two 1-dimensional lines `K·(1,1) ∪ K·(1,-1)` (`dim Z = 1`),
contradicting `dim Z(Cl_{0,1}(K)) = 0` at the identical `(n, r) = (1, 0)`.
-/
theorem cl10_isZeroDivisor_iff {K : Type u} [FieldOps K] (z : K × K) :
    IsZeroDivisor (cl10Alg K).zero (cl10Alg K).mul z ↔ z.1 = z.2 ∨ z.1 = -z.2 := by
  constructor
  · intro hZD
    by_cases hN : cl10NormDiff z = 0
    · exact (field_sq_sub_sq_eq_zero_iff z.1 z.2).mp hN
    · exfalso
      exact (cl10Alg K).not_isZeroDivisor_of_inv (cl10_hasTwoSidedInv_of_normDiff_ne_zero hN) hZD
  · rintro (hEq | hEq)
    · refine ⟨(1, -1), ?_, Or.inl ?_⟩
      · intro hZ
        exact FieldOps.zero_ne_one (congrArg Prod.fst hZ).symm
      · rw [cl10_mul_eq, hEq, FieldOps.mul_one, FieldOps.mul_neg, FieldOps.mul_one,
            FieldOps.add_neg_cancel, FieldOps.neg_add_cancel]
        rfl
    · refine ⟨(1, 1), ?_, Or.inl ?_⟩
      · intro hZ
        exact FieldOps.zero_ne_one (congrArg Prod.fst hZ).symm
      · rw [cl10_mul_eq]
        dsimp only
        rw [hEq, FieldOps.mul_one, FieldOps.mul_one, FieldOps.neg_add_cancel]
        rfl

theorem cl10_dichotomy {K : Type u} [FieldOps K] : HasDichotomy (cl10Alg K) := by
  intro z
  by_cases hN : cl10NormDiff z = 0
  · exact Or.inl ((cl10_isZeroDivisor_iff z).mpr ((field_sq_sub_sq_eq_zero_iff z.1 z.2).mp hN))
  · exact Or.inr (cl10_hasTwoSidedInv_of_normDiff_ne_zero hN)

/-- Every nonzero scalar multiple `(t, t)` (`t ≠ 0`) is a nonzero zero divisor in `Cl_{1,0}(K)`. -/
theorem cl10_line_zeroDivisor {K : Type u} [FieldOps K] (t : K) :
    IsZeroDivisor (cl10Alg K).zero (cl10Alg K).mul (t, t) :=
  (cl10_isZeroDivisor_iff (t, t)).mpr (Or.inl rfl)

/-!
## 4. `Cl_{0,2}(K) ≅ ℍ_K` (`n = 2, p = 0, q = 2, r = 0`, `Q(x, y) = -x² - y²`)
-/

/-- Quaternion Clifford algebra `Cl_{0,2}(K)` (`e₁² = -1, e₂² = -1, e₁e₂ = -e₂e₁`). -/
def cl02Alg (K : Type u) [FieldOps K] : AssocInvolAlg ((K × K) × (K × K)) :=
  (cl01Alg K).cliffordStep .neg

/-- Quaternion conjugate `(z, w) ↦ (z̄, -w)`. -/
def cl02Conj {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) : (K × K) × (K × K) :=
  ((cl01Alg K).invl q.1, (cl01Alg K).neg q.2)

/-- Quaternion squared norm `a² + b² + c² + d²`. -/
def cl02NormSq {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) : K :=
  cl01NormSq q.1 + cl01NormSq q.2

theorem cl02_Conj_eq_zero_iff {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) :
    cl02Conj q = (cl02Alg K).zero ↔ q = (cl02Alg K).zero := by
  constructor
  · intro h
    apply Prod.ext
    · exact ((cl01Alg K).invl_eq_zero_iff q.1).mp (congrArg Prod.fst h)
    · have h2 : (cl01Alg K).neg q.2 = (cl01Alg K).zero := congrArg Prod.snd h
      have h3 := congrArg (cl01Alg K).neg h2
      rw [(cl01Alg K).neg_neg, (cl01Alg K).neg_zero] at h3
      exact h3
  · intro h
    rw [h]
    exact Prod.ext (cl01Alg K).invl_zero (cl01Alg K).neg_zero

theorem cl02_mul_conj {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) :
    (cl02Alg K).mul q (cl02Conj q) = ((cl02NormSq q, 0), (0, 0)) := by
  apply Prod.ext <;> dsimp only [cl02Alg, cl02Conj, cliffordStep, signAct]
  · rw [(cl01Alg K).invl_neg, (cl01Alg K).mul_neg, (cl01Alg K).neg_neg,
        cl01_mul_invl q.1, cl01_mul_invl q.2]
    exact Prod.ext rfl (FieldOps.add_zero 0)
  · rw [(cl01Alg K).mul_neg, (cl01Alg K).invl_invl, cl01_mul_comm q.2 q.1,
        (cl01Alg K).neg_add_cancel]
    rfl

theorem cl02_conj_mul {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) :
    (cl02Alg K).mul (cl02Conj q) q = ((cl02NormSq q, 0), (0, 0)) := by
  apply Prod.ext <;> dsimp only [cl02Alg, cl02Conj, cliffordStep, signAct]
  · rw [cl01_mul_comm ((cl01Alg K).invl q.1) q.1, (cl01Alg K).neg_mul, (cl01Alg K).neg_neg,
        cl01_mul_invl q.1, cl01_mul_invl q.2]
    exact Prod.ext rfl (FieldOps.add_zero 0)
  · rw [(cl01Alg K).neg_mul, cl01_mul_comm q.2 ((cl01Alg K).invl q.1),
        (cl01Alg K).add_neg_cancel]
    rfl

theorem cl02_scalar_mul {K : Type u} [FieldOps K] (s : K) (q : (K × K) × (K × K)) :
    (cl02Alg K).mul ((s, 0), (0, 0)) q = ((s * q.1.1, s * q.1.2), (s * q.2.1, s * q.2.2)) := by
  have hz01 : ((0 : K), (0 : K)) = (cl01Alg K).zero := rfl
  apply Prod.ext <;> dsimp only [cl02Alg, cliffordStep, signAct]
  · rw [hz01, (cl01Alg K).zero_mul, (cl01Alg K).neg_zero, (cl01Alg K).add_zero, cl01_scalar_mul]
  · rw [hz01, (cl01Alg K).zero_mul, (cl01Alg K).add_zero, cl01_scalar_mul]

theorem cl02_mul_scalar {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) (s : K) :
    (cl02Alg K).mul q ((s, 0), (0, 0)) = ((q.1.1 * s, q.1.2 * s), (q.2.1 * s, q.2.2 * s)) := by
  have hz01 : ((0 : K), (0 : K)) = (cl01Alg K).zero := rfl
  apply Prod.ext <;> dsimp only [cl02Alg, cliffordStep, signAct]
  · rw [hz01, (cl01Alg K).invl_zero, (cl01Alg K).mul_zero, (cl01Alg K).neg_zero,
        (cl01Alg K).add_zero, cl01_mul_comm q.1 (s, 0), cl01_scalar_mul,
        FieldOps.mul_comm s q.1.1, FieldOps.mul_comm s q.1.2]
  · rw [hz01, (cl01Alg K).mul_zero, (cl01Alg K).zero_add]
    have hInvS : (cl01Alg K).invl (s, 0) = (s, 0) := by
      dsimp only [cl01Alg, cliffordStep, FieldOps.toAssocInvolAlg]
      exact Prod.ext rfl FieldOps.neg_zero
    rw [hInvS, cl01_mul_comm q.2 (s, 0), cl01_scalar_mul,
        FieldOps.mul_comm s q.2.1, FieldOps.mul_comm s q.2.2]

theorem cl02_hasTwoSidedInv_of_normSq_ne_zero {K : Type u} [FieldOps K]
    {q : (K × K) × (K × K)} (hN : cl02NormSq q ≠ 0) :
    HasTwoSidedInv (cl02Alg K).one (cl02Alg K).mul q := by
  let sInv : K := (cl02NormSq q)⁻¹
  let qInv := (cl02Alg K).mul (cl02Conj q) ((sInv, 0), (0, 0))
  refine ⟨qInv, ?_, ?_⟩
  · dsimp only [qInv]
    rw [← (cl02Alg K).mul_assoc, cl02_mul_conj, cl02_mul_scalar]
    apply Prod.ext <;> apply Prod.ext
    · exact FieldOps.mul_inv_cancel (cl02NormSq q) hN
    · exact FieldOps.zero_mul sInv
    · exact FieldOps.zero_mul sInv
    · exact FieldOps.zero_mul sInv
  · have hComm : qInv = (cl02Alg K).mul ((sInv, 0), (0, 0)) (cl02Conj q) := by
      dsimp only [qInv]
      rw [cl02_mul_scalar, cl02_scalar_mul]
      apply Prod.ext <;> apply Prod.ext <;> exact FieldOps.mul_comm _ _
    rw [hComm, (cl02Alg K).mul_assoc, cl02_conj_mul, cl02_scalar_mul]
    apply Prod.ext <;> apply Prod.ext
    · exact FieldOps.inv_mul_cancel hN
    · exact FieldOps.mul_zero sInv
    · exact FieldOps.mul_zero sInv
    · exact FieldOps.mul_zero sInv

/-- Hypothesis that `(a² + b²) + (c² + d²) = 0 → a = b = c = d = 0` (holds for `ℝ` and `ℚ`). -/
def IsFourSqAnisotropic (K : Type u) [FieldOps K] : Prop :=
  ∀ a b c d : K, (a * a + b * b) + (c * c + d * d) = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0

/--
**Division Algebra Classification of `Cl_{0,2}(K) ≅ ℍ_K` (`n = 2, r = 0`):**
Whenever `K` is 4-square anisotropic, `Z(Cl_{0,2}(K)) = {0}` has dimension `0`.
-/
theorem cl02_isZeroDivisor_iff {K : Type u} [FieldOps K] (hAniso : IsFourSqAnisotropic K)
    (q : (K × K) × (K × K)) :
    IsZeroDivisor (cl02Alg K).zero (cl02Alg K).mul q ↔ q = ((0, 0), (0, 0)) := by
  constructor
  · intro hZD
    by_cases hN : cl02NormSq q = 0
    · rcases hAniso q.1.1 q.1.2 q.2.1 q.2.2 hN with ⟨ha, hb, hc, hd⟩
      exact Prod.ext (Prod.ext ha hb) (Prod.ext hc hd)
    · exfalso
      exact (cl02Alg K).not_isZeroDivisor_of_inv (cl02_hasTwoSidedInv_of_normSq_ne_zero hN) hZD
  · rintro rfl
    exact (cl02Alg K).zero_isZeroDivisor

/-!
## 5. `Cl_{1,1}(K)` (`n = 2, p = 1, q = 1, r = 0`, `Q(x, y) = x² - y²`)
-/

/-- Split Clifford algebra `Cl_{1,1}(K)` (`e₁² = +1, e₂² = -1, e₁e₂ = -e₂e₁`). -/
def cl11Alg (K : Type u) [FieldOps K] : AssocInvolAlg ((K × K) × (K × K)) :=
  (cl10Alg K).cliffordStep .neg

/-- Split-quaternion conjugate `(z, w) ↦ (invl z, -w)` on `Cl_{1,1}(K)`. -/
def cl11Conj {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) : (K × K) × (K × K) :=
  ((cl10Alg K).invl q.1, (cl10Alg K).neg q.2)

/-- Split quadratic norm `(a² - b²) + (c² - d²)` cutting out the 3D quadric hypersurface `Z`. -/
def cl11QuadNorm {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) : K :=
  cl10NormDiff q.1 + cl10NormDiff q.2

theorem cl11_conj_eq_zero_iff {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) :
    cl11Conj q = (cl11Alg K).zero ↔ q = (cl11Alg K).zero := by
  constructor
  · intro h
    apply Prod.ext
    · exact ((cl10Alg K).invl_eq_zero_iff q.1).mp (congrArg Prod.fst h)
    · have h2 : (cl10Alg K).neg q.2 = (cl10Alg K).zero := congrArg Prod.snd h
      have h3 := congrArg (cl10Alg K).neg h2
      rw [(cl10Alg K).neg_neg, (cl10Alg K).neg_zero] at h3
      exact h3
  · intro h
    rw [h]
    exact Prod.ext (cl10Alg K).invl_zero (cl10Alg K).neg_zero

theorem cl11_mul_conj {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) :
    (cl11Alg K).mul q (cl11Conj q) = ((cl11QuadNorm q, 0), (0, 0)) := by
  apply Prod.ext <;> dsimp only [cl11Alg, cl11Conj, cliffordStep, signAct]
  · rw [(cl10Alg K).invl_neg, (cl10Alg K).mul_neg, (cl10Alg K).neg_neg,
        cl10_mul_invl q.1, cl10_mul_invl q.2]
    exact Prod.ext rfl (FieldOps.add_zero 0)
  · rw [(cl10Alg K).mul_neg, (cl10Alg K).invl_invl, cl10_mul_comm q.2 q.1,
        (cl10Alg K).neg_add_cancel]
    rfl

theorem cl11_conj_mul {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) :
    (cl11Alg K).mul (cl11Conj q) q = ((cl11QuadNorm q, 0), (0, 0)) := by
  apply Prod.ext <;> dsimp only [cl11Alg, cl11Conj, cliffordStep, signAct]
  · rw [cl10_mul_comm ((cl10Alg K).invl q.1) q.1, (cl10Alg K).neg_mul, (cl10Alg K).neg_neg,
        cl10_mul_invl q.1, cl10_mul_invl q.2]
    exact Prod.ext rfl (FieldOps.add_zero 0)
  · rw [(cl10Alg K).neg_mul, cl10_mul_comm q.2 ((cl10Alg K).invl q.1),
        (cl10Alg K).add_neg_cancel]
    rfl

theorem cl11_scalar_mul {K : Type u} [FieldOps K] (s : K) (q : (K × K) × (K × K)) :
    (cl11Alg K).mul ((s, 0), (0, 0)) q = ((s * q.1.1, s * q.1.2), (s * q.2.1, s * q.2.2)) := by
  have hz10 : ((0 : K), (0 : K)) = (cl10Alg K).zero := rfl
  apply Prod.ext <;> dsimp only [cl11Alg, cliffordStep, signAct]
  · rw [hz10, (cl10Alg K).zero_mul, (cl10Alg K).neg_zero, (cl10Alg K).add_zero, cl10_scalar_mul]
  · rw [hz10, (cl10Alg K).zero_mul, (cl10Alg K).add_zero, cl10_scalar_mul]

theorem cl11_mul_scalar {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) (s : K) :
    (cl11Alg K).mul q ((s, 0), (0, 0)) = ((q.1.1 * s, q.1.2 * s), (q.2.1 * s, q.2.2 * s)) := by
  have hz10 : ((0 : K), (0 : K)) = (cl10Alg K).zero := rfl
  apply Prod.ext <;> dsimp only [cl11Alg, cliffordStep, signAct]
  · rw [hz10, (cl10Alg K).invl_zero, (cl10Alg K).mul_zero, (cl10Alg K).neg_zero,
        (cl10Alg K).add_zero, cl10_mul_comm q.1 (s, 0), cl10_scalar_mul,
        FieldOps.mul_comm s q.1.1, FieldOps.mul_comm s q.1.2]
  · rw [hz10, (cl10Alg K).mul_zero, (cl10Alg K).zero_add]
    have hInvS : (cl10Alg K).invl (s, 0) = (s, 0) := by
      dsimp only [cl10Alg, cliffordStep, FieldOps.toAssocInvolAlg]
      exact Prod.ext rfl FieldOps.neg_zero
    rw [hInvS, cl10_mul_comm q.2 (s, 0), cl10_scalar_mul,
        FieldOps.mul_comm s q.2.1, FieldOps.mul_comm s q.2.2]

theorem cl11_hasTwoSidedInv_of_quadNorm_ne_zero {K : Type u} [FieldOps K]
    {q : (K × K) × (K × K)} (hN : cl11QuadNorm q ≠ 0) :
    HasTwoSidedInv (cl11Alg K).one (cl11Alg K).mul q := by
  let sInv : K := (cl11QuadNorm q)⁻¹
  let qInv := (cl11Alg K).mul (cl11Conj q) ((sInv, 0), (0, 0))
  refine ⟨qInv, ?_, ?_⟩
  · dsimp only [qInv]
    rw [← (cl11Alg K).mul_assoc, cl11_mul_conj, cl11_mul_scalar]
    apply Prod.ext <;> apply Prod.ext
    · exact FieldOps.mul_inv_cancel (cl11QuadNorm q) hN
    · exact FieldOps.zero_mul sInv
    · exact FieldOps.zero_mul sInv
    · exact FieldOps.zero_mul sInv
  · have hComm : qInv = (cl11Alg K).mul ((sInv, 0), (0, 0)) (cl11Conj q) := by
      dsimp only [qInv]
      rw [cl11_mul_scalar, cl11_scalar_mul]
      apply Prod.ext <;> apply Prod.ext <;> exact FieldOps.mul_comm _ _
    rw [hComm, (cl11Alg K).mul_assoc, cl11_conj_mul, cl11_scalar_mul]
    apply Prod.ext <;> apply Prod.ext
    · exact FieldOps.inv_mul_cancel hN
    · exact FieldOps.mul_zero sInv
    · exact FieldOps.mul_zero sInv
    · exact FieldOps.mul_zero sInv

/--
**Quadric Hypersurface Classification of `Cl_{1,1}(K)` (`n = 2, r = 0`):**
Over every field `K`, `q = ((a, b), (c, d)) ∈ Z(Cl_{1,1}(K))` iff `(a² - b²) + (c² - d²) = 0`
(a 3-dimensional quadric hypersurface of codimension `1`, despite metric nullity `r = 0`).
-/
theorem cl11_isZeroDivisor_iff {K : Type u} [FieldOps K] (q : (K × K) × (K × K)) :
    IsZeroDivisor (cl11Alg K).zero (cl11Alg K).mul q ↔ cl11QuadNorm q = 0 := by
  constructor
  · intro hZD
    by_cases hN : cl11QuadNorm q = 0
    · exact hN
    · exfalso
      exact (cl11Alg K).not_isZeroDivisor_of_inv (cl11_hasTwoSidedInv_of_quadNorm_ne_zero hN) hZD
  · intro hN
    by_cases hq : q = (cl11Alg K).zero
    · rw [hq]
      exact (cl11Alg K).zero_isZeroDivisor
    · refine ⟨cl11Conj q, ?_, Or.inl ?_⟩
      · intro hConjZ
        exact hq ((cl11_conj_eq_zero_iff q).mp hConjZ)
      · rw [cl11_mul_conj, hN]
        rfl

theorem cl11_dichotomy {K : Type u} [FieldOps K] : HasDichotomy (cl11Alg K) := by
  intro q
  by_cases hN : cl11QuadNorm q = 0
  · exact Or.inl ((cl11_isZeroDivisor_iff q).mpr hN)
  · exact Or.inr (cl11_hasTwoSidedInv_of_quadNorm_ne_zero hN)

/--
**Grade-1 Vector Zero-Divisor Classification (`Z ∩ V = {v ∈ V : Q(v) = 0}`):**
Embedding `v = x e₁ + y e₂ ↦ ((0, x), (y, 0))` into `Cl_{1,1}(K)` vs. `Cl_{0,2}(K)` shows:
- In `Cl_{1,1}(K)` (`r = 0`), `v ∈ Z` iff `x² - y² = 0` (`(1, 1)` is a nonzero isotropic vector).
- In `Cl_{0,2}(K)` (`r = 0`, 4-square anisotropic), `v ∈ Z` iff `x = 0 ∧ y = 0`.
-/
def grade1Vec {K : Type u} [FieldOps K] (x y : K) : (K × K) × (K × K) :=
  ((0, x), (y, 0))

theorem cl11_grade1_isZeroDivisor_iff {K : Type u} [FieldOps K] (x y : K) :
    IsZeroDivisor (cl11Alg K).zero (cl11Alg K).mul (grade1Vec x y) ↔ x = y ∨ x = -y := by
  rw [cl11_isZeroDivisor_iff]
  dsimp only [cl11QuadNorm, cl10NormDiff, grade1Vec]
  rw [FieldOps.zero_mul, FieldOps.zero_sub, FieldOps.sub_zero, FieldOps.add_comm,
      ← FieldOps.sub_eq_add_neg, field_sq_sub_sq_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · right
      rw [h, FieldOps.neg_neg]
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · right
      exact (FieldOps.neg_neg y).symm

theorem cl02_grade1_isZeroDivisor_iff {K : Type u} [FieldOps K] (hAniso : IsFourSqAnisotropic K)
    (x y : K) :
    IsZeroDivisor (cl02Alg K).zero (cl02Alg K).mul (grade1Vec x y) ↔ x = 0 ∧ y = 0 := by
  rw [cl02_isZeroDivisor_iff hAniso]
  dsimp only [grade1Vec]
  constructor
  · intro h
    exact ⟨congrArg Prod.snd (congrArg Prod.fst h), congrArg Prod.fst (congrArg Prod.snd h)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-!
## 6. `2 × 2` Matrix Algebra `M₂(K) ≅ Cl_{1,1}(K)`: Determinant & Annihilator Laws
-/

/-- Explicit `2 × 2` matrix type over `K`. -/
structure Mat2 (K : Type u) where
  m11 : K
  m12 : K
  m21 : K
  m22 : K
  deriving DecidableEq, Repr

namespace Mat2

section MatrixOps

variable {K : Type u} [FieldOps K]

def zero : Mat2 K := ⟨0, 0, 0, 0⟩
def one : Mat2 K := ⟨1, 0, 0, 1⟩
def add (A B : Mat2 K) : Mat2 K :=
  ⟨A.m11 + B.m11, A.m12 + B.m12, A.m21 + B.m21, A.m22 + B.m22⟩
def neg (A : Mat2 K) : Mat2 K := ⟨-A.m11, -A.m12, -A.m21, -A.m22⟩
def mul (A B : Mat2 K) : Mat2 K :=
  ⟨ A.m11 * B.m11 + A.m12 * B.m21,
    A.m11 * B.m12 + A.m12 * B.m22,
    A.m21 * B.m11 + A.m22 * B.m21,
    A.m21 * B.m12 + A.m22 * B.m22 ⟩

def det (A : Mat2 K) : K := A.m11 * A.m22 - A.m12 * A.m21
def adj (A : Mat2 K) : Mat2 K := ⟨A.m22, -A.m12, -A.m21, A.m11⟩
def scalar (s : K) : Mat2 K := ⟨s, 0, 0, s⟩

end MatrixOps

theorem ext_iff {K : Type u} {A B : Mat2 K} :
    A = B ↔ A.m11 = B.m11 ∧ A.m12 = B.m12 ∧ A.m21 = B.m21 ∧ A.m22 = B.m22 := by
  cases A; cases B
  simp only [mk.injEq]

def alg (K : Type u) [FieldOps K] : AssocInvolAlg (Mat2 K) where
  zero := zero
  one := one
  add := add
  neg := neg
  mul := mul
  invl := fun A => A
  zero_ne_one := by
    intro h
    exact FieldOps.zero_ne_one (congrArg m11 h)
  add_assoc A B C := by
    apply ext_iff.mpr; dsimp only [add]
    exact ⟨FieldOps.add_assoc _ _ _, FieldOps.add_assoc _ _ _,
           FieldOps.add_assoc _ _ _, FieldOps.add_assoc _ _ _⟩
  add_comm A B := by
    apply ext_iff.mpr; dsimp only [add]
    exact ⟨FieldOps.add_comm _ _, FieldOps.add_comm _ _,
           FieldOps.add_comm _ _, FieldOps.add_comm _ _⟩
  zero_add A := by
    apply ext_iff.mpr; dsimp only [zero, add]
    exact ⟨FieldOps.zero_add _, FieldOps.zero_add _, FieldOps.zero_add _, FieldOps.zero_add _⟩
  add_zero A := by
    apply ext_iff.mpr; dsimp only [zero, add]
    exact ⟨FieldOps.add_zero _, FieldOps.add_zero _, FieldOps.add_zero _, FieldOps.add_zero _⟩
  neg_add_cancel A := by
    apply ext_iff.mpr; dsimp only [zero, neg, add]
    exact ⟨FieldOps.neg_add_cancel _, FieldOps.neg_add_cancel _,
           FieldOps.neg_add_cancel _, FieldOps.neg_add_cancel _⟩
  mul_assoc A B C := by
    apply ext_iff.mpr; dsimp only [mul]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [FieldOps.right_distrib, FieldOps.right_distrib,
          FieldOps.left_distrib, FieldOps.left_distrib,
          FieldOps.mul_assoc, FieldOps.mul_assoc, FieldOps.mul_assoc, FieldOps.mul_assoc]
      exact field_add_add_add_comm _ _ _ _
  one_mul A := by
    apply ext_iff.mpr; dsimp only [one, mul]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [FieldOps.one_mul, FieldOps.zero_mul, FieldOps.add_zero]
    · rw [FieldOps.one_mul, FieldOps.zero_mul, FieldOps.add_zero]
    · rw [FieldOps.zero_mul, FieldOps.one_mul, FieldOps.zero_add]
    · rw [FieldOps.zero_mul, FieldOps.one_mul, FieldOps.zero_add]
  mul_one A := by
    apply ext_iff.mpr; dsimp only [one, mul]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [FieldOps.mul_one, FieldOps.mul_zero, FieldOps.add_zero]
    · rw [FieldOps.mul_zero, FieldOps.mul_one, FieldOps.zero_add]
    · rw [FieldOps.mul_one, FieldOps.mul_zero, FieldOps.add_zero]
    · rw [FieldOps.mul_zero, FieldOps.mul_one, FieldOps.zero_add]
  left_distrib A B C := by
    apply ext_iff.mpr; dsimp only [add, mul]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [FieldOps.left_distrib, FieldOps.left_distrib]
      exact (field_add_add_add_comm _ _ _ _).symm
  right_distrib A B C := by
    apply ext_iff.mpr; dsimp only [add, mul]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [FieldOps.right_distrib, FieldOps.right_distrib]
      exact (field_add_add_add_comm _ _ _ _).symm
  invl_invl _ := rfl
  invl_zero := rfl
  invl_one := rfl
  invl_add _ _ := rfl
  invl_neg _ := rfl
  invl_mul _ _ := rfl

section MatrixTheorems

variable {K : Type u} [FieldOps K]

theorem mul_adj (A : Mat2 K) : mul A (adj A) = scalar (det A) := by
  cases A with | mk a b c d =>
  apply ext_iff.mpr
  dsimp only [mul, adj, scalar, det]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FieldOps.mul_neg, ← FieldOps.sub_eq_add_neg]
  · rw [FieldOps.mul_neg, FieldOps.mul_comm b a, FieldOps.neg_add_cancel]
  · rw [FieldOps.mul_neg, FieldOps.mul_comm d c, FieldOps.add_neg_cancel]
  · rw [FieldOps.mul_neg, FieldOps.mul_comm c b, FieldOps.mul_comm d a,
        FieldOps.add_comm, ← FieldOps.sub_eq_add_neg]

theorem adj_mul (A : Mat2 K) : mul (adj A) A = scalar (det A) := by
  cases A with | mk a b c d =>
  apply ext_iff.mpr
  dsimp only [mul, adj, scalar, det]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FieldOps.neg_mul, FieldOps.mul_comm d a, ← FieldOps.sub_eq_add_neg]
  · rw [FieldOps.neg_mul, FieldOps.mul_comm d b, FieldOps.add_neg_cancel]
  · rw [FieldOps.neg_mul, FieldOps.mul_comm c a, FieldOps.neg_add_cancel]
  · rw [FieldOps.neg_mul, FieldOps.mul_comm c b, FieldOps.add_comm, ← FieldOps.sub_eq_add_neg]

theorem adj_eq_zero_iff (A : Mat2 K) : adj A = zero ↔ A = zero := by
  cases A with | mk a b c d =>
  dsimp only [adj, zero]
  constructor
  · intro h
    rcases ext_iff.mp h with ⟨hd, hnb, hnc, ha⟩
    dsimp only at hd hnb hnc ha
    have hb : b = 0 := by
      have h1 := congrArg Neg.neg hnb
      rw [FieldOps.neg_neg, FieldOps.neg_zero] at h1
      exact h1
    have hc : c = 0 := by
      have h1 := congrArg Neg.neg hnc
      rw [FieldOps.neg_neg, FieldOps.neg_zero] at h1
      exact h1
    exact ext_iff.mpr ⟨ha, hb, hc, hd⟩
  · intro h
    rcases ext_iff.mp h with ⟨rfl, rfl, rfl, rfl⟩
    dsimp only
    rw [FieldOps.neg_zero]

theorem hasTwoSidedInv_of_det_ne_zero {A : Mat2 K} (hDet : det A ≠ 0) :
    HasTwoSidedInv (alg K).one (alg K).mul A := by
  let sInv := (det A)⁻¹
  let AInv := mul (adj A) (scalar sInv)
  refine ⟨AInv, ?_, ?_⟩
  · have hAssocR := (alg K).mul_assoc A (adj A) (scalar sInv)
    dsimp only [alg] at hAssocR ⊢
    dsimp only [AInv]
    rw [← hAssocR, mul_adj]
    apply ext_iff.mpr; dsimp only [mul, scalar, one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [FieldOps.mul_zero, FieldOps.add_zero, FieldOps.mul_inv_cancel (det A) hDet]
    · rw [FieldOps.mul_zero, FieldOps.zero_mul, FieldOps.add_zero]
    · rw [FieldOps.zero_mul, FieldOps.mul_zero, FieldOps.add_zero]
    · rw [FieldOps.zero_mul, FieldOps.zero_add, FieldOps.mul_inv_cancel (det A) hDet]
  · have hComm : AInv = mul (scalar sInv) (adj A) := by
      apply ext_iff.mpr; dsimp only [AInv, mul, scalar]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [FieldOps.mul_zero, FieldOps.zero_mul, FieldOps.add_zero, FieldOps.add_zero,
            FieldOps.mul_comm]
      · rw [FieldOps.mul_zero, FieldOps.zero_mul, FieldOps.zero_add, FieldOps.add_zero,
            FieldOps.mul_comm]
      · rw [FieldOps.mul_zero, FieldOps.zero_mul, FieldOps.add_zero, FieldOps.zero_add,
            FieldOps.mul_comm]
      · rw [FieldOps.mul_zero, FieldOps.zero_mul, FieldOps.zero_add, FieldOps.zero_add,
            FieldOps.mul_comm]
    have hAssocL := (alg K).mul_assoc (scalar sInv) (adj A) A
    dsimp only [alg] at hAssocL ⊢
    rw [hComm, hAssocL, adj_mul]
    apply ext_iff.mpr; dsimp only [mul, scalar, one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [FieldOps.zero_mul, FieldOps.add_zero, FieldOps.inv_mul_cancel hDet]
    · rw [FieldOps.mul_zero, FieldOps.zero_mul, FieldOps.add_zero]
    · rw [FieldOps.zero_mul, FieldOps.mul_zero, FieldOps.add_zero]
    · rw [FieldOps.zero_mul, FieldOps.zero_add, FieldOps.inv_mul_cancel hDet]

/--
**Exact Determinant Zero-Divisor Law on `M₂(K)`:**
Over any field `K`, `A ∈ Z(M₂(K))` iff `det A = 0`.
-/
theorem isZeroDivisor_iff_det_eq_zero (A : Mat2 K) :
    IsZeroDivisor (alg K).zero (alg K).mul A ↔ det A = 0 := by
  constructor
  · intro hZD
    by_cases hDet : det A = 0
    · exact hDet
    · exfalso
      exact (alg K).not_isZeroDivisor_of_inv (hasTwoSidedInv_of_det_ne_zero hDet) hZD
  · intro hDet
    by_cases hA : A = zero
    · rw [hA]
      exact (alg K).zero_isZeroDivisor
    · refine ⟨adj A, ?_, Or.inl ?_⟩
      · intro hAdjZ
        exact hA ((adj_eq_zero_iff A).mp hAdjZ)
      · dsimp only [alg]
        rw [mul_adj, hDet]
        rfl

/-- Rank-1 idempotent `E₁₁ = ⟨1, 0, 0, 0⟩` is a nonzero zero divisor whose right annihilator
is the 2-dimensional subspace `{⟨0, 0, z, w⟩ : z, w ∈ K}` (`dim Ann_R(E₁₁) = 2 ≠ 0`). -/
def e11 : Mat2 K := ⟨1, 0, 0, 0⟩

theorem e11_isZeroDivisor : IsZeroDivisor (alg K).zero (alg K).mul (e11 : Mat2 K) := by
  rw [isZeroDivisor_iff_det_eq_zero]
  dsimp only [e11, det]
  rw [FieldOps.mul_zero, FieldOps.zero_mul, FieldOps.sub_self]

theorem inRightAnn_e11_iff (Y : Mat2 K) :
    InRightAnn (alg K).zero (alg K).mul e11 Y ↔ Y.m11 = 0 ∧ Y.m12 = 0 := by
  cases Y with | mk y11 y12 y21 y22 =>
  dsimp only [InRightAnn, alg, e11, mul, zero]
  rw [FieldOps.one_mul, FieldOps.one_mul, FieldOps.zero_mul, FieldOps.zero_mul,
      FieldOps.add_zero, FieldOps.add_zero]
  constructor
  · intro h
    rcases ext_iff.mp h with ⟨h1, h2, _, _⟩
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    apply ext_iff.mpr; dsimp only
    refine ⟨rfl, rfl, ?_, ?_⟩ <;> rw [FieldOps.zero_mul, FieldOps.add_zero]

end MatrixTheorems

end Mat2

end ZeroDivisorMetricRankDeficit
