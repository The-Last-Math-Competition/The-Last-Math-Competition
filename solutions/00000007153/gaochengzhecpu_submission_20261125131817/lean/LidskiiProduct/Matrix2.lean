/-
  LidskiiProduct/Matrix2.lean
  2x2 integer matrices, singular values, additive/logarithmic majorization,
  universal Horn-Lidskii product log-majorization, exact equality characterization,
  Weyl eigenvalue-singular-value log-majorization, Ky Fan diagonal pinching,
  and similarity non-diagonalizability of defective matrices.
-/
import LidskiiProduct.Algebra

namespace LidskiiProduct

/-- A 2x2 matrix with integer entries. -/
structure Mat2 where
  a11 : Int
  a12 : Int
  a21 : Int
  a22 : Int
  deriving DecidableEq, Repr

namespace Mat2

def diag (d1 d2 : Int) : Mat2 := ⟨d1, 0, 0, d2⟩

def id2 : Mat2 := diag 1 1

def scale (k : Int) (M : Mat2) : Mat2 :=
  ⟨k * M.a11, k * M.a12, k * M.a21, k * M.a22⟩

def transpose (M : Mat2) : Mat2 :=
  ⟨M.a11, M.a21, M.a12, M.a22⟩

def adj (M : Mat2) : Mat2 :=
  ⟨M.a22, -M.a12, -M.a21, M.a11⟩

def mul (A B : Mat2) : Mat2 :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21,
   A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21,
   A.a21 * B.a12 + A.a22 * B.a22⟩

def tr (M : Mat2) : Int := M.a11 + M.a22

def det (M : Mat2) : Int := M.a11 * M.a22 - M.a12 * M.a21

def frobSq (M : Mat2) : Int := tr (mul (transpose M) M)

/-- Standard-basis diagonal predicate. -/
def IsDiagonal (M : Mat2) : Prop := M.a12 = 0 ∧ M.a21 = 0

instance (M : Mat2) : Decidable (IsDiagonal M) :=
  inferInstanceAs (Decidable (M.a12 = 0 ∧ M.a21 = 0))

/-- Symmetry predicate (`M^T = M`). -/
def IsSymmetric (M : Mat2) : Prop := transpose M = M

instance (M : Mat2) : Decidable (IsSymmetric M) :=
  inferInstanceAs (Decidable (transpose M = M))

/-- Normality predicate (`M^T M = M M^T`). -/
def IsNormal (M : Mat2) : Prop := mul (transpose M) M = mul M (transpose M)

instance (M : Mat2) : Decidable (IsNormal M) :=
  inferInstanceAs (Decidable (mul (transpose M) M = mul M (transpose M)))

/-- Scalar multiple of the identity (`M = c I_2`). -/
def IsScalar (M : Mat2) : Prop := M.a12 = 0 ∧ M.a21 = 0 ∧ M.a11 = M.a22

instance (M : Mat2) : Decidable (IsScalar M) :=
  inferInstanceAs (Decidable (M.a12 = 0 ∧ M.a21 = 0 ∧ M.a11 = M.a22))

/-- Defective 2x2 matrix: repeated root in characteristic polynomial (`tr(M)^2 = 4 det(M)`)
    while not a scalar multiple of the identity. Over any field of characteristic 0 (including C),
    such a matrix has a single 2x2 Jordan block and is not diagonalizable by any similarity. -/
def IsDefective (M : Mat2) : Prop :=
  (tr M) ^ 2 = 4 * det M ∧ ¬ IsScalar M

instance (M : Mat2) : Decidable (IsDefective M) :=
  inferInstanceAs (Decidable ((tr M) ^ 2 = 4 * det M ∧ ¬ IsScalar M))

/-- Similarity to a diagonal matrix via an invertible matrix `S` (`det S ≠ 0`),
    clearing any rational denominators into `S M = diag(l1, l2) S`. -/
def SimilarToDiagInt (M : Mat2) : Prop :=
  ∃ (S : Mat2) (l1 l2 : Int), det S ≠ 0 ∧ mul S M = mul (diag l1 l2) S

theorem ext_iff {A B : Mat2} :
    A = B ↔ A.a11 = B.a11 ∧ A.a12 = B.a12 ∧ A.a21 = B.a21 ∧ A.a22 = B.a22 := by
  constructor
  · intro h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h11, h12, h21, h22⟩
    cases A
    cases B
    simp only at h11 h12 h21 h22
    subst h11; subst h12; subst h21; subst h22
    rfl

theorem dot2_assoc (a b p q r s u v : Int) :
    (a * p + b * r) * u + (a * q + b * s) * v =
      a * (p * u + q * v) + b * (r * u + s * v) := by
  rw [Int.add_mul, Int.add_mul, Int.mul_add, Int.mul_add]
  rw [Int.mul_assoc, Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]
  omega

theorem dot2_comm (a b c d : Int) :
    a * c + b * d = c * a + d * b := by
  rw [Int.mul_comm a c, Int.mul_comm b d]

theorem add_mul_add (p q r s : Int) :
    (p + q) * (r + s) = p * r + p * s + q * r + q * s := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add]
  omega

theorem sub_mul_sub (p q r s : Int) :
    (p - q) * (r - s) = p * r - p * s - q * r + q * s := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
  omega

theorem mul4_swap23 (p q r s : Int) :
    (p * q) * (r * s) = (p * r) * (q * s) := by
  rw [Int.mul_assoc, Int.mul_left_comm q r s, ← Int.mul_assoc]

theorem mul_assoc (A B C : Mat2) : mul (mul A B) C = mul A (mul B C) := by
  rw [ext_iff]
  exact ⟨dot2_assoc A.a11 A.a12 B.a11 B.a12 B.a21 B.a22 C.a11 C.a21,
         dot2_assoc A.a11 A.a12 B.a11 B.a12 B.a21 B.a22 C.a12 C.a22,
         dot2_assoc A.a21 A.a22 B.a11 B.a12 B.a21 B.a22 C.a11 C.a21,
         dot2_assoc A.a21 A.a22 B.a11 B.a12 B.a21 B.a22 C.a12 C.a22⟩

theorem transpose_mul (A B : Mat2) :
    transpose (mul A B) = mul (transpose B) (transpose A) := by
  rw [ext_iff]
  dsimp [transpose, mul]
  exact ⟨dot2_comm A.a11 A.a12 B.a11 B.a21,
         dot2_comm A.a21 A.a22 B.a11 B.a21,
         dot2_comm A.a11 A.a12 B.a12 B.a22,
         dot2_comm A.a21 A.a22 B.a12 B.a22⟩

theorem tr_mul_comm (A B : Mat2) : tr (mul A B) = tr (mul B A) := by
  dsimp [tr, mul]
  rw [Int.mul_comm A.a11 B.a11, Int.mul_comm A.a12 B.a21,
      Int.mul_comm A.a21 B.a12, Int.mul_comm A.a22 B.a22]
  omega

theorem det_transpose (A : Mat2) : det (transpose A) = det A := by
  dsimp [det, transpose]
  rw [Int.mul_comm A.a21 A.a12]

theorem det_mul (A B : Mat2) : det (mul A B) = det A * det B := by
  dsimp [det, mul]
  rw [add_mul_add, add_mul_add, sub_mul_sub]
  rw [mul4_swap23 A.a11 B.a11 A.a21 B.a12,
      mul4_swap23 A.a11 B.a11 A.a22 B.a22,
      mul4_swap23 A.a12 B.a21 A.a21 B.a12,
      mul4_swap23 A.a12 B.a21 A.a22 B.a22,
      mul4_swap23 A.a11 B.a12 A.a21 B.a11,
      mul4_swap23 A.a11 B.a12 A.a22 B.a21,
      mul4_swap23 A.a12 B.a22 A.a21 B.a11,
      mul4_swap23 A.a12 B.a22 A.a22 B.a21]
  rw [Int.mul_comm B.a12 B.a11,
      Int.mul_comm B.a21 B.a12,
      Int.mul_comm B.a22 B.a11,
      Int.mul_comm B.a22 B.a21]
  omega

theorem det_gram_eq_det_sq (M : Mat2) :
    det (mul (transpose M) M) = (det M) ^ 2 := by
  rw [det_mul, det_transpose, sq_eq_mul_self]

theorem frobSq_eq_sum_sq (M : Mat2) :
    frobSq M = M.a11 ^ 2 + M.a12 ^ 2 + M.a21 ^ 2 + M.a22 ^ 2 := by
  dsimp [frobSq, tr, mul, transpose]
  rw [sq_eq_mul_self, sq_eq_mul_self, sq_eq_mul_self, sq_eq_mul_self]
  omega

theorem frobSq_mul_eq_tr_grams (A B : Mat2) :
    frobSq (mul A B) = tr (mul (mul (transpose A) A) (mul B (transpose B))) := by
  dsimp [frobSq]
  rw [transpose_mul, mul_assoc (transpose B) (transpose A) (mul A B),
      tr_mul_comm (transpose B) (mul (transpose A) (mul A B)),
      ← mul_assoc (transpose A) A B,
      mul_assoc (mul (transpose A) A) B (transpose B)]

theorem mul_adj_right (S : Mat2) : mul S (adj S) = scale (det S) id2 := by
  rw [ext_iff]
  dsimp [mul, adj, scale, id2, diag, det]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Int.mul_neg, Int.mul_comm S.a12 S.a21, Int.mul_one]
    omega
  · rw [Int.mul_neg, Int.mul_comm S.a12 S.a11, Int.mul_zero]
    omega
  · rw [Int.mul_neg, Int.mul_comm S.a22 S.a21, Int.mul_zero]
    omega
  · rw [Int.mul_neg, Int.mul_comm S.a21 S.a12, Int.mul_comm S.a22 S.a11, Int.mul_one]
    omega

theorem mul_adj_left (S : Mat2) : mul (adj S) S = scale (det S) id2 := by
  rw [ext_iff]
  dsimp [mul, adj, scale, id2, diag, det]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Int.neg_mul, Int.mul_comm S.a22 S.a11, Int.mul_comm S.a12 S.a21, Int.mul_one]
    omega
  · rw [Int.neg_mul, Int.mul_comm S.a22 S.a12, Int.mul_zero]
    omega
  · rw [Int.neg_mul, Int.mul_comm S.a21 S.a11, Int.mul_zero]
    omega
  · rw [Int.neg_mul, Int.mul_comm S.a21 S.a12, Int.mul_one]
    omega

theorem mul_scale_id_left (c : Int) (M : Mat2) :
    mul (scale c id2) M = scale c M := by
  rw [ext_iff]
  dsimp [mul, scale, id2, diag]
  simp [Int.mul_one, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add]

theorem mul_scale_id_right (M : Mat2) (c : Int) :
    mul M (scale c id2) = scale c M := by
  rw [ext_iff]
  dsimp [mul, scale, id2, diag]
  simp [Int.mul_one, Int.mul_zero, Int.add_zero, Int.zero_add]
  exact ⟨Int.mul_comm M.a11 c, Int.mul_comm M.a12 c,
         Int.mul_comm M.a21 c, Int.mul_comm M.a22 c⟩

theorem tr_scale (c : Int) (M : Mat2) : tr (scale c M) = c * tr M := by
  dsimp [tr, scale]
  rw [Int.mul_add]

/-- Universal theorem: No defective 2x2 matrix is similar to ANY diagonal matrix. -/
theorem defective_not_similar_to_diag {M : Mat2} (hdef : IsDefective M) :
    ¬ SimilarToDiagInt M := by
  rintro ⟨S, l1, l2, hdetS, hSM⟩
  rcases hdef with ⟨_hdisc, hnotScalar⟩
  have hdet_eq : det S * det M = det S * (l1 * l2) := by
    have h1 := congrArg det hSM
    rw [det_mul, det_mul] at h1
    have hd : det (diag l1 l2) = l1 * l2 := by
      dsimp [det, diag]
      omega
    rw [hd, Int.mul_comm (l1 * l2) (det S)] at h1
    exact h1
  have hdetM : det M = l1 * l2 := Int.eq_of_mul_eq_mul_left hdetS hdet_eq
  have htr_eq : det S * tr M = det S * (l1 + l2) := by
    have h2 := congrArg (fun X => tr (mul X (adj S))) hSM
    dsimp only at h2
    have hlhs : tr (mul (mul S M) (adj S)) = det S * tr M := by
      rw [mul_assoc S M (adj S), tr_mul_comm S (mul M (adj S)),
          mul_assoc M (adj S) S, mul_adj_left S, mul_scale_id_right M (det S),
          tr_scale]
    have hrhs : tr (mul (mul (diag l1 l2) S) (adj S)) = det S * (l1 + l2) := by
      rw [mul_assoc (diag l1 l2) S (adj S), mul_adj_right S,
          mul_scale_id_right (diag l1 l2) (det S), tr_scale]
      rfl
    rw [hlhs, hrhs] at h2
    exact h2
  have htrM : tr M = l1 + l2 := Int.eq_of_mul_eq_mul_left hdetS htr_eq
  have hl_diff_sq : (l1 - l2) ^ 2 = 0 := by
    rw [sub_sq]
    have hsum_sq : (l1 + l2) ^ 2 = l1 ^ 2 + l2 ^ 2 + 2 * (l1 * l2) := add_sq l1 l2
    rw [← htrM, ← hdetM] at hsum_sq
    omega
  have hl_eq : l1 = l2 := by
    rcases Int.lt_trichotomy (l1 - l2) 0 with hlt | heq | hgt
    · have _hp := sq_pos_of_ne_zero (by omega : l1 - l2 ≠ 0)
      omega
    · omega
    · have _hp := sq_pos_of_ne_zero (by omega : l1 - l2 ≠ 0)
      omega
  have hdiag_scalar : mul (diag l1 l2) S = mul S (scale l1 id2) := by
    subst hl_eq
    rw [mul_scale_id_right S l1, ext_iff]
    dsimp [mul, diag, scale]
    simp [Int.zero_mul, Int.add_zero, Int.zero_add]
  rw [hdiag_scalar] at hSM
  have hleft := congrArg (mul (adj S)) hSM
  rw [← mul_assoc (adj S) S M, ← mul_assoc (adj S) S (scale l1 id2),
      mul_adj_left S, mul_scale_id_left (det S) M,
      mul_scale_id_left (det S) (scale l1 id2)] at hleft
  rw [ext_iff] at hleft
  rcases hleft with ⟨e11, e12, e21, e22⟩
  dsimp [scale, id2, diag] at e11 e12 e21 e22
  have _m11 : M.a11 = l1 * 1 := Int.eq_of_mul_eq_mul_left hdetS e11
  have _m12 : M.a12 = l1 * 0 := Int.eq_of_mul_eq_mul_left hdetS e12
  have _m21 : M.a21 = l1 * 0 := Int.eq_of_mul_eq_mul_left hdetS e21
  have _m22 : M.a22 = l1 * 1 := Int.eq_of_mul_eq_mul_left hdetS e22
  apply hnotScalar
  exact ⟨by omega, by omega, by omega⟩

end Mat2

/-! ### Majorization Definitions on Non-Increasing Non-Negative Pairs -/

/-- Additive weak majorization `(x1, x2) ≺_w (y1, y2)` on sorted pairs. -/
def WeakMajorizes2 (x1 x2 y1 y2 : Int) : Prop :=
  x1 ≤ y1 ∧ x1 + x2 ≤ y1 + y2

/-- Additive majorization `(x1, x2) ≺ (y1, y2)` on sorted pairs. -/
def Majorizes2 (x1 x2 y1 y2 : Int) : Prop :=
  x1 ≤ y1 ∧ x1 + x2 = y1 + y2

/-- Multiplicative weak log-majorization `(x1, x2) ≺_{w log} (y1, y2)` on sorted pairs. -/
def WeakLogMajorizes2 (x1 x2 y1 y2 : Int) : Prop :=
  x1 ≤ y1 ∧ x1 * x2 ≤ y1 * y2

instance (x1 x2 y1 y2 : Int) : Decidable (WeakLogMajorizes2 x1 x2 y1 y2) :=
  inferInstanceAs (Decidable (x1 ≤ y1 ∧ x1 * x2 ≤ y1 * y2))

/-- Logarithmic majorization `(x1, x2) ≺_{log} (y1, y2)` on sorted non-negative pairs:
    `x1 ≤ y1` at `k = 1` and `x1 * x2 = y1 * y2` at `k = 2`. -/
def LogMajorizes2 (x1 x2 y1 y2 : Int) : Prop :=
  x1 ≤ y1 ∧ x1 * x2 = y1 * y2

instance (x1 x2 y1 y2 : Int) : Decidable (LogMajorizes2 x1 x2 y1 y2) :=
  inferInstanceAs (Decidable (x1 ≤ y1 ∧ x1 * x2 = y1 * y2))

/-- Equality in every partial product of logarithmic majorization (`k = 1, 2`). -/
def LogMajorizesEq2 (x1 x2 y1 y2 : Int) : Prop :=
  x1 = y1 ∧ x1 * x2 = y1 * y2

instance (x1 x2 y1 y2 : Int) : Decidable (LogMajorizesEq2 x1 x2 y1 y2) :=
  inferInstanceAs (Decidable (x1 = y1 ∧ x1 * x2 = y1 * y2))

/-- Logarithmic majorization strictly strengthens additive weak majorization. -/
theorem logMajorizes2_implies_weakMajorizes2
    {x1 x2 y1 y2 : Int}
    (hx_ord : x2 ≤ x1) (hy_ord : y2 ≤ y1) (hx0 : 0 ≤ x2) (hy0 : 0 ≤ y2)
    (hlog : LogMajorizes2 x1 x2 y1 y2) :
    WeakMajorizes2 x1 x2 y1 y2 := by
  rcases hlog with ⟨hle, hprod⟩
  exact ⟨hle, sum_le_of_le_of_prod_eq hx_ord hy_ord hx0 hy0 hle hprod⟩

/-! ### Exact Singular Value Characterization and Uniqueness -/

/-- `(s1, s2)` are the singular values of `M` iff `s1 ≥ s2 ≥ 0` and `(s1^2, s2^2)`
    are the exact roots of the characteristic polynomial of `M^T M`
    (i.e. `s1^2 + s2^2 = tr(M^T M)` and `(s1 * s2)^2 = det(M^T M)`). -/
def HasSingularValues (M : Mat2) (s1 s2 : Int) : Prop :=
  0 ≤ s2 ∧ s2 ≤ s1 ∧
    s1 ^ 2 + s2 ^ 2 = Mat2.frobSq M ∧
    (s1 * s2) ^ 2 = Mat2.det (Mat2.mul (Mat2.transpose M) M)

instance (M : Mat2) (s1 s2 : Int) : Decidable (HasSingularValues M s1 s2) :=
  inferInstanceAs (Decidable (0 ≤ s2 ∧ s2 ≤ s1 ∧
    s1 ^ 2 + s2 ^ 2 = Mat2.frobSq M ∧
    (s1 * s2) ^ 2 = Mat2.det (Mat2.mul (Mat2.transpose M) M)))

/-- Singular values are uniquely determined by `M`. -/
theorem hasSingularValues_unique {M : Mat2} {s1 s2 t1 t2 : Int}
    (hs : HasSingularValues M s1 s2) (ht : HasSingularValues M t1 t2) :
    s1 = t1 ∧ s2 = t2 := by
  rcases hs with ⟨hs2_0, _hs_ord, _hs_sum, _hs_prod⟩
  rcases ht with ⟨ht2_0, _ht_ord, _ht_sum, _ht_prod⟩
  have hs1_0 : 0 ≤ s1 := by omega
  have ht1_0 : 0 ≤ t1 := by omega
  have hprod_eq : s1 * s2 = t1 * t2 := by
    apply eq_of_sq_eq_of_nonneg (Int.mul_nonneg hs1_0 hs2_0) (Int.mul_nonneg ht1_0 ht2_0)
    omega
  have _hsum_eq : s1 + s2 = t1 + t2 := by
    apply eq_of_sq_eq_of_nonneg (by omega) (by omega)
    rw [add_sq, add_sq, hprod_eq]
    omega
  have _hdiff_eq : s1 - s2 = t1 - t2 := by
    apply eq_of_sq_eq_of_nonneg (by omega) (by omega)
    rw [sub_sq, sub_sq, hprod_eq]
    omega
  omega

/-- Singular values of a sorted non-negative diagonal matrix `diag d1 d2`. -/
theorem hasSingularValues_diag {d1 d2 : Int} (hd2 : 0 ≤ d2) (hord : d2 ≤ d1) :
    HasSingularValues (Mat2.diag d1 d2) d1 d2 := by
  refine ⟨hd2, hord, ?_, ?_⟩
  · rw [Mat2.frobSq_eq_sum_sq]
    dsimp [Mat2.diag]
    omega
  · rw [Mat2.det_gram_eq_det_sq]
    dsimp [Mat2.det, Mat2.diag]
    have hd : d1 * d2 - 0 = d1 * d2 := by omega
    rw [hd]

/-! ### Universal 2x2 Horn-Lidskii Product Log-Majorization & Exact Equality Theorem -/

abbrev gramLeft (A : Mat2) : Mat2 := Mat2.mul (Mat2.transpose A) A
abbrev gramRight (B : Mat2) : Mat2 := Mat2.mul B (Mat2.transpose B)

/-- Spectral alignment of the traceless parts of `A^T A` and `B B^T`. -/
def GramAligned (A B : Mat2) : Prop :=
  0 ≤ ((gramLeft A).a11 - (gramLeft A).a22) * ((gramRight B).a11 - (gramRight B).a22) +
    4 * ((gramLeft A).a12 * (gramRight B).a12)

private theorem gram_left_sym (A : Mat2) :
    (gramLeft A).a21 = (gramLeft A).a12 := by
  dsimp [gramLeft, Mat2.mul, Mat2.transpose]
  rw [Int.mul_comm A.a12 A.a11, Int.mul_comm A.a22 A.a21]

private theorem gram_right_sym (B : Mat2) :
    (gramRight B).a21 = (gramRight B).a12 := by
  dsimp [gramRight, Mat2.mul, Mat2.transpose]
  rw [Int.mul_comm B.a21 B.a11, Int.mul_comm B.a22 B.a12]

private theorem gram_right_tr_eq (B : Mat2) :
    (gramRight B).a11 + (gramRight B).a22 = Mat2.frobSq B := by
  change Mat2.tr (gramRight B) = Mat2.frobSq B
  exact Mat2.tr_mul_comm B (Mat2.transpose B)

private theorem gram_right_det_eq (B : Mat2) :
    (gramRight B).a11 * (gramRight B).a22 - (gramRight B).a12 * (gramRight B).a21 =
      Mat2.det (gramLeft B) := by
  change Mat2.det (gramRight B) = Mat2.det (gramLeft B)
  rw [Mat2.det_mul, Mat2.det_mul, Mat2.det_transpose, Int.mul_comm]

private theorem sym_gram_trace_identity
    (G H : Mat2) (hq : G.a21 = G.a12) (hv : H.a21 = H.a12) :
    2 * Mat2.tr (Mat2.mul G H) - (G.a11 + G.a22) * (H.a11 + H.a22) =
      (G.a11 - G.a22) * (H.a11 - H.a22) + 4 * (G.a12 * H.a12) := by
  cases G with | mk p q12 q21 r =>
  cases H with | mk u v12 v21 w =>
  dsimp only at hq hv ⊢
  rw [hq, hv]
  dsimp [Mat2.tr, Mat2.mul]
  rw [Mat2.add_mul_add, Mat2.sub_mul_sub]
  omega

private theorem sym_gram_disc_identity
    {p q12 q21 r s1 s2 : Int}
    (hq : q21 = q12)
    (hsum : s1 ^ 2 + s2 ^ 2 = p + r)
    (hprod : (s1 * s2) ^ 2 = p * r - q12 * q21) :
    (s1 ^ 2 - s2 ^ 2) ^ 2 = (p - r) ^ 2 + (2 * q12) ^ 2 := by
  rw [hq] at hprod
  have h1 : (s1 ^ 2 + s2 ^ 2) ^ 2 - (s1 ^ 2 - s2 ^ 2) ^ 2 = 4 * ((s1 * s2) ^ 2) := by
    rw [add_sq, sub_sq, mul_pow_two]
    omega
  have _h2 : (p + r) ^ 2 - 4 * (p * r - q12 * q12) = (p - r) ^ 2 + (2 * q12) ^ 2 := by
    rw [add_sq, sub_sq, mul_pow_two, sq_eq_mul_self 2, sq_eq_mul_self q12]
    omega
  rw [hsum, hprod] at h1
  omega

private theorem sym_gram_comm_iff
    (G H : Mat2) (hq : G.a21 = G.a12) (hv : H.a21 = H.a12) :
    Mat2.mul G H = Mat2.mul H G ↔
      (G.a11 - G.a22) * H.a12 = G.a12 * (H.a11 - H.a22) := by
  cases G with | mk p q12 q21 r =>
  cases H with | mk u v12 v21 w =>
  dsimp only at hq hv ⊢
  rw [hq, hv, Mat2.ext_iff]
  dsimp [Mat2.mul]
  have hc11 : p * u + q12 * v12 = u * p + v12 * q12 := by
    rw [Int.mul_comm p u, Int.mul_comm q12 v12]
  have hc22 : q12 * v12 + r * w = v12 * q12 + w * r := by
    rw [Int.mul_comm q12 v12, Int.mul_comm r w]
  have _hdiff1 : (p - r) * v12 = p * v12 - r * v12 := Int.sub_mul p r v12
  have _hdiff2 : q12 * (u - w) = q12 * u - q12 * w := Int.mul_sub q12 u w
  have _hcomm_uq : u * q12 = q12 * u := Int.mul_comm u q12
  have _hcomm_vr : v12 * r = r * v12 := Int.mul_comm v12 r
  have _hcomm_vp : v12 * p = p * v12 := Int.mul_comm v12 p
  have _hcomm_wq : w * q12 = q12 * w := Int.mul_comm w q12
  constructor
  · rintro ⟨_, _h12, _, _⟩
    omega
  · intro _heq
    refine ⟨hc11, by omega, by omega, hc22⟩

/-- Core inequality: `c1^2 + c2^2 ≤ a1^2 * b1^2 + a2^2 * b2^2` for all `A, B : Mat2`. -/
theorem lidskii_frobSq_majorization {A B : Mat2} {a1 a2 b1 b2 c1 c2 : Int}
    (hA : HasSingularValues A a1 a2)
    (hB : HasSingularValues B b1 b2)
    (hAB : HasSingularValues (Mat2.mul A B) c1 c2) :
    c1 ^ 2 + c2 ^ 2 ≤ (a1 * b1) ^ 2 + (a2 * b2) ^ 2 := by
  rcases hA with ⟨_ha2_0, _ha_ord, ha_sum, ha_prod⟩
  rcases hB with ⟨_hb2_0, _hb_ord, hb_sum, hb_prod⟩
  rcases hAB with ⟨_, _, hc_sum, _⟩
  have hGA_sym : (gramLeft A).a21 = (gramLeft A).a12 := gram_left_sym A
  have hGB_sym : (gramRight B).a21 = (gramRight B).a12 := gram_right_sym B
  have hGA_tr : a1 ^ 2 + a2 ^ 2 = (gramLeft A).a11 + (gramLeft A).a22 := ha_sum
  have hGB_tr : b1 ^ 2 + b2 ^ 2 = (gramRight B).a11 + (gramRight B).a22 :=
    hb_sum.trans (gram_right_tr_eq B).symm
  have hGB_det : (b1 * b2) ^ 2 =
      (gramRight B).a11 * (gramRight B).a22 - (gramRight B).a12 * (gramRight B).a21 :=
    hb_prod.trans (gram_right_det_eq B).symm
  have hdiscA := sym_gram_disc_identity hGA_sym hGA_tr ha_prod
  have hdiscB := sym_gram_disc_identity hGB_sym hGB_tr hGB_det
  have htrAB : c1 ^ 2 + c2 ^ 2 = Mat2.tr (Mat2.mul (gramLeft A) (gramRight B)) := by
    rw [hc_sum, Mat2.frobSq_mul_eq_tr_grams]
  have hid := sym_gram_trace_identity (gramLeft A) (gramRight B) hGA_sym hGB_sym
  have hbf := brahmagupta_fibonacci
    ((gramLeft A).a11 - (gramLeft A).a22) (2 * (gramLeft A).a12)
    ((gramRight B).a11 - (gramRight B).a22) (2 * (gramRight B).a12)
  have h2q2v : (2 * (gramLeft A).a12) * (2 * (gramRight B).a12) =
      4 * ((gramLeft A).a12 * (gramRight B).a12) := by
    rw [Mat2.mul4_swap23 2 (gramLeft A).a12 2 (gramRight B).a12]
    omega
  rw [h2q2v, ← hdiscA, ← hdiscB, ← mul_pow_two] at hbf
  have hsq_le : (((gramLeft A).a11 - (gramLeft A).a22) * ((gramRight B).a11 - (gramRight B).a22) +
      4 * ((gramLeft A).a12 * (gramRight B).a12)) ^ 2 ≤
      ((a1 ^ 2 - a2 ^ 2) * (b1 ^ 2 - b2 ^ 2)) ^ 2 := by
    have _hrem := sq_nonneg
      (((gramLeft A).a11 - (gramLeft A).a22) * (2 * (gramRight B).a12) -
        (2 * (gramLeft A).a12) * ((gramRight B).a11 - (gramRight B).a22))
    omega
  have ha_diff_0 : 0 ≤ a1 ^ 2 - a2 ^ 2 := by
    have _hdiff : (a1 - a2) * (a1 + a2) = a1 ^ 2 - a2 ^ 2 := by
      rw [sq_eq_mul_self, sq_eq_mul_self, diff_sq]
    have _hpos : 0 ≤ (a1 - a2) * (a1 + a2) := Int.mul_nonneg (by omega) (by omega)
    omega
  have hb_diff_0 : 0 ≤ b1 ^ 2 - b2 ^ 2 := by
    have _hdiff : (b1 - b2) * (b1 + b2) = b1 ^ 2 - b2 ^ 2 := by
      rw [sq_eq_mul_self, sq_eq_mul_self, diff_sq]
    have _hpos : 0 ≤ (b1 - b2) * (b1 + b2) := Int.mul_nonneg (by omega) (by omega)
    omega
  have _hlin_le := le_of_sq_le_of_nonneg (Int.mul_nonneg ha_diff_0 hb_diff_0) hsq_le
  have _htarget :
      (a1 ^ 2 + a2 ^ 2) * (b1 ^ 2 + b2 ^ 2) + (a1 ^ 2 - a2 ^ 2) * (b1 ^ 2 - b2 ^ 2) =
        2 * ((a1 * b1) ^ 2 + (a2 * b2) ^ 2) := by
    rw [Mat2.add_mul_add, Mat2.sub_mul_sub, mul_pow_two, mul_pow_two]
    omega
  rw [← hGA_tr, ← hGB_tr, ← htrAB] at hid
  omega

/-- **Universal 2x2 Horn-Lidskii Product Log-Majorization Theorem**:
    For all `A, B : Mat2`, the singular values of `AB` are logarithmically majorized
    by the entrywise product of the singular values of `A` and `B`:
    `c1 ≤ a1 * b1` and `c1 * c2 = (a1 * b1) * (a2 * b2)`. -/
theorem lidskii_product_log_majorization {A B : Mat2} {a1 a2 b1 b2 c1 c2 : Int}
    (hA : HasSingularValues A a1 a2)
    (hB : HasSingularValues B b1 b2)
    (hAB : HasSingularValues (Mat2.mul A B) c1 c2) :
    LogMajorizes2 c1 c2 (a1 * b1) (a2 * b2) := by
  have hfrob := lidskii_frobSq_majorization hA hB hAB
  rcases hA with ⟨ha2_0, ha_ord, _, ha_prod⟩
  rcases hB with ⟨hb2_0, hb_ord, _, hb_prod⟩
  rcases hAB with ⟨hc2_0, _hc_ord, _, hc_prod⟩
  have hprod_sq : (c1 * c2) ^ 2 = ((a1 * b1) * (a2 * b2)) ^ 2 := by
    rw [hc_prod, Mat2.det_gram_eq_det_sq, Mat2.det_mul, mul_pow_two,
        ← Mat2.det_gram_eq_det_sq A, ← Mat2.det_gram_eq_det_sq B,
        ← ha_prod, ← hb_prod, ← mul_pow_two, Mat2.mul4_swap23]
  have ha1_0 : 0 ≤ a1 := by omega
  have hb1_0 : 0 ≤ b1 := by omega
  have hc1_0 : 0 ≤ c1 := by omega
  have hprod_eq : c1 * c2 = (a1 * b1) * (a2 * b2) :=
    eq_of_sq_eq_of_nonneg (Int.mul_nonneg hc1_0 hc2_0)
      (Int.mul_nonneg (Int.mul_nonneg ha1_0 hb1_0) (Int.mul_nonneg ha2_0 hb2_0))
      hprod_sq
  have hc_ord_sq : c2 ^ 2 ≤ c1 ^ 2 := by
    have _hd : (c1 - c2) * (c1 + c2) = c1 ^ 2 - c2 ^ 2 := by
      rw [sq_eq_mul_self, sq_eq_mul_self, diff_sq]
    have _hp := Int.mul_nonneg (by omega : 0 ≤ c1 - c2) (by omega : 0 ≤ c1 + c2)
    omega
  have _hab_ord : a2 * b2 ≤ a1 * b1 := by
    have _h1 : a2 * b2 ≤ a1 * b2 := Int.mul_le_mul_of_nonneg_right ha_ord hb2_0
    have _h2 : a1 * b2 ≤ a1 * b1 := Int.mul_le_mul_of_nonneg_left hb_ord ha1_0
    omega
  have hab_sum_0 : 0 ≤ a1 * b1 + a2 * b2 := by
    have _p1 := Int.mul_nonneg ha1_0 hb1_0
    have _p2 := Int.mul_nonneg ha2_0 hb2_0
    omega
  have hab_ord_sq : (a2 * b2) ^ 2 ≤ (a1 * b1) ^ 2 := by
    have _hd : (a1 * b1 - a2 * b2) * (a1 * b1 + a2 * b2) = (a1 * b1) ^ 2 - (a2 * b2) ^ 2 := by
      rw [sq_eq_mul_self, sq_eq_mul_self, diff_sq]
    have _hp := Int.mul_nonneg (by omega : 0 ≤ a1 * b1 - a2 * b2) hab_sum_0
    omega
  have hprod_sq_pair : c1 ^ 2 * c2 ^ 2 = (a1 * b1) ^ 2 * (a2 * b2) ^ 2 := by
    rw [← mul_pow_two, ← mul_pow_two, hprod_sq]
  have hc1_sq_le : c1 ^ 2 ≤ (a1 * b1) ^ 2 :=
    pair_domination_of_sum_le_of_prod_eq hc_ord_sq hab_ord_sq
      (sq_nonneg c2) (sq_nonneg (a2 * b2)) hprod_sq_pair hfrob
  have hc1_le : c1 ≤ a1 * b1 :=
    le_of_sq_le_of_nonneg (Int.mul_nonneg ha1_0 hb1_0) hc1_sq_le
  exact ⟨hc1_le, hprod_eq⟩

/-- **Exact Necessary and Sufficient Equality Characterization Theorem**:
    For distinct singular values `a1 > a2` and `b1 > b2`, exact singular-value product
    equality `(c1, c2) = (a1 * b1, a2 * b2)` holds **if and only if** `A^T A` commutes
    with `B B^T` and their traceless parts are positively aligned (`GramAligned A B`). -/
theorem lidskii_product_eq_iff_gram_aligned {A B : Mat2} {a1 a2 b1 b2 c1 c2 : Int}
    (hA : HasSingularValues A a1 a2)
    (hB : HasSingularValues B b1 b2)
    (hAB : HasSingularValues (Mat2.mul A B) c1 c2)
    (ha_strict : a2 < a1) (hb_strict : b2 < b1) :
    (c1 = a1 * b1 ∧ c2 = a2 * b2) ↔
      (Mat2.mul (gramLeft A) (gramRight B) = Mat2.mul (gramRight B) (gramLeft A) ∧
       GramAligned A B) := by
  have hlog := lidskii_product_log_majorization hA hB hAB
  rcases hA with ⟨ha2_0, ha_ord, ha_sum, ha_prod⟩
  rcases hB with ⟨hb2_0, hb_ord, hb_sum, hb_prod⟩
  rcases hAB with ⟨hc2_0, _hc_ord, hc_sum, _⟩
  have hGA_sym : (gramLeft A).a21 = (gramLeft A).a12 := gram_left_sym A
  have hGB_sym : (gramRight B).a21 = (gramRight B).a12 := gram_right_sym B
  have hGA_tr : a1 ^ 2 + a2 ^ 2 = (gramLeft A).a11 + (gramLeft A).a22 := ha_sum
  have hGB_tr : b1 ^ 2 + b2 ^ 2 = (gramRight B).a11 + (gramRight B).a22 :=
    hb_sum.trans (gram_right_tr_eq B).symm
  have hGB_det : (b1 * b2) ^ 2 =
      (gramRight B).a11 * (gramRight B).a22 - (gramRight B).a12 * (gramRight B).a21 :=
    hb_prod.trans (gram_right_det_eq B).symm
  have hdiscA := sym_gram_disc_identity hGA_sym hGA_tr ha_prod
  have hdiscB := sym_gram_disc_identity hGB_sym hGB_tr hGB_det
  have htrAB : c1 ^ 2 + c2 ^ 2 = Mat2.tr (Mat2.mul (gramLeft A) (gramRight B)) := by
    rw [hc_sum, Mat2.frobSq_mul_eq_tr_grams]
  have hid := sym_gram_trace_identity (gramLeft A) (gramRight B) hGA_sym hGB_sym
  rw [← hGA_tr, ← hGB_tr, ← htrAB] at hid
  have hcomm_iff := sym_gram_comm_iff (gramLeft A) (gramRight B) hGA_sym hGB_sym
  have hbf := brahmagupta_fibonacci
    ((gramLeft A).a11 - (gramLeft A).a22) (2 * (gramLeft A).a12)
    ((gramRight B).a11 - (gramRight B).a22) (2 * (gramRight B).a12)
  have h2q2v : (2 * (gramLeft A).a12) * (2 * (gramRight B).a12) =
      4 * ((gramLeft A).a12 * (gramRight B).a12) := by
    rw [Mat2.mul4_swap23 2 (gramLeft A).a12 2 (gramRight B).a12]
    omega
  have hrem_eq :
      ((gramLeft A).a11 - (gramLeft A).a22) * (2 * (gramRight B).a12) -
        (2 * (gramLeft A).a12) * ((gramRight B).a11 - (gramRight B).a22) =
      2 * (((gramLeft A).a11 - (gramLeft A).a22) * (gramRight B).a12 -
        (gramLeft A).a12 * ((gramRight B).a11 - (gramRight B).a22)) := by
    rw [← Int.mul_assoc, Int.mul_comm ((gramLeft A).a11 - (gramLeft A).a22) 2, Int.mul_assoc,
        Int.mul_assoc 2 (gramLeft A).a12 ((gramRight B).a11 - (gramRight B).a22), ← Int.mul_sub]
  rw [h2q2v, hrem_eq, ← hdiscA, ← hdiscB, ← mul_pow_two] at hbf
  have _htarget :
      (a1 ^ 2 + a2 ^ 2) * (b1 ^ 2 + b2 ^ 2) + (a1 ^ 2 - a2 ^ 2) * (b1 ^ 2 - b2 ^ 2) =
        2 * ((a1 * b1) ^ 2 + (a2 * b2) ^ 2) := by
    rw [Mat2.add_mul_add, Mat2.sub_mul_sub, mul_pow_two, mul_pow_two]
    omega
  have ha_diff_pos : 0 < a1 ^ 2 - a2 ^ 2 := by
    have _hd : (a1 - a2) * (a1 + a2) = a1 ^ 2 - a2 ^ 2 := by
      rw [sq_eq_mul_self, sq_eq_mul_self, diff_sq]
    have _hp := Int.mul_pos (by omega : 0 < a1 - a2) (by omega : 0 < a1 + a2)
    omega
  have hb_diff_pos : 0 < b1 ^ 2 - b2 ^ 2 := by
    have _hd : (b1 - b2) * (b1 + b2) = b1 ^ 2 - b2 ^ 2 := by
      rw [sq_eq_mul_self, sq_eq_mul_self, diff_sq]
    have _hp := Int.mul_pos (by omega : 0 < b1 - b2) (by omega : 0 < b1 + b2)
    omega
  have hprod_pos : 0 < (a1 ^ 2 - a2 ^ 2) * (b1 ^ 2 - b2 ^ 2) :=
    Int.mul_pos ha_diff_pos hb_diff_pos
  constructor
  · rintro ⟨hc1, hc2⟩
    have _hsum_sq_eq : c1 ^ 2 + c2 ^ 2 = (a1 * b1) ^ 2 + (a2 * b2) ^ 2 := by
      rw [hc1, hc2]
    have hinner_eq :
        ((gramLeft A).a11 - (gramLeft A).a22) * ((gramRight B).a11 - (gramRight B).a22) +
          4 * ((gramLeft A).a12 * (gramRight B).a12) =
        (a1 ^ 2 - a2 ^ 2) * (b1 ^ 2 - b2 ^ 2) := by omega
    have _hrem_sq_zero :
        (2 * (((gramLeft A).a11 - (gramLeft A).a22) * (gramRight B).a12 -
          (gramLeft A).a12 * ((gramRight B).a11 - (gramRight B).a22))) ^ 2 = 0 := by
      rw [hinner_eq] at hbf
      omega
    have hrem_zero :
        ((gramLeft A).a11 - (gramLeft A).a22) * (gramRight B).a12 =
          (gramLeft A).a12 * ((gramRight B).a11 - (gramRight B).a22) := by
      rcases Int.lt_trichotomy
        (((gramLeft A).a11 - (gramLeft A).a22) * (gramRight B).a12)
        ((gramLeft A).a12 * ((gramRight B).a11 - (gramRight B).a22)) with hlt | heq | hgt
      · have hnz : 2 * (((gramLeft A).a11 - (gramLeft A).a22) * (gramRight B).a12 -
            (gramLeft A).a12 * ((gramRight B).a11 - (gramRight B).a22)) ≠ 0 := by omega
        have _hpos := sq_pos_of_ne_zero hnz
        omega
      · exact heq
      · have hnz : 2 * (((gramLeft A).a11 - (gramLeft A).a22) * (gramRight B).a12 -
            (gramLeft A).a12 * ((gramRight B).a11 - (gramRight B).a22)) ≠ 0 := by omega
        have _hpos := sq_pos_of_ne_zero hnz
        omega
    exact ⟨hcomm_iff.mpr hrem_zero, by dsimp [GramAligned]; omega⟩
  · rintro ⟨hcomm, halign⟩
    have hrem_zero :
        ((gramLeft A).a11 - (gramLeft A).a22) * (gramRight B).a12 -
          (gramLeft A).a12 * ((gramRight B).a11 - (gramRight B).a22) = 0 := by
      have _hc := hcomm_iff.mp hcomm
      omega
    have _hrem_sq_zero :
        (2 * (((gramLeft A).a11 - (gramLeft A).a22) * (gramRight B).a12 -
          (gramLeft A).a12 * ((gramRight B).a11 - (gramRight B).a22))) ^ 2 = 0 := by
      rw [hrem_zero, Int.mul_zero, sq_eq_mul_self 0, Int.mul_zero]
    have hsq_eq :
        (((gramLeft A).a11 - (gramLeft A).a22) * ((gramRight B).a11 - (gramRight B).a22) +
          4 * ((gramLeft A).a12 * (gramRight B).a12)) ^ 2 =
        ((a1 ^ 2 - a2 ^ 2) * (b1 ^ 2 - b2 ^ 2)) ^ 2 := by omega
    dsimp [GramAligned] at halign
    have _hinner_eq := eq_of_sq_eq_of_nonneg halign (Int.le_of_lt hprod_pos) hsq_eq
    have hsum_sq_eq : c1 ^ 2 + c2 ^ 2 = (a1 * b1) ^ 2 + (a2 * b2) ^ 2 := by omega
    have hc_ord_sq : c2 ^ 2 ≤ c1 ^ 2 := by
      have _hd : (c1 - c2) * (c1 + c2) = c1 ^ 2 - c2 ^ 2 := by
        rw [sq_eq_mul_self, sq_eq_mul_self, diff_sq]
      have _hp := Int.mul_nonneg (by omega : 0 ≤ c1 - c2) (by omega : 0 ≤ c1 + c2)
      omega
    have ha1_0 : 0 ≤ a1 := by omega
    have hb1_0 : 0 ≤ b1 := by omega
    have _hab_ord : a2 * b2 ≤ a1 * b1 := by
      have _h1 : a2 * b2 ≤ a1 * b2 := Int.mul_le_mul_of_nonneg_right ha_ord hb2_0
      have _h2 : a1 * b2 ≤ a1 * b1 := Int.mul_le_mul_of_nonneg_left hb_ord ha1_0
      omega
    have hab_sum_0 : 0 ≤ a1 * b1 + a2 * b2 := by
      have _p1 := Int.mul_nonneg ha1_0 hb1_0
      have _p2 := Int.mul_nonneg ha2_0 hb2_0
      omega
    have hab_ord_sq : (a2 * b2) ^ 2 ≤ (a1 * b1) ^ 2 := by
      have _hd : (a1 * b1 - a2 * b2) * (a1 * b1 + a2 * b2) = (a1 * b1) ^ 2 - (a2 * b2) ^ 2 := by
        rw [sq_eq_mul_self, sq_eq_mul_self, diff_sq]
      have _hp := Int.mul_nonneg (by omega : 0 ≤ a1 * b1 - a2 * b2) hab_sum_0
      omega
    have hprod_sq_pair : c1 ^ 2 * c2 ^ 2 = (a1 * b1) ^ 2 * (a2 * b2) ^ 2 := by
      rw [← mul_pow_two, ← mul_pow_two, hlog.2]
    rcases pair_eq_of_sum_eq_of_prod_eq hc_ord_sq hab_ord_sq hprod_sq_pair hsum_sq_eq with ⟨e1, e2⟩
    have hc1_0 : 0 ≤ c1 := by omega
    exact ⟨eq_of_sq_eq_of_nonneg hc1_0 (Int.mul_nonneg ha1_0 hb1_0) e1,
           eq_of_sq_eq_of_nonneg hc2_0 (Int.mul_nonneg ha2_0 hb2_0) e2⟩

/-! ### Universal 2x2 Weyl Eigenvalue-Singular-Value Log-Majorization -/

/-- `(l1, l2)` are the real/integer eigenvalues of `M` ordered by `|l1| ≥ |l2|`. -/
def HasRealEigenvalues (M : Mat2) (l1 l2 : Int) : Prop :=
  absInt l2 ≤ absInt l1 ∧
    l1 + l2 = Mat2.tr M ∧ l1 * l2 = Mat2.det M

instance (M : Mat2) (l1 l2 : Int) : Decidable (HasRealEigenvalues M l1 l2) :=
  inferInstanceAs (Decidable (absInt l2 ≤ absInt l1 ∧
    l1 + l2 = Mat2.tr M ∧ l1 * l2 = Mat2.det M))

/-- **Weyl's 2x2 Log-Majorization Theorem** (`|λ(M)| ≺_{log} σ(M)`) and its exact
    symmetry equality characterization on real-spectrum matrices. -/
theorem weyl_log_majorization {M : Mat2} {l1 l2 s1 s2 : Int}
    (heig : HasRealEigenvalues M l1 l2)
    (hsv : HasSingularValues M s1 s2) :
    LogMajorizes2 (absInt l1) (absInt l2) s1 s2 ∧
      ((absInt l1 = s1 ∧ absInt l2 = s2) ↔ Mat2.IsSymmetric M) := by
  rcases heig with ⟨_hl_ord, hl_sum, hl_prod⟩
  rcases hsv with ⟨hs2_0, _hs_ord, hs_sum, hs_prod⟩
  have hm2_0 : 0 ≤ absInt l2 := absInt_nonneg l2
  have hm1_0 : 0 ≤ absInt l1 := absInt_nonneg l1
  have hs1_0 : 0 ≤ s1 := by omega
  have hprod_sq : (absInt l1 * absInt l2) ^ 2 = (s1 * s2) ^ 2 := by
    rw [mul_pow_two, absInt_sq, absInt_sq, ← mul_pow_two, hl_prod,
        hs_prod, Mat2.det_gram_eq_det_sq]
  have hprod_eq : absInt l1 * absInt l2 = s1 * s2 :=
    eq_of_sq_eq_of_nonneg (Int.mul_nonneg hm1_0 hm2_0) (Int.mul_nonneg hs1_0 hs2_0) hprod_sq
  have hfrob_diff :
      (s1 ^ 2 + s2 ^ 2) - ((absInt l1) ^ 2 + (absInt l2) ^ 2) = (M.a12 - M.a21) ^ 2 := by
    rw [absInt_sq, absInt_sq, hs_sum, Mat2.frobSq_eq_sum_sq, sub_sq]
    have hlsq : (l1 + l2) ^ 2 = l1 ^ 2 + l2 ^ 2 + 2 * (l1 * l2) := add_sq l1 l2
    have _htrsq : (Mat2.tr M) ^ 2 = M.a11 ^ 2 + M.a22 ^ 2 + 2 * (M.a11 * M.a22) :=
      add_sq M.a11 M.a22
    rw [hl_sum, hl_prod] at hlsq
    dsimp [Mat2.det] at hlsq
    omega
  have hsum_le : (absInt l1) ^ 2 + (absInt l2) ^ 2 ≤ s1 ^ 2 + s2 ^ 2 := by
    have _hsq := sq_nonneg (M.a12 - M.a21)
    omega
  have hm_ord_sq : (absInt l2) ^ 2 ≤ (absInt l1) ^ 2 := by
    have _hd : (absInt l1 - absInt l2) * (absInt l1 + absInt l2) =
        (absInt l1) ^ 2 - (absInt l2) ^ 2 := by
      rw [sq_eq_mul_self, sq_eq_mul_self, diff_sq]
    have _hp := Int.mul_nonneg (by omega : 0 ≤ absInt l1 - absInt l2)
      (by omega : 0 ≤ absInt l1 + absInt l2)
    omega
  have hs_ord_sq : s2 ^ 2 ≤ s1 ^ 2 := by
    have _hd : (s1 - s2) * (s1 + s2) = s1 ^ 2 - s2 ^ 2 := by
      rw [sq_eq_mul_self, sq_eq_mul_self, diff_sq]
    have _hp := Int.mul_nonneg (by omega : 0 ≤ s1 - s2) (by omega : 0 ≤ s1 + s2)
    omega
  have hprod_sq_pair : (absInt l1) ^ 2 * (absInt l2) ^ 2 = s1 ^ 2 * s2 ^ 2 := by
    rw [← mul_pow_two, ← mul_pow_two, hprod_sq]
  have hm1_sq_le := pair_domination_of_sum_le_of_prod_eq hm_ord_sq hs_ord_sq
    (sq_nonneg (absInt l2)) (sq_nonneg s2) hprod_sq_pair hsum_le
  have hm1_le := le_of_sq_le_of_nonneg hs1_0 hm1_sq_le
  refine ⟨⟨hm1_le, hprod_eq⟩, ?_⟩
  constructor
  · rintro ⟨e1, e2⟩
    have _hsq0 : (M.a12 - M.a21) ^ 2 = 0 := by
      rw [e1, e2] at hfrob_diff
      omega
    have heq12 : M.a12 = M.a21 := by
      rcases Int.lt_trichotomy M.a12 M.a21 with hlt | heq | hgt
      · have _hpos := sq_pos_of_ne_zero (by omega : M.a12 - M.a21 ≠ 0)
        omega
      · exact heq
      · have _hpos := sq_pos_of_ne_zero (by omega : M.a12 - M.a21 ≠ 0)
        omega
    dsimp [Mat2.IsSymmetric, Mat2.transpose]
    rw [Mat2.ext_iff]
    exact ⟨rfl, heq12.symm, heq12, rfl⟩
  · intro hsym
    dsimp [Mat2.IsSymmetric, Mat2.transpose] at hsym
    rw [Mat2.ext_iff] at hsym
    rcases hsym with ⟨_, _h12, _, _⟩
    dsimp only at _h12
    have hsum_eq : (absInt l1) ^ 2 + (absInt l2) ^ 2 = s1 ^ 2 + s2 ^ 2 := by
      have hz : M.a12 - M.a21 = 0 := by omega
      have h0 : (0 : Int) ^ 2 = 0 := rfl
      rw [hz, h0] at hfrob_diff
      omega
    rcases pair_eq_of_sum_eq_of_prod_eq hm_ord_sq hs_ord_sq hprod_sq_pair hsum_eq with ⟨e1, e2⟩
    exact ⟨eq_of_sq_eq_of_nonneg hm1_0 hs1_0 e1,
           eq_of_sq_eq_of_nonneg hm2_0 hs2_0 e2⟩

/-! ### Ky Fan Diagonal-Pinching Equality Characterization -/

/-- Equality of sorted diagonal magnitudes `(|a11|, |a22|)` and singular values `(s1, s2)`
    forces `M` to be diagonal (`M.a12 = 0 ∧ M.a21 = 0`). -/
theorem diag_abs_eq_sv_implies_diagonal {M : Mat2} {d1 d2 s1 s2 : Int}
    (_hd_perm : d1 ^ 2 + d2 ^ 2 = M.a11 ^ 2 + M.a22 ^ 2)
    (hsv : HasSingularValues M s1 s2) :
    (d1 = s1 ∧ d2 = s2) → Mat2.IsDiagonal M := by
  rintro ⟨e1, e2⟩
  rcases hsv with ⟨_, _, hs_sum, _⟩
  rw [Mat2.frobSq_eq_sum_sq, ← e1, ← e2] at hs_sum
  have _hoff_zero : M.a12 ^ 2 + M.a21 ^ 2 = 0 := by omega
  have _h12_0 := sq_nonneg M.a12
  have _h21_0 := sq_nonneg M.a21
  have ha12 : M.a12 = 0 := by
    rcases Int.lt_trichotomy M.a12 0 with hlt | heq | hgt
    · have _hp := sq_pos_of_ne_zero (by omega : M.a12 ≠ 0)
      omega
    · exact heq
    · have _hp := sq_pos_of_ne_zero (by omega : M.a12 ≠ 0)
      omega
  have ha21 : M.a21 = 0 := by
    rcases Int.lt_trichotomy M.a21 0 with hlt | heq | hgt
    · have _hp := sq_pos_of_ne_zero (by omega : M.a21 ≠ 0)
      omega
    · exact heq
    · have _hp := sq_pos_of_ne_zero (by omega : M.a21 ≠ 0)
      omega
  exact ⟨ha12, ha21⟩

end LidskiiProduct
