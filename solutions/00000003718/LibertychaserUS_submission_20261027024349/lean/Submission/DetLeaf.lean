import Mathlib

set_option linter.unusedSectionVars false

/-!
# Determinant expansion along a "leaf" row

Let `M` be a square matrix indexed by a finite type `ι`, and let `v ≠ u` be two indices such that
row `v` and column `v` of `M` are supported on `{v, u}`.  Then

  `det M = M v v * det (M with v deleted) - M v u * M u v * det (M with v and u deleted)`.

This is the matrix form of the leaf recurrence for the characteristic polynomial of a forest.
-/

open Matrix

namespace TLMC3718

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The principal minor of `M` obtained by deleting the index `v`. -/
abbrev minor (M : Matrix ι ι R) (v : ι) : Matrix {x // x ≠ v} {x // x ≠ v} R :=
  M.submatrix Subtype.val Subtype.val

/-- The principal minor of `M` obtained by deleting the indices `v` and `u`. -/
abbrev minor₂ (M : Matrix ι ι R) (v u : ι) :
    Matrix {x // x ≠ v ∧ x ≠ u} {x // x ≠ v ∧ x ≠ u} R :=
  M.submatrix Subtype.val Subtype.val

/-- If row `v` of `M` vanishes off the diagonal, the determinant factors through the minor. -/
theorem det_eq_mul_det_minor_of_row (M : Matrix ι ι R) (v : ι)
    (h : ∀ w, w ≠ v → M v w = 0) : M.det = M v v * (minor M v).det := by
  classical
  let e : {x // x = v} ⊕ {x // ¬ x = v} ≃ ι := Equiv.sumCompl (· = v)
  have : Unique {x // x = v} := ⟨⟨⟨v, rfl⟩⟩, fun x => Subtype.ext x.2⟩
  rw [← det_submatrix_equiv_self e, ← fromBlocks_toBlocks (M.submatrix e e)]
  have h12 : (M.submatrix e e).toBlocks₁₂ = 0 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [toBlocks₁₂, of_apply, submatrix_apply, Matrix.zero_apply]
    subst hi
    exact h j hj
  rw [h12, det_fromBlocks_zero₁₂, det_unique]
  congr 1
  · show M (default : {x // x = v}).1 (default : {x // x = v}).1 = M v v
    rw [(default : {x // x = v}).2]

/-- Column version of `det_eq_mul_det_minor_of_row`. -/
theorem det_eq_mul_det_minor_of_col (M : Matrix ι ι R) (v : ι)
    (h : ∀ w, w ≠ v → M w v = 0) : M.det = M v v * (minor M v).det := by
  rw [← det_transpose M, det_eq_mul_det_minor_of_row Mᵀ v (fun w hw => h w hw)]
  rw [transpose_apply]
  congr 1
  rw [← det_transpose]
  rfl

/-- The leaf expansion of a determinant. -/
theorem det_leaf (M : Matrix ι ι R) (v u : ι) (hvu : v ≠ u)
    (hrow : ∀ w, w ≠ v → w ≠ u → M v w = 0)
    (hcol : ∀ w, w ≠ v → w ≠ u → M w v = 0) :
    M.det = M v v * (minor M v).det - M v u * M u v * (minor₂ M v u).det := by
  classical
  -- Step 1: split row `v`.
  have hrowv : M v = M v v • Pi.single v (1 : R) + M v u • Pi.single u (1 : R) := by
    funext w
    by_cases hwv : w = v
    · subst hwv; simp [hvu.symm]
    by_cases hwu : w = u
    · subst hwu; simp [hvu]
    · simp [hwv, hwu, hrow w hwv hwu]
  have hsplit : M.det = M v v * (M.updateRow v (Pi.single v 1)).det
      + M v u * (M.updateRow v (Pi.single u 1)).det := by
    conv_lhs => rw [← updateRow_eq_self M v, hrowv]
    rw [det_updateRow_add, det_updateRow_smul, det_updateRow_smul]
  -- Step 2: the first determinant is the minor.
  have h1 : (M.updateRow v (Pi.single v 1)).det = (minor M v).det := by
    rw [det_eq_mul_det_minor_of_row (M.updateRow v (Pi.single v 1)) v]
    · simp only [updateRow_self, Pi.single_eq_same, one_mul]
      congr 1
      ext ⟨a, ha⟩ ⟨b, hb⟩
      simp [minor, updateRow_ne ha]
    · intro w hw
      simp [hw]
  -- Step 3: the second determinant.
  set N := M.updateRow v (Pi.single u 1) with hN
  have hcolN : (fun w => N w v) = M u v • Pi.single u (1 : R) := by
    funext w
    by_cases hwv : w = v
    · subst hwv; simp [N, hvu]
    by_cases hwu : w = u
    · subst hwu; simp [N, updateRow_ne hvu.symm]
    · simp [N, updateRow_ne hwv, hwu, hcol w hwv hwu]
  have h2 : N.det = M u v * (N.updateCol v (Pi.single u 1)).det := by
    conv_lhs => rw [← updateCol_eq_self N v]
    rw [show (fun i => N i v) = M u v • Pi.single u (1 : R) from hcolN, det_updateCol_smul]
  set P := N.updateCol v (Pi.single u 1) with hP
  -- Step 4: swap rows `u` and `v` in `P`.
  have h3 : P.det = -(P.submatrix (Equiv.swap u v) id).det := by
    rw [det_permute, Equiv.Perm.sign_swap hvu.symm]
    simp
  set Q := P.submatrix (Equiv.swap u v) id with hQ
  -- Row `u` of `Q` is the unit vector at `u`.
  have hQrow : ∀ w, w ≠ u → Q u w = 0 := by
    intro w hw
    simp [Q, P, N, updateCol_apply, updateRow_apply, hw, hvu, Equiv.swap_apply_left]
  have hQuu : Q u u = 1 := by
    simp [Q, P, N, updateRow_apply, Equiv.swap_apply_left, hvu.symm]
  have h4 : Q.det = (minor Q u).det := by
    rw [det_eq_mul_det_minor_of_row Q u hQrow, hQuu, one_mul]
  -- Column `v` of `minor Q u` is the unit vector at `v`.
  have hv' : v ≠ u := hvu
  have hQcol : ∀ w : {x // x ≠ u}, w ≠ ⟨v, hv'⟩ → (minor Q u) w ⟨v, hv'⟩ = 0 := by
    rintro ⟨w, hwu⟩ hw
    have hwv : w ≠ v := fun h => hw (Subtype.ext h)
    simp [minor, Q, P, N, Equiv.swap_apply_of_ne_of_ne hwu hwv, hwu]
  have hQvv : (minor Q u) ⟨v, hv'⟩ ⟨v, hv'⟩ = 1 := by
    simp [minor, Q, P, N, Equiv.swap_apply_right]
  have h5 : (minor Q u).det = (minor (minor Q u) ⟨v, hv'⟩).det := by
    rw [det_eq_mul_det_minor_of_col (minor Q u) ⟨v, hv'⟩ hQcol, hQvv, one_mul]
  -- Step 5: identify the double minor.
  let f : {x // x ≠ v ∧ x ≠ u} ≃ {y : {x // x ≠ u} // y ≠ ⟨v, hv'⟩} :=
    { toFun := fun x => ⟨⟨x.1, x.2.2⟩, fun h => x.2.1 (congrArg Subtype.val h)⟩
      invFun := fun y => ⟨y.1.1, ⟨fun h => y.2 (Subtype.ext h), y.1.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have h6 : (minor (minor Q u) ⟨v, hv'⟩).det = (minor₂ M v u).det := by
    rw [← det_submatrix_equiv_self f]
    congr 1
    ext ⟨a, hav, hau⟩ ⟨b, hbv, hbu⟩
    simp [minor, minor₂, f, Q, P, N, Equiv.swap_apply_of_ne_of_ne hau hav,
      updateRow_ne hav, updateCol_ne hbv]
  rw [hsplit, h1, h2, h3, h4, h5, h6]
  ring

end TLMC3718
