/-
  Counterexamples.lean
  Exact polynomial basis transition verifications, positive low-degree power-of-two
  regimes, and explicit counterexamples across all standard multisymmetric bases
  (elementary `e_Λ`, complete homogeneous `h_Λ`, power-sum `p_Λ`, and augmented monomial `m̃_Λ`).
-/

import Conjecture00000000441.Multisymmetric

namespace Conjecture00000000441

/-! ### 1. Multidegree `d = (1, 1)` (`r = 2`, `N = 2`) -/

def parts_11 : List VecPart :=
  [[[1, 1]],
   [[1, 0], [0, 1]]]

def rows_e_11 : List (List Int) := [
  [0, 1],
  [1, 1]
]

def rows_h_11 : List (List Int) := [
  [2, 1],
  [1, 1]
]

def rows_p_11 : List (List Int) := [
  [1, 0],
  [1, 1]
]

abbrev M_e_11 : Mat 2 := matOfRows 2 rows_e_11
abbrev M_h_11 : Mat 2 := matOfRows 2 rows_h_11
abbrev M_p_11 : Mat 2 := matOfRows 2 rows_p_11

theorem basis_e_11 :
    IsBasisTransition 2 2 (fun j => parts_11.getD j.val [])
      (fun i => ePoly 2 2 [1, 1] (parts_11.getD i.val [])) M_e_11 :=
  checkBasisTransitionBool_sound 2 2 2 parts_11 (ePoly 2 2 [1, 1]) rows_e_11 rfl

theorem basis_h_11 :
    IsBasisTransition 2 2 (fun j => parts_11.getD j.val [])
      (fun i => hPoly 2 2 [1, 1] (parts_11.getD i.val [])) M_h_11 :=
  checkBasisTransitionBool_sound 2 2 2 parts_11 (hPoly 2 2 [1, 1]) rows_h_11 rfl

theorem basis_p_11 :
    IsBasisTransition 2 2 (fun j => parts_11.getD j.val [])
      (fun i => pPoly 2 2 [1, 1] (parts_11.getD i.val [])) M_p_11 :=
  checkBasisTransitionBool_sound 2 2 2 parts_11 (pPoly 2 2 [1, 1]) rows_p_11 rfl

theorem det_M_e_11 : det M_e_11 = -1 := by decide
theorem det_M_h_11 : det M_h_11 = 1 := by decide
theorem det_M_p_11 : det M_p_11 = 1 := by decide

theorem permTri_M_e_11 : IsPermTriangular M_e_11 := by
  left
  refine ⟨revPerm 2, ⟨id, id, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hij01 : i.val = 1 ∧ j.val = 0 := by omega
  rcases hij01 with ⟨hi1, hj0⟩
  have hi_eq : i = ⟨1, by decide⟩ := Fin.ext hi1
  have hj_eq : j = ⟨0, by decide⟩ := Fin.ext hj0
  subst hi_eq hj_eq
  decide

theorem not_permTri_M_h_11 : ¬IsPermTriangular M_h_11 :=
  not_permTriangular_via_two_nonzeros 2 (by decide) rows_h_11 (by decide)

/-! ### 2. Multidegree `d = (2, 1)` (`r = 2`, `N = 4`) -/

def parts_21 : List VecPart :=
  [[[2, 1]],
   [[2, 0], [0, 1]],
   [[1, 1], [1, 0]],
   [[1, 0], [1, 0], [0, 1]]]

def rows_e_21 : List (List Int) := [
  [0, 0, 0, 1],
  [0, 0, 1, 1],
  [0, 1, 1, 2],
  [1, 1, 2, 2]
]

def rows_h_21 : List (List Int) := [
  [3, 1, 2, 1],
  [1, 1, 1, 1],
  [2, 1, 3, 2],
  [1, 1, 2, 2]
]

def rows_p_21 : List (List Int) := [
  [1, 0, 0, 0],
  [1, 1, 0, 0],
  [1, 0, 1, 0],
  [1, 1, 2, 2]
]

abbrev M_e_21 : Mat 4 := matOfRows 4 rows_e_21
abbrev M_h_21 : Mat 4 := matOfRows 4 rows_h_21
abbrev M_p_21 : Mat 4 := matOfRows 4 rows_p_21

theorem basis_e_21 :
    IsBasisTransition 3 2 (fun j => parts_21.getD j.val [])
      (fun i => ePoly 3 2 [2, 1] (parts_21.getD i.val [])) M_e_21 :=
  checkBasisTransitionBool_sound 4 3 2 parts_21 (ePoly 3 2 [2, 1]) rows_e_21 rfl

theorem basis_h_21 :
    IsBasisTransition 3 2 (fun j => parts_21.getD j.val [])
      (fun i => hPoly 3 2 [2, 1] (parts_21.getD i.val [])) M_h_21 :=
  checkBasisTransitionBool_sound 4 3 2 parts_21 (hPoly 3 2 [2, 1]) rows_h_21 rfl

theorem basis_p_21 :
    IsBasisTransition 3 2 (fun j => parts_21.getD j.val [])
      (fun i => pPoly 3 2 [2, 1] (parts_21.getD i.val [])) M_p_21 :=
  checkBasisTransitionBool_sound 4 3 2 parts_21 (pPoly 3 2 [2, 1]) rows_p_21 rfl

theorem det_M_e_21 : det M_e_21 = 1 := by decide
theorem det_M_h_21 : det M_h_21 = 1 := by decide
theorem det_M_p_21 : det M_p_21 = 2 := det_matOfRows_lowerTri 4 rows_p_21 2 rfl

theorem permTri_M_e_21 : IsPermTriangular M_e_21 := by
  left
  refine ⟨revPerm 4, ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  have hup := checkUpperTriBool_sound 4 [
    [1, 1, 2, 2],
    [0, 1, 1, 2],
    [0, 0, 1, 1],
    [0, 0, 0, 1]
  ] rfl
  intro i j hij
  dsimp only
  have hrow : M_e_21 ((revPerm 4).toFun i) j =
      matOfRows 4 [[1, 1, 2, 2], [0, 1, 1, 2], [0, 0, 1, 1], [0, 0, 0, 1]] i j := by
    revert i j hij
    decide
  rw [hrow]
  exact hup i j hij

/-! ### 3. Multidegree `d = (1, 1, 1)` (`r = 3`, `N = 5`) -/

def parts_111 : List VecPart :=
  [[[1, 1, 1]],
   [[1, 1, 0], [0, 0, 1]],
   [[1, 0, 1], [0, 1, 0]],
   [[1, 0, 0], [0, 1, 1]],
   [[1, 0, 0], [0, 1, 0], [0, 0, 1]]]

def rows_e_111 : List (List Int) := [
  [0, 0, 0, 0, 1],
  [0, 0, 1, 1, 1],
  [0, 1, 0, 1, 1],
  [0, 1, 1, 0, 1],
  [1, 1, 1, 1, 1]
]

def ops_e_111 : List (RowOp 5) := [
  RowOp.swap ⟨0, by decide⟩ ⟨4, by decide⟩,
  RowOp.swap ⟨1, by decide⟩ ⟨2, by decide⟩,
  RowOp.addMul ⟨3, by decide⟩ ⟨1, by decide⟩ (-1),
  RowOp.addMul ⟨3, by decide⟩ ⟨2, by decide⟩ (-1)
]

def rows_h_111 : List (List Int) := [
  [6, 2, 2, 2, 1],
  [2, 2, 1, 1, 1],
  [2, 1, 2, 1, 1],
  [2, 1, 1, 2, 1],
  [1, 1, 1, 1, 1]
]

def ops_h_111 : List (RowOp 5) := [
  RowOp.swap ⟨0, by decide⟩ ⟨4, by decide⟩,
  RowOp.addMul ⟨1, by decide⟩ ⟨0, by decide⟩ (-2),
  RowOp.addMul ⟨2, by decide⟩ ⟨0, by decide⟩ (-2),
  RowOp.addMul ⟨3, by decide⟩ ⟨0, by decide⟩ (-2),
  RowOp.addMul ⟨4, by decide⟩ ⟨0, by decide⟩ (-6),
  RowOp.swap ⟨1, by decide⟩ ⟨2, by decide⟩,
  RowOp.addMul ⟨3, by decide⟩ ⟨1, by decide⟩ (-1),
  RowOp.addMul ⟨4, by decide⟩ ⟨1, by decide⟩ (-4),
  RowOp.addMul ⟨3, by decide⟩ ⟨2, by decide⟩ (-1),
  RowOp.addMul ⟨4, by decide⟩ ⟨2, by decide⟩ (-4),
  RowOp.addMul ⟨4, by decide⟩ ⟨3, by decide⟩ (-2)
]

def rows_p_111 : List (List Int) := [
  [1, 0, 0, 0, 0],
  [1, 1, 0, 0, 0],
  [1, 0, 1, 0, 0],
  [1, 0, 0, 1, 0],
  [1, 1, 1, 1, 1]
]

abbrev M_e_111 : Mat 5 := matOfRows 5 rows_e_111
abbrev M_h_111 : Mat 5 := matOfRows 5 rows_h_111
abbrev M_p_111 : Mat 5 := matOfRows 5 rows_p_111

theorem basis_e_111 :
    IsBasisTransition 3 3 (fun j => parts_111.getD j.val [])
      (fun i => ePoly 3 3 [1, 1, 1] (parts_111.getD i.val [])) M_e_111 :=
  checkBasisTransitionBool_sound 5 3 3 parts_111 (ePoly 3 3 [1, 1, 1]) rows_e_111 rfl

theorem basis_h_111 :
    IsBasisTransition 3 3 (fun j => parts_111.getD j.val [])
      (fun i => hPoly 3 3 [1, 1, 1] (parts_111.getD i.val [])) M_h_111 :=
  checkBasisTransitionBool_sound 5 3 3 parts_111 (hPoly 3 3 [1, 1, 1]) rows_h_111 rfl

theorem basis_p_111 :
    IsBasisTransition 3 3 (fun j => parts_111.getD j.val [])
      (fun i => pPoly 3 3 [1, 1, 1] (parts_111.getD i.val [])) M_p_111 :=
  checkBasisTransitionBool_sound 5 3 3 parts_111 (pPoly 3 3 [1, 1, 1]) rows_p_111 rfl

theorem det_M_e_111 : det M_e_111 = -2 :=
  det_matOfRows_via_ops 5 rows_e_111 ops_e_111 (-2) (by decide)

theorem det_M_h_111 : det M_h_111 = 2 :=
  det_matOfRows_via_ops 5 rows_h_111 ops_h_111 2 (by decide)

theorem det_M_p_111 : det M_p_111 = 1 :=
  det_matOfRows_lowerTri 5 rows_p_111 1 (by decide)

theorem not_permTri_M_e_111 : ¬IsPermTriangular M_e_111 :=
  not_permTriangular_via_singleton_row 5 (by decide) rows_e_111 ⟨0, by decide⟩ ⟨4, by decide⟩
    (by decide)

theorem not_permTri_M_h_111 : ¬IsPermTriangular M_h_111 :=
  not_permTriangular_via_two_nonzeros 5 (by decide) rows_h_111 (by decide)

/-! ### 4. Multidegree `d = (2, 2)` (`r = 2`, `N = 9`) -/

def parts_22 : List VecPart :=
  [[[2, 2]],
   [[2, 1], [0, 1]],
   [[2, 0], [0, 2]],
   [[2, 0], [0, 1], [0, 1]],
   [[1, 2], [1, 0]],
   [[1, 1], [1, 1]],
   [[1, 1], [1, 0], [0, 1]],
   [[1, 0], [1, 0], [0, 2]],
   [[1, 0], [1, 0], [0, 1], [0, 1]]]

def rows_e_22 : List (List Int) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 1, 1, 2],
  [0, 0, 0, 0, 0, 1, 1, 0, 1],
  [0, 0, 0, 0, 1, 2, 2, 1, 2],
  [0, 0, 0, 1, 0, 0, 1, 0, 2],
  [0, 0, 1, 2, 0, 2, 2, 2, 4],
  [0, 1, 1, 2, 1, 2, 3, 2, 4],
  [0, 1, 0, 1, 0, 2, 2, 0, 2],
  [1, 2, 1, 2, 2, 4, 4, 2, 4]
]

def ops_e_22 : List (RowOp 9) := [
  RowOp.swap ⟨0, by decide⟩ ⟨8, by decide⟩,
  RowOp.swap ⟨1, by decide⟩ ⟨6, by decide⟩,
  RowOp.addMul ⟨7, by decide⟩ ⟨1, by decide⟩ (-1),
  RowOp.swap ⟨2, by decide⟩ ⟨5, by decide⟩,
  RowOp.addMul ⟨7, by decide⟩ ⟨2, by decide⟩ 1,
  RowOp.swap ⟨3, by decide⟩ ⟨4, by decide⟩,
  RowOp.addMul ⟨7, by decide⟩ ⟨3, by decide⟩ (-1),
  RowOp.addMul ⟨7, by decide⟩ ⟨4, by decide⟩ 1,
  RowOp.addMul ⟨7, by decide⟩ ⟨5, by decide⟩ (-4),
  RowOp.addMul ⟨7, by decide⟩ ⟨6, by decide⟩ 2
]

def rows_h_22 : List (List Int) := [
  [6, 3, 1, 1, 3, 4, 2, 1, 1],
  [3, 4, 1, 2, 2, 4, 3, 1, 2],
  [1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 2, 1, 2, 1, 2, 2, 1, 2],
  [3, 2, 1, 1, 4, 4, 3, 2, 2],
  [4, 4, 1, 2, 4, 10, 6, 2, 4],
  [2, 3, 1, 2, 3, 6, 5, 2, 4],
  [1, 1, 1, 1, 2, 2, 2, 2, 2],
  [1, 2, 1, 2, 2, 4, 4, 2, 4]
]

def ops_h_22 : List (RowOp 9) := [
  RowOp.swap ⟨0, by decide⟩ ⟨2, by decide⟩,
  RowOp.addMul ⟨1, by decide⟩ ⟨0, by decide⟩ (-3),
  RowOp.addMul ⟨2, by decide⟩ ⟨0, by decide⟩ (-6),
  RowOp.addMul ⟨3, by decide⟩ ⟨0, by decide⟩ (-1),
  RowOp.addMul ⟨4, by decide⟩ ⟨0, by decide⟩ (-3),
  RowOp.addMul ⟨5, by decide⟩ ⟨0, by decide⟩ (-4),
  RowOp.addMul ⟨6, by decide⟩ ⟨0, by decide⟩ (-2),
  RowOp.addMul ⟨7, by decide⟩ ⟨0, by decide⟩ (-1),
  RowOp.addMul ⟨8, by decide⟩ ⟨0, by decide⟩ (-1),
  RowOp.addMul ⟨2, by decide⟩ ⟨1, by decide⟩ 3,
  RowOp.addMul ⟨3, by decide⟩ ⟨1, by decide⟩ (-1),
  RowOp.addMul ⟨4, by decide⟩ ⟨1, by decide⟩ 1,
  RowOp.addMul ⟨6, by decide⟩ ⟨1, by decide⟩ (-1),
  RowOp.addMul ⟨8, by decide⟩ ⟨1, by decide⟩ (-1),
  RowOp.swap ⟨2, by decide⟩ ⟨6, by decide⟩,
  RowOp.addMul ⟨3, by decide⟩ ⟨2, by decide⟩ (-2),
  RowOp.addMul ⟨4, by decide⟩ ⟨2, by decide⟩ 4,
  RowOp.addMul ⟨5, by decide⟩ ⟨2, by decide⟩ 3,
  RowOp.addMul ⟨6, by decide⟩ ⟨2, by decide⟩ 11,
  RowOp.addMul ⟨8, by decide⟩ ⟨2, by decide⟩ (-2),
  RowOp.swap ⟨3, by decide⟩ ⟨4, by decide⟩,
  RowOp.addMul ⟨5, by decide⟩ ⟨3, by decide⟩ (-1),
  RowOp.addMul ⟨6, by decide⟩ ⟨3, by decide⟩ (-3),
  RowOp.swap ⟨4, by decide⟩ ⟨7, by decide⟩,
  RowOp.addMul ⟨5, by decide⟩ ⟨4, by decide⟩ 2,
  RowOp.addMul ⟨6, by decide⟩ ⟨4, by decide⟩ 8,
  RowOp.addMul ⟨7, by decide⟩ ⟨4, by decide⟩ 3,
  RowOp.addMul ⟨8, by decide⟩ ⟨4, by decide⟩ 2,
  RowOp.swap ⟨5, by decide⟩ ⟨8, by decide⟩,
  RowOp.addMul ⟨7, by decide⟩ ⟨5, by decide⟩ (-1),
  RowOp.addMul ⟨8, by decide⟩ ⟨5, by decide⟩ 2,
  RowOp.swap ⟨5, by decide⟩ ⟨7, by decide⟩,
  RowOp.addMul ⟨7, by decide⟩ ⟨5, by decide⟩ (-2),
  RowOp.addMul ⟨8, by decide⟩ ⟨5, by decide⟩ (-1),
  RowOp.addMul ⟨7, by decide⟩ ⟨6, by decide⟩ (-1),
  RowOp.addMul ⟨8, by decide⟩ ⟨7, by decide⟩ 1
]

def rows_p_22 : List (List Int) := [
  [1, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 1, 0, 0, 0, 0, 0, 0],
  [1, 2, 1, 2, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 1, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 2, 0, 0, 0],
  [1, 1, 0, 0, 1, 2, 1, 0, 0],
  [1, 0, 1, 0, 2, 0, 0, 2, 0],
  [1, 2, 1, 2, 2, 4, 4, 2, 4]
]

abbrev M_e_22 : Mat 9 := matOfRows 9 rows_e_22
abbrev M_h_22 : Mat 9 := matOfRows 9 rows_h_22
abbrev M_p_22 : Mat 9 := matOfRows 9 rows_p_22

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
theorem basis_e_22 :
    IsBasisTransition 4 2 (fun j => parts_22.getD j.val [])
      (fun i => ePoly 4 2 [2, 2] (parts_22.getD i.val [])) M_e_22 :=
  checkBasisTransitionBool_sound 9 4 2 parts_22 (ePoly 4 2 [2, 2]) rows_e_22 rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem basis_h_22 :
    IsBasisTransition 4 2 (fun j => parts_22.getD j.val [])
      (fun i => hPoly 4 2 [2, 2] (parts_22.getD i.val [])) M_h_22 :=
  checkBasisTransitionBool_sound 9 4 2 parts_22 (hPoly 4 2 [2, 2]) rows_h_22 rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
theorem basis_p_22 :
    IsBasisTransition 4 2 (fun j => parts_22.getD j.val [])
      (fun i => pPoly 4 2 [2, 2] (parts_22.getD i.val [])) M_p_22 :=
  checkBasisTransitionBool_sound 9 4 2 parts_22 (pPoly 4 2 [2, 2]) rows_p_22 rfl

theorem det_M_e_22 : det M_e_22 = 3 :=
  det_matOfRows_via_ops 9 rows_e_22 ops_e_22 3 (by decide)

theorem det_M_h_22 : det M_h_22 = 3 :=
  det_matOfRows_via_ops 9 rows_h_22 ops_h_22 3 (by decide)

theorem det_M_p_22 : det M_p_22 = 32 :=
  det_matOfRows_lowerTri 9 rows_p_22 32 (by decide)

theorem not_pow2_M_e_22 : ¬IsPowerOfTwoUpToSign (det M_e_22) := by
  rw [det_M_e_22]
  exact not_isPowerOfTwoUpToSign_of_dvd_three ⟨1, rfl⟩

theorem not_pow2_M_h_22 : ¬IsPowerOfTwoUpToSign (det M_h_22) := by
  rw [det_M_h_22]
  exact not_isPowerOfTwoUpToSign_of_dvd_three ⟨1, rfl⟩

theorem not_permTri_M_e_22 : ¬IsPermTriangular M_e_22 :=
  not_permTriangular_via_singleton_row 9 (by decide) rows_e_22 ⟨0, by decide⟩ ⟨8, by decide⟩
    (by decide)

theorem not_permTri_M_h_22 : ¬IsPermTriangular M_h_22 :=
  not_permTriangular_via_two_nonzeros 9 (by decide) rows_h_22 (by decide)

/-! ### 5. Multidegree `d = (3, 1)` (`r = 2`, `N = 7`) -/

def parts_31 : List VecPart :=
  [[[3, 1]],
   [[3, 0], [0, 1]],
   [[2, 1], [1, 0]],
   [[2, 0], [1, 1]],
   [[2, 0], [1, 0], [0, 1]],
   [[1, 1], [1, 0], [1, 0]],
   [[1, 0], [1, 0], [1, 0], [0, 1]]]

def rows_p_31 : List (List Int) := [
  [1, 0, 0, 0, 0, 0, 0],
  [1, 1, 0, 0, 0, 0, 0],
  [1, 0, 1, 0, 0, 0, 0],
  [1, 0, 0, 1, 0, 0, 0],
  [1, 1, 1, 1, 1, 0, 0],
  [1, 0, 2, 1, 0, 2, 0],
  [1, 1, 3, 3, 3, 6, 6]
]

abbrev M_p_31 : Mat 7 := matOfRows 7 rows_p_31

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
theorem basis_p_31 :
    IsBasisTransition 4 2 (fun j => parts_31.getD j.val [])
      (fun i => pPoly 4 2 [3, 1] (parts_31.getD i.val [])) M_p_31 :=
  checkBasisTransitionBool_sound 7 4 2 parts_31 (pPoly 4 2 [3, 1]) rows_p_31 rfl

theorem lowerTri_M_p_31 : IsLowerTri M_p_31 :=
  checkLowerTriBool_sound 7 rows_p_31 (by decide)

theorem det_M_p_31 : det M_p_31 = 12 :=
  det_matOfRows_lowerTri 7 rows_p_31 12 (by decide)

theorem not_pow2_M_p_31 : ¬IsPowerOfTwoUpToSign (det M_p_31) := by
  rw [det_M_p_31]
  exact not_isPowerOfTwoUpToSign_of_dvd_three ⟨4, rfl⟩

/-! ### 6. Multilinear Degree `d = (1, 1, 1, 1)` (`r = 4`, `N = 15`) -/

def parts_1111 : List VecPart :=
  [[[1, 1, 1, 1]],
   [[1, 1, 1, 0], [0, 0, 0, 1]],
   [[1, 1, 0, 1], [0, 0, 1, 0]],
   [[1, 1, 0, 0], [0, 0, 1, 1]],
   [[1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
   [[1, 0, 1, 1], [0, 1, 0, 0]],
   [[1, 0, 1, 0], [0, 1, 0, 1]],
   [[1, 0, 1, 0], [0, 1, 0, 0], [0, 0, 0, 1]],
   [[1, 0, 0, 1], [0, 1, 1, 0]],
   [[1, 0, 0, 1], [0, 1, 0, 0], [0, 0, 1, 0]],
   [[1, 0, 0, 0], [0, 1, 1, 1]],
   [[1, 0, 0, 0], [0, 1, 1, 0], [0, 0, 0, 1]],
   [[1, 0, 0, 0], [0, 1, 0, 1], [0, 0, 1, 0]],
   [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 1]],
   [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]]

def rows_e_1111 : List (List Int) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1],
  [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1],
  [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1],
  [0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1],
  [0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1],
  [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1],
  [0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1],
  [0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1],
  [0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1],
  [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1],
  [0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]

def ops_e_1111 : List (RowOp 15) := [
  RowOp.swap ⟨0, by decide⟩ ⟨14, by decide⟩,
  RowOp.swap ⟨1, by decide⟩ ⟨9, by decide⟩,
  RowOp.addMul ⟨12, by decide⟩ ⟨1, by decide⟩ (-1),
  RowOp.addMul ⟨13, by decide⟩ ⟨1, by decide⟩ (-1),
  RowOp.swap ⟨2, by decide⟩ ⟨7, by decide⟩,
  RowOp.addMul ⟨11, by decide⟩ ⟨2, by decide⟩ (-1),
  RowOp.addMul ⟨13, by decide⟩ ⟨2, by decide⟩ (-1),
  RowOp.swap ⟨3, by decide⟩ ⟨6, by decide⟩,
  RowOp.addMul ⟨8, by decide⟩ ⟨3, by decide⟩ (-1),
  RowOp.addMul ⟨13, by decide⟩ ⟨3, by decide⟩ 2,
  RowOp.swap ⟨4, by decide⟩ ⟨5, by decide⟩,
  RowOp.addMul ⟨10, by decide⟩ ⟨4, by decide⟩ (-1),
  RowOp.addMul ⟨13, by decide⟩ ⟨4, by decide⟩ (-1),
  RowOp.addMul ⟨11, by decide⟩ ⟨5, by decide⟩ (-1),
  RowOp.addMul ⟨12, by decide⟩ ⟨5, by decide⟩ (-1),
  RowOp.addMul ⟨8, by decide⟩ ⟨6, by decide⟩ (-1),
  RowOp.addMul ⟨12, by decide⟩ ⟨6, by decide⟩ 2,
  RowOp.addMul ⟨10, by decide⟩ ⟨7, by decide⟩ (-1),
  RowOp.addMul ⟨12, by decide⟩ ⟨7, by decide⟩ (-1),
  RowOp.addMul ⟨11, by decide⟩ ⟨8, by decide⟩ (-1),
  RowOp.addMul ⟨12, by decide⟩ ⟨8, by decide⟩ 1,
  RowOp.addMul ⟨13, by decide⟩ ⟨8, by decide⟩ 1,
  RowOp.addMul ⟨10, by decide⟩ ⟨9, by decide⟩ (-1),
  RowOp.addMul ⟨11, by decide⟩ ⟨9, by decide⟩ (-1),
  RowOp.swap ⟨10, by decide⟩ ⟨11, by decide⟩,
  RowOp.addMul ⟨12, by decide⟩ ⟨10, by decide⟩ (-1),
  RowOp.addMul ⟨13, by decide⟩ ⟨10, by decide⟩ (-1),
  RowOp.addMul ⟨12, by decide⟩ ⟨11, by decide⟩ (-1),
  RowOp.addMul ⟨13, by decide⟩ ⟨11, by decide⟩ (-1),
  RowOp.swap ⟨12, by decide⟩ ⟨13, by decide⟩,
  RowOp.addMul ⟨13, by decide⟩ ⟨12, by decide⟩ (-2)
]

def rows_h_1111 : List (List Int) := [
  [24, 6, 6, 4, 2, 6, 4, 2, 4, 2, 6, 2, 2, 2, 1],
  [6, 6, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1],
  [6, 2, 6, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1],
  [4, 2, 2, 4, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1],
  [2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [6, 2, 2, 2, 1, 6, 2, 2, 2, 2, 2, 1, 1, 2, 1],
  [4, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 1],
  [2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1],
  [4, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1],
  [2, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1],
  [6, 2, 2, 2, 1, 2, 2, 1, 2, 1, 6, 2, 2, 2, 1],
  [2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1],
  [2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1],
  [2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]

def ops_h_1111 : List (RowOp 15) := [
  RowOp.swap ⟨0, by decide⟩ ⟨14, by decide⟩,
  RowOp.addMul ⟨1, by decide⟩ ⟨0, by decide⟩ (-6),
  RowOp.addMul ⟨2, by decide⟩ ⟨0, by decide⟩ (-6),
  RowOp.addMul ⟨3, by decide⟩ ⟨0, by decide⟩ (-4),
  RowOp.addMul ⟨4, by decide⟩ ⟨0, by decide⟩ (-2),
  RowOp.addMul ⟨5, by decide⟩ ⟨0, by decide⟩ (-6),
  RowOp.addMul ⟨6, by decide⟩ ⟨0, by decide⟩ (-4),
  RowOp.addMul ⟨7, by decide⟩ ⟨0, by decide⟩ (-2),
  RowOp.addMul ⟨8, by decide⟩ ⟨0, by decide⟩ (-4),
  RowOp.addMul ⟨9, by decide⟩ ⟨0, by decide⟩ (-2),
  RowOp.addMul ⟨10, by decide⟩ ⟨0, by decide⟩ (-6),
  RowOp.addMul ⟨11, by decide⟩ ⟨0, by decide⟩ (-2),
  RowOp.addMul ⟨12, by decide⟩ ⟨0, by decide⟩ (-2),
  RowOp.addMul ⟨13, by decide⟩ ⟨0, by decide⟩ (-2),
  RowOp.addMul ⟨14, by decide⟩ ⟨0, by decide⟩ (-24),
  RowOp.swap ⟨1, by decide⟩ ⟨9, by decide⟩,
  RowOp.addMul ⟨2, by decide⟩ ⟨1, by decide⟩ (-4),
  RowOp.addMul ⟨3, by decide⟩ ⟨1, by decide⟩ (-2),
  RowOp.addMul ⟨5, by decide⟩ ⟨1, by decide⟩ (-4),
  RowOp.addMul ⟨6, by decide⟩ ⟨1, by decide⟩ (-2),
  RowOp.addMul ⟨8, by decide⟩ ⟨1, by decide⟩ (-2),
  RowOp.addMul ⟨10, by decide⟩ ⟨1, by decide⟩ (-4),
  RowOp.addMul ⟨12, by decide⟩ ⟨1, by decide⟩ (-1),
  RowOp.addMul ⟨13, by decide⟩ ⟨1, by decide⟩ (-1),
  RowOp.addMul ⟨14, by decide⟩ ⟨1, by decide⟩ (-18),
  RowOp.swap ⟨2, by decide⟩ ⟨7, by decide⟩,
  RowOp.addMul ⟨3, by decide⟩ ⟨2, by decide⟩ (-2),
  RowOp.addMul ⟨5, by decide⟩ ⟨2, by decide⟩ (-4),
  RowOp.addMul ⟨6, by decide⟩ ⟨2, by decide⟩ (-2),
  RowOp.addMul ⟨8, by decide⟩ ⟨2, by decide⟩ (-2),
  RowOp.addMul ⟨9, by decide⟩ ⟨2, by decide⟩ (-4),
  RowOp.addMul ⟨10, by decide⟩ ⟨2, by decide⟩ (-4),
  RowOp.addMul ⟨11, by decide⟩ ⟨2, by decide⟩ (-1),
  RowOp.addMul ⟨13, by decide⟩ ⟨2, by decide⟩ (-1),
  RowOp.addMul ⟨14, by decide⟩ ⟨2, by decide⟩ (-18),
  RowOp.swap ⟨3, by decide⟩ ⟨6, by decide⟩,
  RowOp.addMul ⟨5, by decide⟩ ⟨3, by decide⟩ (-4),
  RowOp.addMul ⟨6, by decide⟩ ⟨3, by decide⟩ (-4),
  RowOp.addMul ⟨8, by decide⟩ ⟨3, by decide⟩ (-1),
  RowOp.addMul ⟨10, by decide⟩ ⟨3, by decide⟩ (-4),
  RowOp.addMul ⟨13, by decide⟩ ⟨3, by decide⟩ (-2),
  RowOp.addMul ⟨14, by decide⟩ ⟨3, by decide⟩ (-16),
  RowOp.swap ⟨4, by decide⟩ ⟨5, by decide⟩,
  RowOp.addMul ⟨6, by decide⟩ ⟨4, by decide⟩ (-2),
  RowOp.addMul ⟨10, by decide⟩ ⟨4, by decide⟩ (-1),
  RowOp.addMul ⟨13, by decide⟩ ⟨4, by decide⟩ (-1),
  RowOp.addMul ⟨14, by decide⟩ ⟨4, by decide⟩ (-2),
  RowOp.addMul ⟨6, by decide⟩ ⟨5, by decide⟩ (-10),
  RowOp.addMul ⟨7, by decide⟩ ⟨5, by decide⟩ (-4),
  RowOp.addMul ⟨9, by decide⟩ ⟨5, by decide⟩ (-4),
  RowOp.addMul ⟨10, by decide⟩ ⟨5, by decide⟩ (-4),
  RowOp.addMul ⟨11, by decide⟩ ⟨5, by decide⟩ (-1),
  RowOp.addMul ⟨12, by decide⟩ ⟨5, by decide⟩ (-1),
  RowOp.addMul ⟨13, by decide⟩ ⟨5, by decide⟩ (-4),
  RowOp.addMul ⟨14, by decide⟩ ⟨5, by decide⟩ (-2),
  RowOp.swap ⟨6, by decide⟩ ⟨12, by decide⟩,
  RowOp.addMul ⟨7, by decide⟩ ⟨6, by decide⟩ (-2),
  RowOp.addMul ⟨8, by decide⟩ ⟨6, by decide⟩ 2,
  RowOp.addMul ⟨10, by decide⟩ ⟨6, by decide⟩ (-2),
  RowOp.addMul ⟨12, by decide⟩ ⟨6, by decide⟩ (-8),
  RowOp.addMul ⟨13, by decide⟩ ⟨6, by decide⟩ (-4),
  RowOp.addMul ⟨14, by decide⟩ ⟨6, by decide⟩ 8,
  RowOp.swap ⟨6, by decide⟩ ⟨8, by decide⟩,
  RowOp.addMul ⟨8, by decide⟩ ⟨6, by decide⟩ (-2),
  RowOp.addMul ⟨12, by decide⟩ ⟨6, by decide⟩ (-1),
  RowOp.addMul ⟨8, by decide⟩ ⟨7, by decide⟩ 1,
  RowOp.addMul ⟨10, by decide⟩ ⟨7, by decide⟩ (-1),
  RowOp.addMul ⟨14, by decide⟩ ⟨7, by decide⟩ (-6),
  RowOp.swap ⟨8, by decide⟩ ⟨11, by decide⟩,
  RowOp.addMul ⟨9, by decide⟩ ⟨8, by decide⟩ (-2),
  RowOp.addMul ⟨10, by decide⟩ ⟨8, by decide⟩ (-2),
  RowOp.addMul ⟨11, by decide⟩ ⟨8, by decide⟩ 3,
  RowOp.addMul ⟨12, by decide⟩ ⟨8, by decide⟩ (-1),
  RowOp.addMul ⟨13, by decide⟩ ⟨8, by decide⟩ (-1),
  RowOp.addMul ⟨14, by decide⟩ ⟨8, by decide⟩ (-4),
  RowOp.addMul ⟨10, by decide⟩ ⟨9, by decide⟩ (-1),
  RowOp.addMul ⟨11, by decide⟩ ⟨9, by decide⟩ (-1),
  RowOp.addMul ⟨12, by decide⟩ ⟨9, by decide⟩ (-3),
  RowOp.addMul ⟨13, by decide⟩ ⟨9, by decide⟩ (-1),
  RowOp.addMul ⟨14, by decide⟩ ⟨9, by decide⟩ (-2),
  RowOp.swap ⟨10, by decide⟩ ⟨13, by decide⟩,
  RowOp.addMul ⟨12, by decide⟩ ⟨10, by decide⟩ (-2),
  RowOp.addMul ⟨14, by decide⟩ ⟨10, by decide⟩ 1,
  RowOp.swap ⟨10, by decide⟩ ⟨12, by decide⟩,
  RowOp.addMul ⟨12, by decide⟩ ⟨10, by decide⟩ (-2),
  RowOp.addMul ⟨12, by decide⟩ ⟨11, by decide⟩ 1,
  RowOp.addMul ⟨13, by decide⟩ ⟨11, by decide⟩ 1,
  RowOp.addMul ⟨14, by decide⟩ ⟨11, by decide⟩ 3,
  RowOp.addMul ⟨13, by decide⟩ ⟨12, by decide⟩ (-2),
  RowOp.addMul ⟨14, by decide⟩ ⟨12, by decide⟩ (-3),
  RowOp.addMul ⟨14, by decide⟩ ⟨13, by decide⟩ (-2)
]

abbrev M_e_1111 : Mat 15 := matOfRows 15 rows_e_1111
abbrev M_h_1111 : Mat 15 := matOfRows 15 rows_h_1111

theorem multilinear_formula_e_1111 :
    ∀ i j : Fin 15,
      M_e_1111 i j = multilinearElemEntry (parts_1111.getD i.val []) (parts_1111.getD j.val []) := by
  decide

theorem det_M_e_1111 : det M_e_1111 = -96 :=
  det_matOfRows_via_ops 15 rows_e_1111 ops_e_1111 (-96) (by decide)

theorem det_M_h_1111 : det M_h_1111 = 96 :=
  det_matOfRows_via_ops 15 rows_h_1111 ops_h_1111 96 (by decide)

theorem not_pow2_M_e_1111 : ¬IsPowerOfTwoUpToSign (det M_e_1111) := by
  rw [det_M_e_1111]
  exact not_isPowerOfTwoUpToSign_of_dvd_three ⟨-32, rfl⟩

theorem not_pow2_M_h_1111 : ¬IsPowerOfTwoUpToSign (det M_h_1111) := by
  rw [det_M_h_1111]
  exact not_isPowerOfTwoUpToSign_of_dvd_three ⟨32, rfl⟩

theorem not_permTri_M_e_1111 : ¬IsPermTriangular M_e_1111 :=
  not_permTriangular_via_singleton_row 15 (by decide) rows_e_1111 ⟨0, by decide⟩ ⟨14, by decide⟩
    (by decide)

theorem not_permTri_M_h_1111 : ¬IsPermTriangular M_h_1111 :=
  not_permTriangular_via_two_nonzeros 15 (by decide) rows_h_1111 (by decide)

end Conjecture00000000441
