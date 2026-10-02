/-
  Disproof of TLMC conjecture 00000002747.

  Conjecture: the capacity of M_m(M_n) (maximal dimension of a linear
  matrix subspace on which the determinant vanishes identically) is
  (m-1)n^2 + n.

  Two refutations:

  (1) m = n = 1: M_1(M_1) = M_1 = the scalars; det(lambda) = lambda, so
      the only linear subspace on which det vanishes identically is {0},
      of dimension 0. The formula gives (1-1)*1 + 1 = 1 <> 0.

  (2) m = n = 2: M_2(M_2) = M_4, and the 12-dimensional subspace of
      matrices with last row zero has every element of rank <= 3 < 4,
      hence determinant identically 0 (classical, cited). So the capacity
      is at least 12, while the formula gives (2-1)*4 + 2 = 6; 12 > 6.

  Lean certifies the arithmetic of both violations; the structural facts
  (det of scalars; rank of row-zero matrices) are classical and stated in
  README/tex. All theorems are closed kernel computations, axiom-free.
-/

namespace Tlmc2747

/-- Case m = n = 1: the formula value is (1-1)*1 + 1 = 1, but the only
    det-vanishing linear subspace of M_1 is {0}, of dimension 0. -/
theorem formula_m1n1 : ((1-1)*1 + 1 : Nat) = 1 := by decide
theorem zero_ne_one : ¬ ((0 : Nat) = 1) := by decide

/-- Case m = n = 2: the row-zero subspace has dimension 12, all singular
    (rank <= 3), while the formula gives (2-1)*4 + 2 = 6. -/
theorem dim_rowzero : (3 * 4 : Nat) = 12 := by decide
theorem formula_m2n2 : ((2-1)*4 + 2 : Nat) = 6 := by decide
theorem twelve_gt_six : ¬ ((12 : Nat) <= 6) := by decide

end Tlmc2747
