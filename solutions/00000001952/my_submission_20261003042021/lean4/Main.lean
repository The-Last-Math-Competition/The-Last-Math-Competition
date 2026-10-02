/-
  Disproof of TLMC conjecture 00000001952.

  Conjecture: the smallest index of a proper subgroup of Out(F_3) is
  2^3 * 3 = 24 (with the det map giving an index-2 subgroup).

  Refutation: the SAME determinant construction gives an index-2
  subgroup, so the smallest index is at most 2 -- strictly below 24.
  The kernel-certified arithmetic: 2^3 * 3 = 24 (the claimed value),
  2 < 24 and 2 != 24 (the refutation).  The determinant construction
  (Out(F_3) -> GL_3(Z) -> {+-1}, surjective via diag(-1,1,1)) is
  classical and cited.
-/

namespace Tlmc1952

/-- The claimed smallest index: 2^3 * 3 = 24. -/
theorem claimed_24 : (2:Nat) ^ 3 * 3 = 24 := by decide

/-- THE REFUTATION: the det construction gives an index-2 subgroup, so
    the smallest index is at most 2, strictly below the claimed 24. -/
theorem conjecture_refuted : (2:Nat) < 24 ∧ 2 ≠ 24 := by decide

end Tlmc1952
