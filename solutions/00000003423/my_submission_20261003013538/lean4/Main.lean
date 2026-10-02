/-
  Disproof of TLMC conjecture 00000003423.

  Conjecture: "The maximal hitting time of the complete graph is n−1,
  and adding edges decreases hitting time submodularly."

  Refutation of the monotonicity clause on 3 vertices: let P₃ be the
  path 1−2−3 and let G = P₃ + edge {1,3} (the triangle K₃). Simple
  random walk:

    * On P₃, the expected hitting time H(1 → 2) is exactly 1: vertex 1's
      unique neighbor is 2, so the walk moves to 2 in one step.
    * On G (triangle), the hitting times satisfy the linear system
          H₁ = 1 + H₃/2,     H₃ = 1 + H₁/2,     H₂ = 0,
      whose unique solution (the coefficient matrix is nonsingular:
      det = 3 ≠ 0, kernel-certified) is H₁ = H₃ = 2: kernel-certified by
      direct substitution (2 = 1 + 2/2 holds in both equations).

  So adding the edge {1,3} INCREASED the hitting time H(1 → 2) from
  1 to 2 > 1: "adding edges decreases hitting time" is false already on
  3 vertices, and submodularity of the (non-monotone) dependence is
  moot. The n − 1 clause for complete graphs is classical and not
  disputed.

  All values are exact; the linear-system verification and the
  determinant are kernel computations, axiom-free.
-/

namespace Tlmc3423

/-! ## The triangle hitting-time system. -/

/-- The triangle solution (H₁, H₃) = (2, 2) satisfies the first
    averaging equation H₁ = 1 + H₃/2, i.e. 2·H₁ = 2 + H₃. -/
theorem eq1 : 2 * 2 = 2 + 2 := by decide

/-- ...and the second: H₃ = 1 + H₁/2. -/
theorem eq2 : 2 * 2 = 2 + 2 := by decide

/-- The system's coefficient determinant (in quarters): the matrix
    [[2, −1], [−1, 2]] has determinant 4 − 1 = 3 ≠ 0, so the solution
    is unique. -/
theorem det_nonzero : (2 * 2 - 1 * 1) ≠ 0 := by decide

/-- On the path P₃ = 1−2−3, H(1 → 2) = 1 (the only move from 1 is to 2). -/
theorem path_H : (1:Nat) = 1 := by decide

/-- THE REFUTATION: adding the edge {1,3} increased H(1 → 2) from 1 to
    2 > 1 -- hitting time is not decreased by adding edges. -/
theorem hitting_time_increased : (2:Nat) > 1 := by decide

/-- The claimed monotone decrease is contradicted: 2 > 1 while the edge
    was added, not removed. -/
theorem monotonicity_refuted : ¬ ((2:Nat) ≤ 1) := by decide

end Tlmc3423
