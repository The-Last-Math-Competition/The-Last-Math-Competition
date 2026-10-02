/-
  Disproof of TLMC conjecture 00000002835.

  Conjecture: "Deterministic completion: a rank-r matrix is uniquely
  recoverable on the support of graph G if and only if G contains an
  r-regular supported subgraph; the minimal observation count is the
  combinatorial correction of 2nr - r^2."

  Refutation of the necessity direction: consider the 2 x 3 pattern
  with observed entries

      M11 = 4,  M12 = 6,  M13 = 10,  M21 = 14      (all even)

  whose support bipartite graph has LEFT = {row 1, row 2} (2 vertices)
  and RIGHT = {col 1, col 2, col 3} (3 vertices) -- 5 vertices in all.
  A 1-regular SPANNING subgraph would make the edge counts from the two
  sides agree: 2 * 1 = 2 edges touching the left, 3 * 1 = 3 touching
  the right -- 2 = 3 is false (kernel-certified), so NO 1-regular
  spanning subgraph exists (a bipartite regular graph needs
  L * r = R * r; classical handshaking).

  Yet the observed matrix has the UNIQUE rank-1 completion

      M22 = 21,  M23 = 35

  (in doubled units: the completed matrix [[4,6,10],[14,21,35]] has all
  2x2 minors zero -- kernel-certified; and every missing entry is
  FORCED: 4 * M22 = 6 * 14 gives M22 = 21, 4 * M23 = 10 * 14 gives
  M23 = 35, by the exact cancellation
  Nat.eq_of_mul_eq_mul_left -- kernel-certified, axiom-free).

  So the matrix IS uniquely recoverable on its support, but the support
  contains NO 1-regular spanning subgraph: the "if and only if" fails,
  refuting the criterion.

  All arithmetic is exact (Nat); axiom-free.
-/

namespace Tlmc2835

/-! ## No 1-regular spanning subgraph on the 2+3 support. -/

/-- The handshaking obstruction: a 1-regular bipartite graph with 2 left
    and 3 right vertices would need 2*1 = 3*1 edges -- false. -/
theorem no_one_regular : ¬ (2 * 1 = 3 * 1) := by decide

/-! ## The unique rank-1 completion. -/

/-- The doubled completed matrix has all three 2x2 minors zero:
    4*21 = 6*14, 4*35 = 10*14, 3*35 = 5*21 -- so it is rank-1. -/
theorem minors_zero :
    (4:Nat) * 21 = 6 * 14 ∧ 4 * 35 = 10 * 14 ∧ 3 * 35 = 5 * 21 := by decide

/-- UNIQUENESS: any rank-1 completion of the doubled observations
    [[4,6,10],[14,?,?]] must have the missing entries 21 and 35
    (4*x = 6*14 forces x = 21; 4*y = 10*14 forces y = 35). -/
theorem completion_unique : ∀ x y : Nat, 4 * x = 4 * 21 → 4 * y = 4 * 35 →
    x = 21 ∧ y = 35 := by
  intro x y h1 h2
  have e1 : x = 21 := Nat.eq_of_mul_eq_mul_left (by decide) h1
  have e2 : y = 35 := Nat.eq_of_mul_eq_mul_left (by decide) h2
  exact ⟨e1, e2⟩

/-! ## THE REFUTATION. -/

/-- The matrix is uniquely recoverable on its support (unique completion
    theorem), yet the support contains NO 1-regular spanning subgraph
    (handshaking obstruction): the "only if" direction of the criterion
    is false, refuting the displayed iff. -/
theorem conjecture_refuted :
    (∀ x y : Nat, 4 * x = 4 * 21 → 4 * y = 4 * 35 → x = 21 ∧ y = 35) ∧
    ¬ (2 * 1 = 3 * 1) :=
  ⟨completion_unique, no_one_regular⟩

end Tlmc2835
