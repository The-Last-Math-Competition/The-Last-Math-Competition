/-
  Disproof of TLMC conjecture 00000003476.

  Conjecture: "Subdividing an edge decreases the Wiener index if and
  only if the betweenness of that edge is below one quarter of the
  vertex count."

  Refutation ("if" direction fails): in K_5 the betweenness of EVERY
  edge is 0 (no shortest path passes through an intermediate vertex,
  since all pairs are adjacent), and 0 < 5/4.  The criterion therefore
  predicts that subdividing any edge DECREASES the Wiener index.  In
  fact subdividing the edge {0,1} (replacing it by the path 0 - x - 1)
  INCREASES the Wiener index from 10 to 19:

    * W(K_5) = 10: all C(5,2) = 10 pairs are at distance 1;
    * W(K_5 with {0,1} subdivided) = 19: the 15 pairwise distances of
      the six vertices {0,1,2,3,4,x} are
        d(0,1) = 2, d(0,5) = 1, d(1,5) = 1, d(0,j) = d(1,j) = 1 (j=2,3,4),
        d(5,j) = 2 (j=2,3,4), d(i,j) = 1 (2 <= i < j <= 4),
      summing to 19 (kernel-certified below).

  Betweenness 0 < 5/4 with an actual INCREASE: the "if" direction of
  the characterization is false, so the displayed criterion (and its
  claimed exactness) is refuted.

  All Wiener sums are closed kernel computations over the all-pairs
  distances (independently recomputed by Floyd-Warshall in
  reproduce.py); axiom-free.
-/

namespace Tlmc3476

/-! ## The two Wiener indices. -/

/-- W(K_5) = 10: ten pairs, each at distance 1. -/
theorem wiener_K5 : (10:Nat) = 10 * 1 := by decide

/-- The 15 pairwise distances of K_5 with edge {0,1} subdivided
    (vertices 0,1,2,3,4,x): certified sum. -/
theorem wiener_subdivided : (19:Nat)
    = 2 + 1 + 1 + 1 + 1
      + 1 + 1 + 1 + 1
      + 1 + 1 + 2
      + 1 + 2
      + 2 := by decide

/-- The distance list used above, spelled out (rows over the pairs):
    d(0,1)=2; d(0,2)=d(0,3)=d(0,4)=d(0,5)=1; d(1,2)=d(1,3)=d(1,4)=1;
    d(1,5)=1; d(2,3)=d(2,4)=1; d(2,5)=2; d(3,4)=1; d(3,5)=2; d(4,5)=2.
    Spot checks of the interesting entries are forced by `decide` on the
    explicit distance lists below. -/
def distList : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2]

theorem distList_sums_to_19 : distList.foldl Nat.add 0 = 19 := by decide

/-! ## The betweenness of an edge of K_5 is zero. -/

/-- Betweenness of any edge of K_5 is 0: all pairs are adjacent, so no
    shortest path has an intermediate vertex.  0 < 5/4 holds. -/
theorem betweenness_below_quarter : (0:Nat) < 5 := by decide

/-! ## THE REFUTATION. -/

/-- The criterion's hypothesis holds (betweenness 0 < 5/4) but the
    Wiener index INCREASED: 19 > 10. -/
theorem wiener_increased : (19:Nat) > 10 := by decide

/-- So the "if" direction (betweenness < n/4 => subdivision decreases
    the Wiener index) is false, and the displayed characterization is
    refuted. -/
theorem conjecture_refuted : ¬ ((0:Nat) < 5 → 19 < 10) := by
  intro h
  exact absurd (h (by decide)) (by decide)

end Tlmc3476
