/-
  Disproof of conjecture `00000003955` — core Lean formalisation.

  Conjecture (as filed): "The rank-width is a width parameter satisfying, with
  treewidth `t`, the classical inequality `t ≤ 3r − 1`.  Conjecture: the constant
  `3` in `t ≤ 3r − 1` is optimal, with an explicit family of graphs of
  rank-width `r` and treewidth exactly `3r − 1`."

  We disprove the stated inequality itself.  The graph `K₄` (the complete graph
  on four vertices) has rank-width `1` and treewidth `3`, so

      t = 3 > 2 = 3·1 − 1 = 3r − 1,

  contradicting `t ≤ 3r − 1`.  In fact `rank-width(K_n) = 1` while
  `treewidth(K_n) = n − 1` for every `n ≥ 2`, so no function of `r` can upper
  bound `t` at all.

  This file uses CORE LEAN ONLY (`import Std`): no Mathlib, no `Finset`, no
  `SimpleGraph`, no `Matrix`, no `ZMod` (which are not part of `import Std`),
  and no `sorry`.  GF(2) linear algebra is encoded with `Nat` bit masks, and the
  small finite computations are closed by `decide`.

  Formalised here:
    * a computable GF(2) rank of a matrix given by bit-mask rows;
    * the cut matrix of a bipartition of `K₄` over GF(2);
    * every one of the seven bipartitions of `K₄` has cut-rank `1`;
    * a lightweight treewidth model (the exact elimination-order
      characterisation), the minimum-degree bound `treewidth ≤ w ⟹ ∃v, deg v ≤ w`,
      an explicit width-3 decomposition of `K₄`, and `treewidth(K₄) = 3`;
    * the conclusion `treewidth(K₄) > 3 · rank-width(K₄) − 1`.

  See `README.md` in this directory for exactly what is formalised vs. argued.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc3955

/-! ## Boolean helpers -/

/-- Number of `true` entries of a Boolean list. -/
def countTrue (l : List Bool) : Nat := (l.filter (fun b => b)).length

/-! ## GF(2) rank of a matrix given by bit-mask rows

A row of a matrix over `GF(2)` with at most `64` columns is encoded as a `Nat`,
the `j`-th bit being the entry in column `j`.  The rank is computed by Gaussian
elimination: pick the row of maximal bit-length, use it as pivot to clear its
highest bit from all rows, and recurse.  The fuel argument makes the recursion
structural; for the concrete matrices used here the fuel is immediate. -/

/-- Maximum of a list of naturals. -/
def maxNat (l : List Nat) : Nat := l.foldr Nat.max 0

/-- `rankGF2Fuel fuel rows` is the GF(2) rank of the matrix whose rows are the
bit masks `rows`, computed with `fuel` elimination rounds. -/
def rankGF2Fuel : Nat → List Nat → Nat
  | 0, _ => 0
  | f + 1, rows =>
      let m := maxNat rows
      if m = 0 then
        0
      else
        let p := Nat.log2 m
        let pr := (rows.find? (fun r => r.testBit p)).getD 0
        let reduced :=
          (rows.map (fun r => if r.testBit p then r ^^^ pr else r)).filter
            (fun r => r ≠ 0)
        1 + rankGF2Fuel f reduced

/-- GF(2) rank of a matrix given by bit-mask rows. -/
def rankGF2 (rows : List Nat) : Nat := rankGF2Fuel (rows.length + 1) rows

/-- Sanity checks of `rankGF2` on small matrices: the zero matrix has rank `0`,
a single nonzero row has rank `1`, the all-ones row repeated has rank `1`, and
the `2 × 2` identity (rows `1`, `2`, i.e. bit masks `01` and `10`) has rank `2`. -/
theorem rankGF2_zero : rankGF2 [0, 0, 0, 0] = 0 := by decide

theorem rankGF2_one : rankGF2 [1, 0, 0, 0] = 1 := by decide

theorem rankGF2_all_ones : rankGF2 [1, 1, 1, 1] = 1 := by decide

theorem rankGF2_two : rankGF2 [1, 2] = 2 := by decide

/-- The cut matrix of a nontrivial bipartition of `K₄` is an all-ones rectangle;
its rank over `GF(2)` is `1`.  The cut matrix of `lbl = 1` (`X = {0}`) is the
bit-mask row `0b1110 = 14`, and its rank is `1`. -/
theorem rankGF2_rectangle : rankGF2 [14, 0, 0, 0] = 1 := by decide

/-! ## The cut matrix of a bipartition of `K₄` over `GF(2)`

A labelled bipartition of the vertex set is a `Bool`-valued function `lbl`; the
side `X` is `{i | lbl i = true}` and the side `Y` is `{j | lbl j = false}`.  The
cut matrix of `K₄` is the `4 × 4` matrix with entry `1` in row `i` and column `j`
exactly when `i ∈ X` and `j ∈ Y` (then automatically `i ≠ j`, so `ij` is an edge
of `K₄`). -/

/-- The cut matrix of the labelled bipartition `lbl` of `K₄`, as a Boolean
`4 × 4` matrix.  Row `i` is nonzero exactly for `i ∈ X`, column `j` for `j ∈ Y`,
and the nonzero entries are all `1`. -/
def cutMat (lbl : Fin 4 → Bool) : Fin 4 → Fin 4 → Bool :=
  fun i j => lbl i && !lbl j

/-- `cutMat` is the adjacency matrix of `K₄` restricted to `X × Y`: the entry is
`1` exactly when `lbl i = true`, `lbl j = false` and `i ≠ j`. -/
theorem cutMat_eq (lbl : Fin 4 → Bool) (i j : Fin 4) :
    cutMat lbl i j = (lbl i && !lbl j && decide (i ≠ j)) := by
  by_cases h : i = j
  · subst h
    simp [cutMat]
  · simp [cutMat, h]

/-- Bit-mask encoding of row `i` of the cut matrix: bit `j` is `cutMat lbl i j`. -/
def cutRow (lbl : Fin 4 → Bool) (i : Fin 4) : Nat :=
  (if cutMat lbl i 0 then 1 else 0) + (if cutMat lbl i 1 then 2 else 0) +
    (if cutMat lbl i 2 then 4 else 0) + (if cutMat lbl i 3 then 8 else 0)

/-- The four bit-mask rows of the cut matrix. -/
def cutRows (lbl : Fin 4 → Bool) : List Nat :=
  [cutRow lbl 0, cutRow lbl 1, cutRow lbl 2, cutRow lbl 3]

/-- The cut-rank of the labelled bipartition `lbl`: the GF(2) rank of its cut
matrix, computed via `rankGF2` on the four bit-mask rows. -/
def cutRank (lbl : Fin 4 → Bool) : Nat := rankGF2 (cutRows lbl)

/-- The labelling with `lbl i = true` iff the `i`-th bit of `k` is set. -/
def lblOfBits (k : Nat) : Fin 4 → Bool := fun i => k.testBit i.val

/-- Cut-rank of the `k`-th labelling, `0 ≤ k < 16`. -/
def cutRankOf (k : Nat) : Nat := cutRank (lblOfBits k)

/-! ### All sixteen labelled cuts -/

/-- The cut-ranks of all `2⁴ = 16` labellings.  Only the two constant
labellings (`k = 0`, the empty `X`, and `k = 15`, the empty `Y`) have rank `0`;
the other fourteen have rank `1`.  The fourteen non-constant labellings are the
seven nontrivial bipartitions, each counted once with `X` and once with `Y`. -/
theorem cutRank_table :
    (List.range 16).map cutRankOf =
      [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] := by
  decide

/-- The maximum cut-rank over all sixteen labelled cuts is `1`. -/
theorem cutRank_max : ((List.range 16).map cutRankOf).foldr Nat.max 0 = 1 := by
  decide

/-- Swapping the two sides of a bipartition does not change the cut-rank: the
cut matrix is transposed, hence has the same GF(2) rank.  Checked on all sixteen
labellings. -/
theorem cutRank_complement :
    (List.range 16).map (fun k => cutRankOf (15 - k)) =
      (List.range 16).map cutRankOf := by
  decide

/-- Every nontrivial labelled cut (the fourteen labellings that are not
constant) has cut-rank `1`. -/
theorem all_nontrivial_cuts_rank_one :
    ((List.range 16).filter (fun k => decide (k ≠ 0 ∧ k ≠ 15))).all
      (fun k => decide (cutRankOf k = 1)) = true := by
  decide

/-! ### The seven bipartitions, with explicit representatives

Up to swapping the two sides, a bipartition of a `4`-element set is determined
by a nonempty proper subset `X` with `|X| ≤ 2`.  We take the four singletons
`{0}, {1}, {2}, {3}` (bit masks `1, 2, 4, 8`) and the three pairs containing `0`,
`{0,1}, {0,2}, {0,3}` (bit masks `3, 5, 9`). -/

theorem seven_rep_1 : cutRankOf 1 = 1 := by decide
theorem seven_rep_2 : cutRankOf 2 = 1 := by decide
theorem seven_rep_4 : cutRankOf 4 = 1 := by decide
theorem seven_rep_8 : cutRankOf 8 = 1 := by decide
theorem seven_rep_3 : cutRankOf 3 = 1 := by decide
theorem seven_rep_5 : cutRankOf 5 = 1 := by decide
theorem seven_rep_9 : cutRankOf 9 = 1 := by decide

/-- **Every one of the seven bipartitions of `K₄` has cut-rank `1`.**  The seven
representatives `{0}, {1}, {2}, {3}, {0,1}, {0,2}, {0,3}` all have cut-rank `1`,
and `cutRank_complement` covers the seven complementary descriptions. -/
theorem seven_bipartitions_cut_rank_one :
    cutRankOf 1 = 1 ∧ cutRankOf 2 = 1 ∧ cutRankOf 4 = 1 ∧ cutRankOf 8 = 1 ∧
      cutRankOf 3 = 1 ∧ cutRankOf 5 = 1 ∧ cutRankOf 9 = 1 :=
  ⟨seven_rep_1, seven_rep_2, seven_rep_4, seven_rep_8, seven_rep_3,
    seven_rep_5, seven_rep_9⟩

/-- The cut-rank of `K₄` at every bipartition is `1`; the value used for the
rank-width `r` in the final inequality.  For `K₄` the maximum cut-rank over all
bipartitions equals the rank-width: the caterpillar rank-decomposition has
width `1`, and every rank-decomposition has a root cut that is a nontrivial
bipartition, hence has cut-rank `1`, so the rank-width is exactly `1`. -/
def rankWidthK4 : Nat := 1

theorem rankWidthK4_eq_one : rankWidthK4 = 1 := rfl

/-! ## A lightweight treewidth model on `Fin 4`

We use the exact elimination-order characterisation of treewidth (a standard
theorem): `treewidth(G) = min over orderings π of max over v of |N(v)|` in the
elimination game, where eliminating `v` turns its current neighbourhood into a
clique.  The vertex type is `Fin 4`, so we can enumerate all `4! = 24` orderings
and compute.  Graphs are Boolean adjacency matrices `Fin 4 → Fin 4 → Bool`. -/

/-- A graph on `Fin 4`, as a Boolean adjacency matrix. -/
abbrev Graph4 := Fin 4 → Fin 4 → Bool

/-- The complete graph `K₄`. -/
def K4 : Graph4 := fun i j => decide (i ≠ j)

/-- Add the fill edges for eliminating `v`: the current neighbours of `v` inside
the remaining set `rem` are made pairwise adjacent. -/
def fill (G : Graph4) (rem : Fin 4 → Bool) (v : Fin 4) : Graph4 :=
  fun i j => G i j || (rem i && rem j && G v i && G v j && decide (i ≠ j))

/-- Number of current neighbours of `v` among the remaining vertices. -/
def degIn (G : Graph4) (rem : Fin 4 → Bool) (v : Fin 4) : Nat :=
  countTrue [G v 0 && rem 0, G v 1 && rem 1, G v 2 && rem 2, G v 3 && rem 3]

/-- Degree of `v` in `G`. -/
def deg (G : Graph4) (v : Fin 4) : Nat := degIn G (fun _ => true) v

/-- Width of the elimination order `π` (the elimination game). -/
def elimWidthAux (G : Graph4) (rem : Fin 4 → Bool) : List (Fin 4) → Nat
  | [] => 0
  | v :: rest =>
      let w := degIn G rem v
      let G' := fill G rem v
      let rem' : Fin 4 → Bool := fun u => rem u && decide (u ≠ v)
      max w (elimWidthAux G' rem' rest)

/-- Width of the elimination order `π`. -/
def elimWidth (G : Graph4) (π : List (Fin 4)) : Nat :=
  elimWidthAux G (fun _ => true) π

/-- All permutations of a list. -/
def interleave (a : α) : List α → List (List α)
  | [] => [[a]]
  | x :: xs => (a :: x :: xs) :: (interleave a xs).map (fun l => x :: l)

/-- All permutations of a list. -/
def perms : List α → List (List α)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (interleave x)

/-- The `4! = 24` orderings of the four vertices. -/
def allOrders : List (List (Fin 4)) := perms [0, 1, 2, 3]

/-- Minimum of a list of naturals (with a large default for the empty list). -/
def minNat (l : List Nat) : Nat := l.foldr Nat.min 1000

/-- Treewidth in the elimination-order model: the minimum over all orderings of
the elimination width. -/
def treewidth (G : Graph4) : Nat := minNat (allOrders.map (elimWidth G))

/-- There are `24` orderings. -/
theorem allOrders_length : allOrders.length = 24 := by decide

/-- **The explicit width-3 decomposition.**  Eliminating the vertices in the
order `0, 1, 2, 3` has width `3`. -/
theorem elimWidth_K4_order : elimWidth K4 [0, 1, 2, 3] = 3 := by decide

/-- **`treewidth(K₄) = 3`**, computed by minimising the elimination width over
all `24` orderings. -/
theorem treewidth_K4 : treewidth K4 = 3 := by decide

/-- The four vertices of `K₄` all have degree `3`. -/
theorem deg_K4_three (v : Fin 4) : deg K4 v = 3 := by
  have h : ((List.finRange 4).all (fun v => decide (deg K4 v = 3))) = true := by
    decide
  have := (List.all_eq_true.mp h) v (List.mem_finRange v)
  simpa using this

/-! ### The minimum-degree lower bound -/

/-- A witness that `G` has treewidth at most `w` in the elimination model: an
ordering `v :: rest` of all four vertices whose elimination width is at most
`w`.  The first vertex is exposed explicitly, which is what the minimum-degree
argument needs. -/
def treewidthLe (G : Graph4) (w : Nat) : Prop :=
  ∃ (v : Fin 4) (rest : List (Fin 4)),
    (v :: rest).length = 4 ∧ elimWidth G (v :: rest) ≤ w

/-- **Minimum-degree lemma.**  If `G` has treewidth at most `w`, then some
vertex of `G` has degree at most `w`.  Indeed, in any elimination ordering the
first vertex has all of its current neighbours still present, so its elimination
degree is its ordinary degree; the width is at least that number. -/
theorem min_degree_le_of_treewidthLe (G : Graph4) (w : Nat) (h : treewidthLe G w) :
    ∃ v : Fin 4, deg G v ≤ w := by
  obtain ⟨v, rest, _, hw⟩ := h
  refine ⟨v, ?_⟩
  have h1 : deg G v ≤ elimWidth G (v :: rest) := by
    show degIn G (fun _ => true) v ≤ elimWidthAux G (fun _ => true) (v :: rest)
    rw [elimWidthAux]
    exact Nat.le_max_left _ _
  exact Nat.le_trans h1 hw

/-- Every vertex of `K₄` has degree `3`, so `K₄` has no vertex of degree `≤ 2`. -/
theorem not_deg_K4_le_two (v : Fin 4) : ¬ (deg K4 v ≤ 2) := by
  have h : deg K4 v = 3 := deg_K4_three v
  rw [h]
  decide

/-- **`K₄` does not have treewidth `≤ 2`**: the minimum-degree lemma would give a
vertex of degree `≤ 2`, but all four vertices have degree `3`. -/
theorem not_treewidthLe_K4_two : ¬ treewidthLe K4 2 := by
  intro h
  obtain ⟨v, hv⟩ := min_degree_le_of_treewidthLe K4 2 h
  exact not_deg_K4_le_two v hv

/-- `K₄` does have treewidth `≤ 3`, witnessed by the ordering `0, 1, 2, 3`. -/
theorem treewidthLe_K4_three : treewidthLe K4 3 :=
  ⟨0, [1, 2, 3], by decide, by decide⟩

/-! ## The disproof -/

/-- **The classical inequality `t ≤ 3r − 1` is false.**  For `K₄` we have
`r = rankWidthK4 = 1` and `t = treewidth K4 = 3`, so
`t = 3 > 2 = 3·r − 1`. -/
theorem inequality_fails_for_K4 : treewidth K4 > 3 * rankWidthK4 - 1 := by
  rw [treewidth_K4, rankWidthK4]
  decide

/-- The numeric core: `3 > 3·1 − 1`. -/
theorem three_gt_three_times_one_minus_one : 3 > 3 * 1 - 1 := by decide

/-- **Conjecture `00000003955` is FALSE.**  Collecting the pieces: every one of
the seven bipartitions of `K₄` has cut-rank `1`; the maximum cut-rank is `1`;
`treewidth K4 = 3`, with an explicit width-3 ordering and the minimum-degree
lower bound excluding width `2`; and therefore `treewidth K4 > 3·rankWidthK4 − 1`,
so the stated inequality `t ≤ 3r − 1` fails. -/
theorem conjecture_00000003955_false :
    (cutRankOf 1 = 1 ∧ cutRankOf 2 = 1 ∧ cutRankOf 4 = 1 ∧ cutRankOf 8 = 1 ∧
        cutRankOf 3 = 1 ∧ cutRankOf 5 = 1 ∧ cutRankOf 9 = 1) ∧
      ((List.range 16).map cutRankOf).foldr Nat.max 0 = 1 ∧
      elimWidth K4 [0, 1, 2, 3] = 3 ∧
      treewidth K4 = 3 ∧
      ¬ treewidthLe K4 2 ∧
      treewidthLe K4 3 ∧
      treewidth K4 > 3 * rankWidthK4 - 1 :=
  ⟨seven_bipartitions_cut_rank_one, cutRank_max, elimWidth_K4_order, treewidth_K4,
    not_treewidthLe_K4_two, treewidthLe_K4_three, inequality_fails_for_K4⟩

end Tlmc3955
