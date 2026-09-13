# Lean 4 formalisation — disproof of conjecture `00000003955`

Core Lean only (`import Std`), no Mathlib, no `sorry`.  The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
(`name = "tlmc3955"`) in `lakefile.toml`.

The conjecture states that rank-width `r` and treewidth `t` satisfy the
"classical inequality" `t ≤ 3r − 1`, and that `3` is optimal.  The inequality is
false: `K₄` has rank-width `1` and treewidth `3`, so `3 > 3·1 − 1 = 2`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.  The audit reports only
`propext` (and, for a few theorems that use `List.all_eq_true` /
`List.mem_finRange`, `Quot.sound`); no theorem depends on `sorryAx`.

## What is fully formalised

GF(2) linear algebra is encoded with `Nat` bit masks: a row of a matrix with at
most `64` columns is a `Nat`, bit `j` being column `j`.  `rankGF2` performs
Gaussian elimination (pick the row of maximal bit length, clear its highest bit
from all rows, recurse), with a fuel argument making the recursion structural.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `rankGF2_zero` | `rankGF2 [0,0,0,0] = 0` | sanity check: zero matrix has rank `0` |
| `rankGF2_one` | `rankGF2 [1,0,0,0] = 1` | a single nonzero row has rank `1` |
| `rankGF2_all_ones` | `rankGF2 [1,1,1,1] = 1` | all-ones row repeated has rank `1` |
| `rankGF2_two` | `rankGF2 [1,2] = 2` | the `2 × 2` identity has rank `2` |
| `rankGF2_rectangle` | `rankGF2 [14,0,0,0] = 1` | the cut of `X = {0}` has rank `1` |
| `cutMat_eq` | `cutMat lbl i j = (lbl i && !lbl j && decide (i ≠ j))` | the cut matrix is the `K₄` adjacency restricted to `X × Y` |
| `cutRank_table` | the 16 labelled cut-ranks are `0,1,…,1,0` | only the two constant labellings have rank `0` |
| `cutRank_max` | max over the 16 labelled cuts is `1` | rank-width upper value |
| `cutRank_complement` | complementing a labelling preserves cut-rank | swapping the two sides transposes the matrix |
| `all_nontrivial_cuts_rank_one` | all 14 nonconstant labellings have cut-rank `1` | every nontrivial bipartition |
| `seven_rep_1, …, seven_rep_9` | the seven representatives have cut-rank `1` | `{0},{1},{2},{3},{0,1},{0,2},{0,3}` |
| `seven_bipartitions_cut_rank_one` | the conjunction of the seven | **all seven bipartitions of `K₄` have cut-rank `1`** |
| `rankWidthK4_eq_one` | `rankWidthK4 = 1` | the value `r = 1` used below |
| `allOrders_length` | `allOrders.length = 24` | all `4!` elimination orders |
| `elimWidth_K4_order` | `elimWidth K4 [0,1,2,3] = 3` | **explicit width-3 decomposition** |
| `treewidth_K4` | `treewidth K4 = 3` | `min` over all 24 elimination orders |
| `deg_K4_three` | `deg K4 v = 3` for all `v : Fin 4` | every vertex has degree `3` |
| `min_degree_le_of_treewidthLe` | `treewidthLe G w → ∃ v, deg G v ≤ w` | **minimum-degree lemma** |
| `not_deg_K4_le_two` | `¬ (deg K4 v ≤ 2)` | no vertex has degree `≤ 2` |
| `not_treewidthLe_K4_two` | `¬ treewidthLe K4 2` | **`K₄` has treewidth `> 2`** |
| `treewidthLe_K4_three` | `treewidthLe K4 3` | `K₄` has treewidth `≤ 3` |
| `inequality_fails_for_K4` | `treewidth K4 > 3 * rankWidthK4 - 1` | **the inequality fails: `3 > 2`** |
| `conjecture_00000003955_false` | conjunction of the above | the collected disproof |

## Proof strategy

* The cut matrix of a labelled bipartition `lbl` of `K₄` is
  `cutMat lbl i j = lbl i && !lbl j`; because `lbl i = true` and `lbl j = false`
  force `i ≠ j`, this is exactly the `K₄` adjacency matrix restricted to
  `X × Y` (`cutMat_eq`).  Row `i` is encoded as the bit mask `cutRow`.  For
  `K₄` each such matrix is an all-ones `|X| × |Y|` rectangle, whose GF(2) rank
  is `1` when both sides are nonempty; `cutRank_table` verifies this for all
  `2⁴ = 16` labellings by `decide`.
* Seven representatives of the seven bipartitions (the four singletons and
  `{0,1}, {0,2}, {0,3}`, the pairs containing `0`) are checked individually,
  and `cutRank_complement` handles the complementary descriptions; the
  `List.all` statement `all_nontrivial_cuts_rank_one` covers all fourteen
  nonconstant labellings at once.
* Treewidth is modelled on the vertex type `Fin 4` by the exact elimination
  game: `fill` adds the fill edges, `degIn` counts the current neighbours,
  `elimWidthAux` runs the game, and `treewidth G` is the minimum of
  `elimWidth G π` over all `4! = 24` orderings `π` of `allOrders`.  The explicit
  ordering `[0,1,2,3]` gives width `3`, and `decide` evaluates the minimum to
  `3` (`treewidth_K4`).
* The **minimum-degree lemma** is proved for this model.  `treewidthLe G w`
  exposes an explicit ordering `v :: rest`; the first vertex `v` still has all
  its neighbours present when it is eliminated, so its elimination degree is
  its ordinary degree `deg G v`, and the width is at least that
  (`Nat.le_max_left`).  Hence `deg G v ≤ w`.  Since all four vertices of `K₄`
  have degree `3`, `treewidthLe K4 2` is impossible — giving the lower bound
  `treewidth(K₄) ≥ 3` — while `treewidthLe K4 3` exhibits the upper bound.
* The conclusion `treewidth K4 > 3 * rankWidthK4 - 1` reduces by
  `treewidth_K4` and `rankWidthK4 = 1` to `3 > 3·1 − 1`, closed by `decide`.

## Scope: what is argued in prose rather than formalised

The following are deliberately **not** formalised; they are stated and proved
in `main.tex` (and checked numerically in `reproduce.py`).

1. **Elimination width = treewidth.**  The lightweight model takes the exact
   elimination-order characterisation of treewidth as its *definition*.  The
   classical theorem identifying it with the minimum width over tree
   decompositions is not formalised here.  The minimum-degree lemma is proved
   for this model, where it is immediate; the standard tree-decomposition proof
   of the same lemma is the one given in `main.tex` (Lemma "minimum-degree
   bound").
2. **The rank-width value `r = 1`.**  What is formalised is that every
   bipartition of `K₄` has cut-rank `1` and that the maximum over all
   bipartitions is `1`.  The identification `rankWidthK4 := 1` uses the prose
   argument of `main.tex`: the caterpillar rank-decomposition has all cuts of
   rank `1` (so `rw(K₄) ≤ 1`), and any rank-decomposition has a root cut that is
   a nontrivial bipartition, of cut-rank `1` (so `rw(K₄) ≥ 1`).  The min over all
   rank-decompositions is not formalised.
3. **`K_n` for `n ≥ 5` and the no-function theorem.**  The statements
   `rw(K_n) = 1`, `tw(K_n) = n − 1` for all `n ≥ 2`, and hence that no function
   `f` satisfies `tw(G) ≤ f(rw(G))` for all `G`, are proved in `main.tex`
   (Theorem "No function bounds treewidth by rank-width") and verified
   numerically for `n ≤ 7` in `reproduce.py`.  The Lean file formalises only the
   `K₄` instance.
4. **The kernelization clause.**  The conjecture's final clause about
   distance-hereditary graph kernelization is not addressed; the refutation
   needs only the false inequality.

Nothing above uses `sorry`, and none of the formalised statements is
conditional on an unproved assumption.

## Environment

Lean 4.33.1, Lake 5.0.0, no Mathlib.  `lake build` needs no cache download.
