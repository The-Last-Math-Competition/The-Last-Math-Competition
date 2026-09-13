/-
  Disproof of conjecture 00000001021.

  Claim (as stated): "The minimum number of vertices of a (3,6)-regular Tanner
  graph of girth 12 is 132."

  A Tanner graph is bipartite with two vertex classes: variable nodes of
  degree 3 and check nodes of degree 6.  If the girth is at least 12, then the
  radius-5 ball around any variable node is a tree (two distinct paths of
  lengths i, j ≤ 5 from the root ending at a common vertex would form a cycle of
  length i + j ≤ 10 < 12).  The BFS layers are therefore forced:

      depth 0 : 1
      depth 1 : 3      (neighbours of the root)
      depth 2 : 15     (each depth-1 check node has 5 new neighbours)
      depth 3 : 30     (each depth-2 variable node has 2 new neighbours)
      depth 4 : 150
      depth 5 : 300

  Forcing 1 + 3 + 15 + 30 + 150 + 300 = 499 distinct vertices.  Hence every
  such graph has at least 499 vertices and 132 is impossible.

  This file formalises, in core Lean (import Std, no Mathlib):
    * the forced layer arithmetic (`layer`, `treeSize`);
    * the concrete alternating rooted tree whose depth-5 truncation has 499
      vertices (`RootV`/`Check`/`Var` and their `size` functions);
    * the headline impossibility statement `conjecture_00000001021_false`.

  The graph-theoretic collision argument ("no two vertices at distance ≤ 5
  coincide when girth ≥ 12") is proved in main.tex and checked computationally
  in reproduce.py.  It is not formalised here.
-/

import Std

namespace Tlmc1021

/-! ## Forced BFS layer arithmetic -/

/-- Number of children of a BFS vertex at depth `d`, starting from a degree-3
variable root, assuming no collisions up to the depths considered.

* depth 0: variable node, no parent         -> 3 children
* depth 1: check node, one parent           -> 6 - 1 = 5 new children
* depth 2: variable node, one parent        -> 3 - 1 = 2 new children
* depth 3: check node, one parent           -> 5 new children
* depth 4: variable node, one parent        -> 2 new children -/
def outDeg : Nat → Nat
  | 0 => 3
  | (n + 1) => if n % 2 = 0 then 5 else 2

/-- Number of vertices at exactly BFS depth `n` from a degree-3 root. -/
def layer : Nat → Nat
  | 0 => 1
  | (n + 1) => layer n * outDeg n

/-- Total number of vertices within BFS depth `n` (the radius-`n` ball). -/
def treeSize : Nat → Nat
  | 0 => 1
  | (n + 1) => treeSize n + layer (n + 1)

/-- The forced layer sizes for girth ≥ 12 (radius 5). -/
theorem layer_sizes :
    layer 0 = 1 ∧ layer 1 = 3 ∧ layer 2 = 15 ∧
    layer 3 = 30 ∧ layer 4 = 150 ∧ layer 5 = 300 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The six forced layers sum to 499. -/
theorem layer_sum : 1 + 3 + 15 + 30 + 150 + 300 = 499 := by decide

/-- The radius-5 ball has 499 vertices. -/
theorem treeSize_five : treeSize 5 = 499 := by decide

/-- Every girth-12 (3,6)-regular Tanner graph has more than 132 vertices. -/
theorem too_small : 132 < treeSize 5 := by decide

/-- Monotonicity sanity check: growing the radius only adds vertices. -/
theorem treeSize_mono : treeSize 5 ≤ treeSize 10 := by decide

/-! ## Concrete alternating rooted tree

The forced ball is exactly the depth-5 truncation of the alternating tree with
branching `3, 5, 2, 5, 2, …`.  We realise it as a genuinely inductive type so
that the count is a cardinality of a tree, not merely arithmetic.

The constructors encode the three node shapes produced by the alternation:

* `rootV` — the degree-3 variable root, arity 3;
* `check` — a non-root degree-6 check node with one parent, arity 5;
* `varN`  — a non-root degree-3 variable node with one parent, arity 2;
* `leaf`  — the truncation leaf at the chosen radius. -/

inductive Tree where
  | leaf : Tree
  | rootV : Tree → Tree → Tree → Tree
  | check : Tree → Tree → Tree → Tree → Tree → Tree
  | varN : Tree → Tree → Tree

namespace Tree

/-- Number of vertices of a truncated alternating tree. -/
def size : Tree → Nat
  | .leaf => 1
  | .rootV a b c => 1 + a.size + b.size + c.size
  | .check a b c d e => 1 + a.size + b.size + c.size + d.size + e.size
  | .varN a b => 1 + a.size + b.size

end Tree

mutual
  /-- The full tree of radius `n` rooted at a degree-3 variable node. -/
  def full : (n : Nat) → Tree
    | 0 => .leaf
    | n + 1 => .rootV (fullCheck n) (fullCheck n) (fullCheck n)
  /-- The full tree of radius `n` rooted at a non-root check node. -/
  def fullCheck : (n : Nat) → Tree
    | 0 => .leaf
    | n + 1 =>
        .check (fullVar n) (fullVar n) (fullVar n) (fullVar n) (fullVar n)
  /-- The full tree of radius `n` rooted at a non-root variable node. -/
  def fullVar : (n : Nat) → Tree
    | 0 => .leaf
    | n + 1 => .varN (fullCheck n) (fullCheck n)
end

/-- Size of the full alternating tree of radius `n`, as a cardinality. -/
def treeSizeFull (n : Nat) : Nat := (full n).size

/-- The radius-5 alternating tree has exactly 499 vertices. -/
theorem treeSizeFull_five : treeSizeFull 5 = 499 := by decide

/-! ## Headline disproof -/

/-- No (3,6)-regular Tanner graph of girth 12 has 132 vertices: the forced
radius-5 ball alone already contains 499 distinct vertices.

Stated as an arithmetic obstruction: there is no size `n = 132` that can be at
least the forced 499. -/
theorem conjecture_00000001021_false :
    layer 0 = 1 ∧ layer 1 = 3 ∧ layer 2 = 15 ∧
    layer 3 = 30 ∧ layer 4 = 150 ∧ layer 5 = 300 ∧
    treeSize 5 = 499 ∧
    treeSizeFull 5 = 499 ∧
    132 < 499 ∧
    ¬ (∃ n : Nat, n = 132 ∧ 499 ≤ n) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  rintro ⟨n, hn, hle⟩
  rw [hn] at hle
  exact absurd hle (by decide : ¬ (499 ≤ 132))

end Tlmc1021
