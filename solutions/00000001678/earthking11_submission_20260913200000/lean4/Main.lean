/-
  Disproof of conjecture `00000001678`.

  Conjecture (as filed): the difference between the zero forcing number and the
  path cover number on trees takes values in `{0, 1}`, with an explicit tree
  classification; moreover the trees with difference one are *exactly* the
  odd-diameter trees admitting a perfect matching.

  This file formalises the counterexample that refutes the `exactly` clause:

      T = P_4, the path on four vertices.

  * `Z(P_4) = 1`  (the zero forcing number, a minimum over all colourings),
  * `P(P_4) = 1`  (the path cover number, a minimum over all path covers),
  * hence `Z - P = 0`,
  * while `diameter(P_4) = 3` is odd and `P_4` has a perfect matching.

  So `P_4` satisfies the right-hand classification predicate
  ("odd diameter and perfect matching") yet its difference is `0 != 1`; the
  claimed "exactly" characterisation is therefore false.

  The file uses CORE LEAN ONLY (`import Std`); it does not use Mathlib,
  `Finset`, `SimpleGraph`, `Matrix`, `norm_num`, `linarith`, `omega`, or
  `sorry`. Every numerical fact below is proved by `decide` on the computable
  definitions. Note that function types have no decidable equality in core
  Lean, so colourings and partitions are only ever compared pointwise
  (via `List` images) or through Boolean evaluators; no function equality is
  ever decided.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc1678

/-! ## The graph `P_4` -/

/-- The four vertices of `P_4`, in path order. -/
def V4 : List (Fin 4) := [0, 1, 2, 3]

/-- Adjacency in the path `P_4`: the edges are `i—(i+1)` for `i = 0, 1, 2`. -/
def adj (i j : Fin 4) : Bool :=
  decide (i.val + 1 = j.val ∨ j.val + 1 = i.val)

/-- `{v}` as a colouring (a `Fin 4 → Bool` predicate). -/
def single (v : Fin 4) : Fin 4 → Bool := fun w => decide (w = v)

/-- List monad bind, defined locally (`List.bind` is not exported by `import Std`). -/
def bindL {α β : Type} (l : List α) (f : α → List β) : List β :=
  l.foldr (fun a acc => f a ++ acc) []

/-! ## Zero forcing

The *colour-change rule*: if a black vertex `u` has exactly one white neighbour
`v`, then `v` is forced (turned black). A *zero forcing set* is an initial set of
black vertices whose repeated closure is all of `V`. The *zero forcing number*
`Z(G)` is the minimum size of a zero forcing set. -/

/-- `u` forces `v` under the colouring `c`: `u` is black, `v` is adjacent to
`u`, and every neighbour of `u` other than `v` is already black. -/
def forcedBy (c : Fin 4 → Bool) (u v : Fin 4) : Bool :=
  c u && adj u v &&
    V4.all (fun w => !(adj u w) || decide (w = v) || c w)

/-- One application of the colour-change rule. Black stays black; every vertex
that some black vertex forces becomes black. -/
def step (c : Fin 4 → Bool) : Fin 4 → Bool :=
  fun v => c v || V4.any (fun u => forcedBy c u v)

/-- Iterate the colour-change rule `k` times. -/
def iterate (c : Fin 4 → Bool) : Nat → Fin 4 → Bool
  | 0 => c
  | n + 1 => step (iterate c n)

/-- The colour-change closure. Four iterations suffice: each effective step
strictly increases the number of black vertices and there are only four. -/
def closure (c : Fin 4 → Bool) : Fin 4 → Bool := iterate c 4

/-- A colouring is a zero forcing set iff its closure is all black. -/
def isZFS (c : Fin 4 → Bool) : Bool := V4.all (fun v => closure c v)

/-- The number of black vertices of a colouring. -/
def zfCard (c : Fin 4 → Bool) : Nat := (V4.filter (fun v => c v)).length

/-- The 16 colourings of the four vertices, indexed by `k : 0..15`; `v` is black
iff bit `v` of `k` is set. -/
def coloringOf (k : Nat) : Fin 4 → Bool :=
  fun v => decide (k / 2 ^ v.val % 2 = 1)

/-- All `2^4 = 16` colourings. -/
def allColorings : List (Fin 4 → Bool) := (List.range 16).map coloringOf

/-- The zero forcing number of `P_4`: the minimum size of a zero forcing set
over all `16` colourings. -/
def zeroForcingNumber : Nat :=
  (allColorings.filter isZFS).foldr (fun c acc => min (zfCard c) acc) 4

/-! ## Path covers

A *path cover* is a partition of the vertex set into parts each of which induces
a path. The *path cover number* `P(G)` is the minimum number of parts.

Because every induced subgraph of a tree is a forest, a set `S` of vertices
induces a path exactly when it is nonempty, has maximum induced degree at most
`2`, and has `|S| - 1` induced edges (that last equality is connectedness for a
forest). Partitions are encoded by idempotent maps `p : Fin 4 → Fin 4`: the
blocks are the nonempty fibres `p⁻¹(i)` over the fixed points `i`, and idempotency
makes these fibres a genuine partition of `V_4`. -/

/-- Number of induced edges of the vertex set `S`, each edge counted once (from
its smaller endpoint). -/
def edgeCount (S : List (Fin 4)) : Nat :=
  (S.map (fun i => (S.filter (fun j => adj i j && decide (i.val < j.val))).length))
    |>.foldr (fun a b => a + b) 0

/-- Maximum induced degree of the vertex set `S`. -/
def maxDegreeIn (S : List (Fin 4)) : Nat :=
  (S.map (fun i => (S.filter (fun j => adj i j)).length)).foldr max 0

/-- `S` induces a path. -/
def isPathBlock (S : List (Fin 4)) : Bool :=
  !S.isEmpty && decide (S.Nodup) && decide (maxDegreeIn S ≤ 2) &&
    decide (edgeCount S + 1 = S.length)

/-- Decode `k : 0..255` as a function `Fin 4 → Fin 4` via its four base-4
digits. As `k` runs over `0..255` this lists all `4^4 = 256` functions. -/
def funOf (k : Nat) : Fin 4 → Fin 4 :=
  fun v => ⟨(k / 4 ^ v.val) % 4, Nat.mod_lt _ (by decide)⟩

/-- All `256` functions `Fin 4 → Fin 4`. -/
def allFun4 : List (Fin 4 → Fin 4) := (List.range 256).map funOf

/-- `p` is idempotent, so its fixed points parametrise a partition of `V_4`. -/
def isIdempotent (p : Fin 4 → Fin 4) : Bool :=
  V4.all (fun i => decide (p (p i) = p i))

/-- The fixed points of `p`; one per block of the encoded partition. -/
def fixedPoints (p : Fin 4 → Fin 4) : List (Fin 4) :=
  V4.filter (fun i => decide (p i = i))

/-- The block of the partition encoded by `p` that has representative `i`. -/
def blockOf (p : Fin 4 → Fin 4) (i : Fin 4) : List (Fin 4) :=
  V4.filter (fun v => decide (p v = i))

/-- `p` encodes a path cover: it is idempotent and every block induces a path. -/
def isPathCover (p : Fin 4 → Fin 4) : Bool :=
  isIdempotent p && (fixedPoints p).all (fun i => isPathBlock (blockOf p i))

/-- The path cover number of `P_4`: the minimum number of blocks over all path
covers, i.e. the minimum number of paths needed to cover `V_4`. -/
def pathCoverNumber : Nat :=
  (allFun4.filter isPathCover).foldr
    (fun p acc => min (fixedPoints p).length acc) 4

/-! ## Diameter -/

/-- Vertices reachable from `s` by a walk of exactly `k` steps. -/
def frontier (s : Fin 4) : Nat → List (Fin 4)
  | 0 => [s]
  | k + 1 => bindL (frontier s k) (fun v => V4.filter (fun w => adj v w))

/-- Search for the first `k` with `t ∈ frontier s k`, starting from `k0` with
fuel `n`; returns `8` if not found within the fuel. -/
def firstReach (s t : Fin 4) : Nat → Nat → Nat
  | 0, _ => 8
  | n + 1, k =>
      if (frontier s k).any (fun w => decide (w = t)) then k
      else firstReach s t n (k + 1)

/-- The graph distance in `P_4`, i.e. the length of a shortest walk (= shortest
path, since `P_4` is a tree). Fuel `8` exceeds the diameter `3`. -/
def graphDist (s t : Fin 4) : Nat := firstReach s t 8 0

/-- Maximum of a list of naturals (`0` on the empty list). -/
def maxIn (l : List Nat) : Nat := l.foldr max 0

/-- The diameter: the largest graph distance between two vertices. -/
def diameter : Nat :=
  maxIn (V4.map (fun s => maxIn (V4.map (fun t => graphDist s t))))

/-- `n` is odd. -/
def isOdd (n : Nat) : Bool := decide (n % 2 = 1)

/-! ## Perfect matchings

The three edges of `P_4` are `(0,1)`, `(1,2)`, `(2,3)`; a subset of them is
encoded by a bit mask `k : 0..7`. It is a perfect matching iff the selected
edges are pairwise disjoint and cover every vertex exactly once. -/

/-- First endpoint of the `i`-th edge of `P_4`. -/
def edgeFirst : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- Second endpoint of the `i`-th edge of `P_4`. -/
def edgeSecond : Nat → Fin 4
  | 0 => 1
  | 1 => 2
  | _ => 3

/-- The `i`-th edge of `P_4` as an unordered pair. -/
def edgeAt (i : Nat) : Fin 4 × Fin 4 := (edgeFirst i, edgeSecond i)

/-- The edges selected by the bit mask `k : 0..7`. -/
def selectedEdges (k : Nat) : List (Fin 4 × Fin 4) :=
  ((List.range 3).filter (fun i => decide (k / 2 ^ i % 2 = 1))).map edgeAt

/-- The endpoints of the selected edges, listed with multiplicity. -/
def endpoints (k : Nat) : List (Fin 4) :=
  bindL (selectedEdges k) (fun e => [e.1, e.2])

/-- `k` is a perfect matching. -/
def isPerfectMatching (k : Nat) : Bool :=
  decide ((endpoints k).length = 4) &&
    V4.all (fun v => decide (((endpoints k).filter (fun w => decide (w = v))).length = 1))

/-- `P_4` has a perfect matching (any of the three masks giving `{01, 23}`). -/
def hasPerfectMatching : Bool := (List.range 8).any isPerfectMatching

/-! ## Computations -/

/-- The singleton `{v1}` (vertex `0`) is a zero forcing set: it forces `1`, then
`2`, then `3`. -/
theorem singleton_zero_forces : isZFS (single 0) = true := by decide

/-- The empty set is not a zero forcing set, so `Z(P_4) ≥ 1`. -/
theorem empty_not_zfs : isZFS (coloringOf 0) = false := by decide

/-- **`Z(P_4) = 1`**, by the minimum over all `16` colourings. -/
theorem zeroForcingNumber_P4 : zeroForcingNumber = 1 := by decide

/-- The whole path `[0,1,2,3]` is a valid path cover, so `P(P_4) ≤ 1`. -/
theorem whole_path_is_path_cover : isPathCover (fun _ => 0) = true := by decide

/-- **`P(P_4) = 1`**, by the minimum over all `256` encoded partitions. -/
theorem pathCoverNumber_P4 : pathCoverNumber = 1 := by decide

/-- **The diameter of `P_4` is `3`.** -/
theorem diameter_P4 : diameter = 3 := by decide

/-- **`diameter(P_4) = 3` is odd.** -/
theorem diameter_P4_odd : isOdd diameter = true := by decide

/-- The mask `5 = 0b101` selects the edges `(0,1)` and `(2,3)`. -/
theorem matching_01_23 : isPerfectMatching 5 = true := by decide

/-- **`P_4` has a perfect matching**, namely `{v1v2, v3v4}`. -/
theorem P4_has_perfect_matching : hasPerfectMatching = true := by decide

/-! ## The difference and the refutation -/

/-- `Z(P_4) - P(P_4) = 0`. -/
def zMinusP : Nat := zeroForcingNumber - pathCoverNumber

/-- **The difference on `P_4` is `0`.** -/
theorem difference_P4 : zMinusP = 0 := by decide

/-- **The difference on `P_4` is not `1`.** -/
theorem difference_P4_ne_one : zMinusP ≠ 1 := by decide

/-- The right-hand classification predicate of the conjecture: odd diameter and a
perfect matching. -/
def rhsPredicate : Bool := isOdd diameter && hasPerfectMatching

/-- `P_4` satisfies the conjecture's right-hand predicate. -/
theorem P4_satisfies_rhsPredicate : rhsPredicate = true := by decide

/-- **The `exactly` clause is false.** `P_4` is an odd-diameter tree with a
perfect matching, yet its difference is `0`, not `1`. -/
theorem exactly_clause_false : rhsPredicate = true ∧ zMinusP ≠ 1 :=
  ⟨P4_satisfies_rhsPredicate, difference_P4_ne_one⟩

/-- **Conjecture `00000001678` is refuted.** All the numerical facts together:
`Z(P_4) = 1`, `P(P_4) = 1`, the difference is `0` and hence not `1`, while the
diameter is `3` (odd) and `P_4` has a perfect matching. -/
theorem conjecture_00000001678_refuted :
    diameter = 3 ∧ isOdd diameter = true ∧ hasPerfectMatching = true ∧
    zeroForcingNumber = 1 ∧ pathCoverNumber = 1 ∧ zMinusP = 0 ∧ zMinusP ≠ 1 :=
  ⟨diameter_P4, diameter_P4_odd, P4_has_perfect_matching,
    zeroForcingNumber_P4, pathCoverNumber_P4, difference_P4, difference_P4_ne_one⟩

end Tlmc1678
