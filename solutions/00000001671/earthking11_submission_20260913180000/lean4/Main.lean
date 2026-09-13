import Std

-- The exhaustive `decide` proofs below reduce nested folds over all subsets of
-- the family of even subgraphs of `K_3` and `K_4`; the default elaborator
-- recursion depth is too small for this.
set_option maxRecDepth 100000

/-!
# Refutation of conjecture 00000001671 (core Lean, no Mathlib)

The conjecture states that the *basis number* of the complete graph `K_n` — the
least `k` such that the cycle space of `K_n` has a cycle basis in which every
edge occurs in at most `k` of the basis cycles — equals

    b(K_n) = ⌈(n+3)/2⌉.

This file formalises a counterexample using only core Lean (`import Std`), with
no Mathlib, no `sorry`, no `axiom`, and no `native_decide`.

## Model

An edge subset of `K_n` is coded as a `Nat` bitmask whose bit `i` records
membership of the `i`-th edge of `edgesOf n`.  Over `GF(2)` the cycle space of a
connected graph is exactly the set of edge subsets in which every vertex has even
degree, so a *cycle* is an edge mask with even degree at every vertex.  The four
edges of `K_3` / the six edges of `K_4` are listed explicitly; the cycle set and
the `k`-fold basis predicate are then computed by pure structural recursion, so
the kernel can reduce them during `decide`.

`IsKFoldBasis n k basis` requires that every listed mask is a cycle, that there
are exactly `|E| − |V| + 1` of them, that their `GF(2)` span is the whole cycle
space (hence they are linearly independent), and that every edge lies in at most
`k` of them.  `minBasisNumber n` searches the subsets of the cycle set of the
correct cardinality and returns the first `k` for which such a basis exists.

## Key facts proved below

* `basis_three_is_one : minBasisNumber 3 = 1`   (the triangle alone; every edge
  is in exactly one basis cycle)
* `basis_four_is_two : minBasisNumber 4 = 2`    (three triangles)
* `no_one_fold_four : hasKFoldBasis 4 1 = false`
* `formula 3 = 3`, `formula 4 = 4`              (the conjectured values)
* `conjecture_00000001671_false`                (collecting the mismatches)
-/

namespace Tlmc1671

/-! ## Kernel-reducible bit primitives

Core Lean's `Nat.div` / `Nat.mod` are opaque to the kernel reducer, so we use
purely structural recursion instead. -/

/-- Parity of a natural number, by structural recursion. -/
def parityOf : Nat → Bool
  | 0 => false
  | 1 => true
  | n + 2 => parityOf n

/-- Floor of `n / 2`, by structural recursion. -/
def halfOf : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halfOf n + 1

/-- Bit `i` (least significant first) of the mask `n`. -/
def bitAt : Nat → Nat → Bool
  | 0, n => parityOf n
  | i + 1, n => bitAt i (halfOf n)

/-- `2 ^ k`, by structural recursion. -/
def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

/-- `rangeFrom n start = [start, start+1, …, start+n-1]`, by structural
recursion (unlike `List.range`, this needs no well-founded recursion). -/
def rangeFrom : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, start => start :: rangeFrom n (start + 1)

/-- Number of set bits among positions `0..width-1` of `n`. -/
def popcountBelow (width n : Nat) : Nat :=
  (rangeFrom width 0).foldl (fun acc i => if bitAt i n then acc + 1 else acc) 0

/-! ## The complete graph `K_n` -/

/-- The edges of `K_n` as pairs of vertex numbers.  Only the small cases used
below are tabulated; `K_n` is a simple graph, so every unordered pair `{u,v}`
with `u < v` appears exactly once. -/
def edgesOf : Nat → List (Nat × Nat)
  | 3 => [(0, 1), (0, 2), (1, 2)]
  | 4 => [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
  | _ => []

/-- The edges of `K_n` annotated with their bit index: `(i, u, v)` means edge
`i` of `edgesOf n` joins `u` and `v`. -/
def indexedEdgesAux : List (Nat × Nat) → Nat → List (Nat × Nat × Nat)
  | [], _ => []
  | e :: rest, i => (i, e.1, e.2) :: indexedEdgesAux rest (i + 1)

/-- The indexed edge list of `K_n`. -/
def indexedEdges (n : Nat) : List (Nat × Nat × Nat) :=
  indexedEdgesAux (edgesOf n) 0

/-- Dimension of the cycle space of the connected graph `K_n`, namely
`|E| − |V| + 1`. -/
def cycleDim (n : Nat) : Nat := (edgesOf n).length - n + 1

/-- Number of incident edges of vertex `v` that belong to the edge subset
`mask`. -/
def degreeIn (n v mask : Nat) : Nat :=
  (indexedEdges n).foldl
    (fun acc t =>
      if (t.2.1 == v || t.2.2 == v) && bitAt t.1 mask then acc + 1 else acc)
    0

/-- `isCycle n mask` is true when every vertex of `K_n` has even degree in the
edge subset `mask`; over `GF(2)` these are exactly the elements of the cycle
space. The empty set is included. -/
def isCycle (n mask : Nat) : Bool :=
  (rangeFrom n 0).all (fun v => parityOf (degreeIn n v mask) == false)

/-- All elements of the cycle space of `K_n`, enumerated as bitmasks. -/
def cycleMasks (n : Nat) : List Nat :=
  (rangeFrom (pow2 (edgesOf n).length) 0).filter (isCycle n)

/-! ## The `k`-fold basis predicate -/

/-- Bitwise XOR of two `width`-bit masks, computed by a structural fold over bit
positions.  Core `Nat.xor` is opaque to the kernel reducer and would drag the
`propext` axiom into the `decide` proofs, so we re-implement XOR here. -/
def xorBits (width a b : Nat) : Nat :=
  (rangeFrom width 0).foldl
    (fun acc i => if (bitAt i a) == (bitAt i b) then acc else acc + pow2 i)
    0

/-- XOR of the elements of `basis` selected by the subset bitmask `s` (bit `i`
of `s` selects `basis[i]`). -/
def xorSelected (width : Nat) : Nat → List Nat → Nat → Nat
  | _, [], _ => 0
  | i, b :: rest, s =>
      xorBits width (if bitAt i s then b else 0) (xorSelected width (i + 1) rest s)

/-- `spanContains width basis target` is true when `target` lies in the `GF(2)`
span of `basis`, i.e. equals the XOR of some sublist of `basis`. -/
def spanContains (width : Nat) (basis : List Nat) (target : Nat) : Bool :=
  (rangeFrom (pow2 basis.length) 0).any
    (fun s => xorSelected width 0 basis s == target)

/-- Every edge of `K_n` occurs in at most `k` of the cycles of `basis`. -/
def edgeMultiplicityOK (n k : Nat) (basis : List Nat) : Bool :=
  (rangeFrom (edgesOf n).length 0).all
    (fun i => Nat.ble
      (basis.foldl (fun acc b => if bitAt i b then acc + 1 else acc) 0) k)

/-- `IsKFoldBasis n k basis` holds when `basis` is a cycle basis of `K_n` — its
members are cycles, there are `cycleDim n` of them, and their `GF(2)` span is
the whole cycle space — and every edge occurs in at most `k` of its cycles. -/
def IsKFoldBasis (n k : Nat) (basis : List Nat) : Bool :=
  basis.all (isCycle n) &&
  (basis.length == cycleDim n) &&
  (cycleMasks n).all (fun c => spanContains (edgesOf n).length basis c) &&
  edgeMultiplicityOK n k basis

/-- All sublists of `xs` having exactly `k` elements. -/
def subsetsOfSize : List Nat → Nat → List (List Nat)
  | [], 0 => [[]]
  | [], (_ + 1) => []
  | _ :: xs, 0 => subsetsOfSize xs 0
  | x :: xs, k + 1 => subsetsOfSize xs (k + 1) ++ (subsetsOfSize xs k).map (fun s => x :: s)

/-- `hasKFoldBasis n k` is true when some sublist of the cycle set of `K_n` of
the correct cardinality is a `k`-fold cycle basis. -/
def hasKFoldBasis (n k : Nat) : Bool :=
  (subsetsOfSize (cycleMasks n) (cycleDim n)).any (IsKFoldBasis n k)

/-- First element of `ks` satisfying `hasKFoldBasis n ·`. -/
def findK (n : Nat) : List Nat → Nat
  | [] => cycleDim n + 1
  | k :: rest => if hasKFoldBasis n k then k else findK n rest

/-- The basis number of `K_n`: the least `k` admitting a `k`-fold cycle basis.
The search starts at `0`; `cycleDim n + 1` is an unreachable sentinel. -/
def minBasisNumber (n : Nat) : Nat :=
  findK n (rangeFrom (cycleDim n + 2) 0)

/-- The conjectured value `⌈(n+3)/2⌉`, written as the integer division
`(n+4)/2` (these agree for natural numbers). -/
def formula (n : Nat) : Nat := (n + 4) / 2

/-! ## Explicit witnesses -/

/-- The single triangle of `K_3`: edges `(0,1), (0,2), (1,2)`, i.e. bits
`0,1,2`. -/
def k3Basis1 : List Nat := [7]

/-- Three triangles of `K_4`: `{0,1,2} = 11`, `{0,1,3} = 21`, `{0,2,3} = 38`
(bits `0,1,3` / `0,2,4` / `1,2,5`). -/
def k4Basis2 : List Nat := [11, 21, 38]

/-! ## Counterexample theorems -/

/-- `K_3` has a one-fold basis (its only independent cycle), so `b(K_3) = 1`. -/
theorem basis_three_is_one : minBasisNumber 3 = 1 := by decide

/-- `K_4` admits a two-fold basis and no one-fold basis, so `b(K_4) = 2`. -/
theorem basis_four_is_two : minBasisNumber 4 = 2 := by decide

/-- No one-fold basis of `K_4` exists. -/
theorem no_one_fold_four : hasKFoldBasis 4 1 = false := by decide

/-- The explicit triangle of `K_3` is a one-fold basis. -/
theorem k3_basis_is_one_fold : IsKFoldBasis 3 1 k3Basis1 = true := by decide

/-- The three explicit triangles of `K_4` form a two-fold basis. -/
theorem k4_basis_is_two_fold : IsKFoldBasis 4 2 k4Basis2 = true := by decide

/-- The conjectured formula at `n = 3` is `⌈6/2⌉ = 3`. -/
theorem formula_three : formula 3 = 3 := by decide

/-- The conjectured formula at `n = 4` is `⌈7/2⌉ = 4`. -/
theorem formula_four : formula 4 = 4 := by decide

/-- The formula is wrong at `n = 3`: `3 ≠ 1`. -/
theorem mismatch_three : formula 3 ≠ minBasisNumber 3 := by decide

/-- The formula is wrong at `n = 4`: `4 ≠ 2`. -/
theorem mismatch_four : formula 4 ≠ minBasisNumber 4 := by decide

/-- **Conjecture 00000001671 is false.**  The true basis numbers `b(K_3) = 1`
and `b(K_4) = 2` differ from the conjectured `⌈(n+3)/2⌉ = 3, 4`. -/
theorem conjecture_00000001671_false :
    minBasisNumber 3 = 1 ∧ minBasisNumber 4 = 2 ∧
    formula 3 = 3 ∧ formula 4 = 4 ∧
    formula 3 ≠ minBasisNumber 3 ∧ formula 4 ≠ minBasisNumber 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Tlmc1671
