import Std

-- The exhaustive `decide` proofs below reduce a 512-element `List` fold, which
-- exceeds the default elaborator recursion depth.
set_option maxRecDepth 100000

/-!
# Refutation of conjecture 00000001676 (core Lean, no Mathlib)

The conjecture states that the isoperimetric profile of the `n × n` torus grid
`C_n □ C_n` (the Cartesian product of two cycles) is

    ip(m) = ⌈4 * sqrt(n*m − m²)⌉      for all m ≤ n²/2,

attained by diagonal cuts.

This file formalises a counterexample using only core Lean (`import Std`), with
no Mathlib, no `sorry`, no `axiom`, and no `native_decide`.

## Model

`C_3 □ C_3` is modelled on the nine vertices `Fin 3 × Fin 3`, identified with
the bit positions `0..8` of a 9-bit `Nat` bitmask.  Two vertices are adjacent
when they differ in exactly one coordinate, differences being taken mod 3 (the
torus wrap-around).  There are 18 edges.

## Key facts proved below

* `minBoundaryOfSize 1 = 4`   (a single vertex has closed-degree 4)
* `minBoundaryOfSize 3 = 6`   (a full row of the torus has boundary 6)
* `formula 3 3 = 0`            (the conjecture predicts 0)
* `formula 3 3 ≠ minBoundaryOfSize 3`  (0 ≠ 6: the clean counterexample)
* `(3 : Int) * 4 − 4 * 4 < 0`  (for n = 3, m = 4 the radicand is negative, so
  the formula is not even real, yet m = 4 ≤ n²/2 = 4.5 is inside the stated
  range)
-/

namespace Tlmc1676

/-! ## Kernel-reducible bit primitives

Core Lean's `Nat.sqrt` (and `Nat.div`/`Nat.mod`) are not reliably reducible by
the kernel for `by decide`.  We therefore use purely structural recursion, which
the kernel evaluates without difficulty. -/

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

/-- `rangeFrom n start = [start, start+1, …, start+n-1]`, by structural
recursion (unlike `List.range`, this needs no well-founded recursion). -/
def rangeFrom : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, start => start :: rangeFrom n (start + 1)

/-- Number of set bits among positions `0..8` of `n`. -/
def popcountBits (n : Nat) : Nat :=
  (rangeFrom 9 0).foldl (fun acc i => if bitAt i n then acc + 1 else acc) 0

/-! ## The torus `C_3 □ C_3` -/

/-- The 18 edges of `C_3 □ C_3`, as pairs of bit indices.  Vertex `3*i + j`
stands for `(i, j) ∈ Fin 3 × Fin 3`.  The first nine pairs are the row edges
`(i,j) — (i,(j+1) mod 3)`, the last nine the column edges
`(i,j) — ((i+1) mod 3, j)`. -/
def torusEdges : List (Nat × Nat) :=
  [ (0, 1), (1, 2), (2, 0),
    (3, 4), (4, 5), (5, 3),
    (6, 7), (7, 8), (8, 6),
    (0, 3), (1, 4), (2, 5),
    (3, 6), (4, 7), (5, 8),
    (6, 0), (7, 1), (8, 2) ]

/-- Number of edges of `C_3 □ C_3` with exactly one endpoint in the vertex set
coded by the 9-bit mask `S`.  The core `!=` on `Bool` is the "exactly one" test. -/
def edgeBoundary (S : Nat) : Nat :=
  (torusEdges.filter
    (fun e => (bitAt e.1 S) != (bitAt e.2 S))).length

/-- The minimum edge boundary over all 9-bit masks having exactly `k` set bits.
The search folds over all `2^9 = 512` masks.  The seed `1000` is irrelevant for
the sizes used below (the filtered lists are non-empty and boundaries are small),
it merely keeps the fold total. -/
def minBoundaryOfSize (k : Nat) : Nat :=
  ((rangeFrom 512 0).filter (fun m => (popcountBits m) == k)).foldl
    (fun acc m => min acc (edgeBoundary m)) 1000

/-! ## The conjectured formula -/

/-- Computable ceiling of the square root, via a bounded linear search.  This is
used instead of `Nat.sqrt`, which is opaque to the kernel reducer. -/
def ceilSqrt (N : Nat) : Nat :=
  match (rangeFrom (N + 1) 0).find? (fun s => Nat.ble N (s * s)) with
  | some s => s
  | none => N + 1

/-- The conjectured profile `⌈4·sqrt(n·m − m²)⌉`, encoded without `Nat.sqrt` as
`ceilSqrt (16·(n·m − m²))`.  (Writing it as `4 * ceilSqrt (n*m − m*m)` would
compute `4·⌈sqrt(N)⌉`, which is a different quantity: the conjecture's own
example `(n,m) = (3,1)` gives `⌈4√2⌉ = 6`, whereas `4·⌈√2⌉ = 8`.) -/
def formula (n m : Nat) : Nat :=
  ceilSqrt (16 * (n * m - m * m))

/-! ## Counterexample theorems -/

/-- A single vertex has boundary its closed degree `4`; the formula at
`(n,m) = (3,1)` gives `⌈4√2⌉ = 6`. -/
theorem minBoundaryOfSize_one : minBoundaryOfSize 1 = 4 := by decide

/-- A full row of `C_3 □ C_3` has boundary `6`, and this is minimal. -/
theorem minBoundaryOfSize_three : minBoundaryOfSize 3 = 6 := by decide

/-- At `(n,m) = (3,3)` the radicand is `3*3 − 3*3 = 0`, so the formula is `0`. -/
theorem formula_3_3 : formula 3 3 = 0 := by decide

/-- At `(n,m) = (3,1)` the formula is `⌈4√2⌉ = 6`. -/
theorem formula_3_1 : formula 3 1 = 6 := by decide

/-- **Cleanest counterexample.**  At `(n,m) = (3,3)` the conjecture predicts `0`
but the true minimum edge boundary is `6`. -/
theorem mismatch_3_3 : formula 3 3 ≠ minBoundaryOfSize 3 := by decide

/-- The formula is also wrong at `(n,m) = (3,1)`: `6` versus the true `4`. -/
theorem mismatch_3_1 : formula 3 1 ≠ minBoundaryOfSize 1 := by decide

/-- **Ill-posedness.**  For `n = 3`, `m = 4` we have `m ≤ n²/2 = 4.5`, yet the
radicand `n·m − m² = 12 − 16 = −4` is negative: the formula is not real. -/
theorem radicand_negative_3_4 : (3 : Int) * 4 - 4 * 4 < 0 := by decide

/-- Conjecture 00000001676 is **false**: at `(n,m) = (3,3)` the formula gives `0`
while the true minimum edge boundary is `6`, and at `(n,m) = (3,4)` the radicand
is negative even though `m` lies in the stated range. -/
theorem conjecture_00000001676_false :
    formula 3 3 = 0 ∧ minBoundaryOfSize 3 = 6 ∧
    formula 3 3 ≠ minBoundaryOfSize 3 ∧
    (3 : Int) * 4 - 4 * 4 < 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Tlmc1676
