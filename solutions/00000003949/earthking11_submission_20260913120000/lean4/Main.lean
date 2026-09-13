import Std

/-!
# Rule-3 disproof for conjecture 00000003949 (grid burning number)

The conjecture states that the burning number of the `n × n` square grid is
*exactly* `⌈2·√n − 1⌉`.  This file refutes that statement at `n = 4`.

The whole development is self-contained: it uses only core Lean 4 plus `Std`.
No `Mathlib`, no `sorry`, no `axiom`, no `native_decide`.

A cell of the `4 × 4` grid is a pair `(row, col) : Fin 4 × Fin 4`.  A finite set
of cells is represented by a `Nat` bitmask with bit `row*4 + col`.  The burning
process is encoded by the standard equivalent characterisation

  `b(G) = min { k | ∃ v₁,…,v_k, ⋃ᵢ B(vᵢ, k−i) = V(G) }`

i.e. the round-`i` source has radius `k − i`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Tlmc3949

/-- A cell of the `4 × 4` grid. -/
abbrev Cell := Fin 4 × Fin 4

/-- Absolute difference of two naturals. -/
def absDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- Manhattan distance on the grid, expressed through `Nat` subtraction on `.val`s. -/
def dist (p q : Cell) : Nat :=
  absDiff p.1.val q.1.val + absDiff p.2.val q.2.val

/-- Bitmask of a single cell: bit `row*4 + col`. -/
def bit (p : Cell) : Nat := 2 ^ (p.1.val * 4 + p.2.val)

/-- All 16 cells, listed row by row. -/
def allCells : List Cell :=
  [(0,0), (0,1), (0,2), (0,3),
   (1,0), (1,1), (1,2), (1,3),
   (2,0), (2,1), (2,2), (2,3),
   (3,0), (3,1), (3,2), (3,3)]

/-- Bitmask of the closed ball of radius `r` around `c`. -/
def ballMask (c : Cell) (r : Nat) : Nat :=
  List.foldr (fun p acc => if dist c p ≤ r then acc ||| bit p else acc) 0 allCells

/-- Union of the balls whose centres and radii are given in parallel lists. -/
def unionMasks : List Cell → List Nat → Nat
  | c :: cs, r :: rs => ballMask c r ||| unionMasks cs rs
  | _, _ => 0

/-- The full `4 × 4` grid as a bitmask (`2^16 − 1`). -/
def full : Nat := 65535

/-- `covers centres radii` is `true` iff the union of the corresponding closed
balls is the whole grid. -/
def covers (centres : List Cell) (radii : List Nat) : Bool :=
  unionMasks centres radii == full

/-- Number of `c1` such that `(c0, c1, c2)` over all `c2` (radii `2,1,0`)
covers the grid, summed over `c2`. -/
def countFor (c0 : Cell) : Nat :=
  (allCells.map (fun c1 =>
    (allCells.map (fun c2 => if covers [c0, c1, c2] [2, 1, 0] then 1 else 0)).sum)).sum

/-- Total number of ordered triples `(c0,c1,c2)` of centres whose balls of radii
`2,1,0` cover all 16 cells. -/
def countTriples : Nat := (allCells.map countFor).sum

/--
**No 3-round cover exists.**  Of the `16³ = 4096` ordered triples of centres
with radii `2, 1, 0`, not one covers all 16 cells.  Proved by exhaustive
kernel reduction (`decide`).
-/
theorem no_three_cover : countTriples = 0 := by decide

/--
**A 4-round cover exists.**  Witness:
round 1 at `(0,0)` radius 3, round 2 at `(0,2)` radius 2,
round 3 at `(3,2)` radius 1, round 4 at `(2,3)` radius 0.
-/
theorem four_cover_exists :
    ∃ c0 c1 c2 c3 : Cell, covers [c0, c1, c2, c3] [3, 2, 1, 0] = true :=
  ⟨(0,0), (0,2), (3,2), (2,3), by decide⟩

/-- Smallest `k` with `k*k ≥ x` (integer ceiling of the square root).
Computed by a bounded fold so that it reduces definitionally under `decide`
(`Nat.sqrt` is opaque to the kernel reducer).  For `x ≥ 1` the answer is at
most `x`, since `x*x ≥ x`. -/
def ceilSqrt (x : Nat) : Nat :=
  (List.range (x + 1)).foldr (fun k acc => if k * k ≥ x then k else acc) (x + 1)

/-- The conjectured closed form `⌈2·√n − 1⌉`, written as `⌈√(4n)⌉ − 1`. -/
def formulaValue (n : Nat) : Nat := ceilSqrt (4 * n) - 1

/--
**The conjecture is false at `n = 4`.**  The closed form returns `3`, no
3-round cover exists, yet an explicit 4-round cover does exist; hence
`3 ≠ 4`.
-/
theorem conjecture_00000003949_false :
    formulaValue 4 = 3 ∧ countTriples = 0 ∧
      (∃ c0 c1 c2 c3 : Cell, covers [c0, c1, c2, c3] [3, 2, 1, 0] = true) ∧
      (3 ≠ 4) :=
  ⟨by decide, no_three_cover, four_cover_exists, by decide⟩

end Tlmc3949
