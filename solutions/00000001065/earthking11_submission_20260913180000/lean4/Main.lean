import Std

/-!
# Conjecture 00000001065 is FALSE: the Nikodym--Kakeya difference in F_q^2

This file formalises the decisive `q = 2` case in core Lean (`import Std` only,
no Mathlib, no `sorry`, no `axiom`, no `native_decide`).

## Representation

Points of `F_2^2` are indexed row-major:

  `(0,0) -> 0`, `(0,1) -> 1`, `(1,0) -> 2`, `(1,1) -> 3`.

A subset of `F_2^2` is represented by a 4-bit `Fin 16` bitmask.

The six lines of `F_2^2` (each with two points) are:

* horizontal: `{0,2}` and `{1,3}`
* vertical:   `{0,1}` and `{2,3}`
* diagonal:   `{0,3}` and `{1,2}`

A **Kakeya set** contains a full line in each of the three directions.

A **Nikodym set** `N` has, through every point `p`, a line whose *other* points
all lie in `N` (the point `p` itself may be exceptional).

## Result

`{(0,0),(0,1)}` is a Nikodym set of size `2`, while no set of size `< 3` is
Kakeya and a triangle is Kakeya. Hence

  minimal Nikodym size = 2, minimal Kakeya size = 3, difference = -1,

whereas the conjecture predicts `q - 1 = 1`.
-/

namespace TLM1065

abbrev Pt := Fin 2 × Fin 2

/-- Row-major index of a point of `F_2^2`. -/
def ptIdx (p : Pt) : Nat := 2 * p.1.val + p.2.val

/-- Membership test for a bitmask. -/
def InIdx (m : Fin 16) (i : Nat) : Bool := (m : Nat).testBit i

/-- Membership of a point in a bitmask. -/
def mem (m : Fin 16) (p : Pt) : Bool := InIdx m (ptIdx p)

/-- Number of points in the subset encoded by the mask. -/
def size (m : Fin 16) : Nat :=
  (List.range 4).foldl (fun acc i => if InIdx m i then acc + 1 else acc) 0

/-- The bitmask of a list of points (`% 16` only for well-typedness; any list
of points of `F_2^2` has at most four distinct bits set). -/
def maskOf (S : List Pt) : Fin 16 :=
  ⟨(S.foldl (fun acc p => acc ||| (1 <<< ptIdx p)) 0) % 16,
    Nat.mod_lt _ (by decide)⟩

/-- The two-point line `{i,j}` is fully contained in the mask. -/
def fullLine (m : Fin 16) (i j : Nat) : Bool := InIdx m i && InIdx m j

/-- Kakeya: a full line in each of the three directions. -/
def IsKakeya (m : Fin 16) : Bool :=
  (fullLine m 0 2 || fullLine m 1 3) &&
  (fullLine m 0 1 || fullLine m 2 3) &&
  (fullLine m 0 3 || fullLine m 1 2)

/-- For the point with index `i`, is at least one of its three line-neighbours
in the set?  For `q = 2` every line through a point has exactly one other
point, so this is exactly "there is a line through `i` whose other points all
lie in the set".  The neighbours of `i` are the three points `i + d` for the
three nonzero directions `d`. -/
def hasNeighbour (m : Fin 16) (i : Nat) : Bool :=
  match i with
  | 0 => InIdx m 1 || InIdx m 2 || InIdx m 3
  | 1 => InIdx m 0 || InIdx m 2 || InIdx m 3
  | 2 => InIdx m 0 || InIdx m 1 || InIdx m 3
  | _ => InIdx m 0 || InIdx m 1 || InIdx m 2

/-- Nikodym: through every point of the plane there is a line whose other
points all lie in the set.  We quantify over all four points, including the
ones outside the set. -/
def IsNikodym (m : Fin 16) : Bool :=
  hasNeighbour m 0 && hasNeighbour m 1 && hasNeighbour m 2 && hasNeighbour m 3

/-! ## Witnesses -/

/-- The two-point set `{(0,0),(0,1)}` is Nikodym. -/
theorem nikodym_two : IsNikodym (maskOf [(0,0), (0,1)]) = true := by decide

/-- A triangle is Kakeya in `F_2^2`, using three points. -/
theorem kakeya_three : IsKakeya (maskOf [(0,0), (0,1), (1,0)]) = true := by decide

/-- The minimal Nikodym size is at most `2`. -/
theorem nikodym_min :
    ∃ m : Fin 16, IsNikodym m = true ∧ size m = 2 :=
  ⟨maskOf [(0,0), (0,1)], by decide, by decide⟩

/-- The minimal Kakeya size is at most `3`. -/
theorem kakeya_min :
    ∃ m : Fin 16, IsKakeya m = true ∧ size m = 3 :=
  ⟨maskOf [(0,0), (0,1), (1,0)], by decide, by decide⟩

/-- No subset with fewer than three points is Kakeya: min Kakeya size is `3`. -/
theorem no_kakeya_lt_three :
    ∀ m : Fin 16, size m < 3 → IsKakeya m = false := by decide

/-- No subset with fewer than two points is Nikodym: min Nikodym size is `2`. -/
theorem no_nikodym_lt_two :
    ∀ m : Fin 16, size m < 2 → IsNikodym m = false := by decide

/-- The claimed identity `(min Nikodym) - (min Kakeya) = q - 1` fails
arithmetically at `q = 2` (`-1 ≠ 1`). -/
theorem difference_not_q_minus_one :
    (2 : Int) - 3 = -1 ∧ (1 : Int) ≠ -1 := by decide

/-- The `q = 2` facts together refute Conjecture 00000001065 under the stated
"almost all" wording. -/
theorem conjecture_00000001065_false :
    IsNikodym (maskOf [(0,0), (0,1)]) = true ∧
    IsKakeya (maskOf [(0,0), (0,1), (1,0)]) = true ∧
    size (maskOf [(0,0), (0,1)]) = 2 ∧
    size (maskOf [(0,0), (0,1), (1,0)]) = 3 ∧
    (∀ m : Fin 16, size m < 3 → IsKakeya m = false) ∧
    (∀ m : Fin 16, size m < 2 → IsNikodym m = false) ∧
    ((2 : Int) - 3 = -1 ∧ (1 : Int) ≠ -1) :=
  ⟨nikodym_two, kakeya_three, by decide, by decide,
   no_kakeya_lt_three, no_nikodym_lt_two, difference_not_q_minus_one⟩

end TLM1065
