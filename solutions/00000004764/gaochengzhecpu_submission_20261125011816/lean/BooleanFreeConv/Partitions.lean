/-
  Conjecture 00000004764 — Set Partitions, Interval Partitions `Int(n)`,
  Noncrossing Partitions `NC(n)`, and Irreducible Noncrossing Partitions `NC_irr(n)`
  Core Lean 4.19.0 (zero external dependencies)
-/
import BooleanFreeConv.Series

namespace BooleanFreeConv

/-- Maximum element of a `List Nat` (`0` on the empty list). -/
def maxList : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.max x (maxList xs)

/-- Last element of a `List Nat` (`0` on the empty list). -/
def lastOrZero : List Nat → Nat
  | [] => 0
  | [x] => x
  | _ :: xs => lastOrZero xs

/-- Canonical set partitions of `{0, ..., n - 1}` represented bijectively as
    restricted growth strings (RGS). -/
def allRGS : Nat → List (List Nat)
  | 0 => [[]]
  | 1 => [[0]]
  | n + 2 =>
    (allRGS (n + 1)).flatMap fun p =>
      (List.range (maxList p + 2)).map fun lbl => p ++ [lbl]

/-- Weakly increasing RGS predicate characterizing interval partitions `Int(n)`. -/
def isWeaklyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a ≤ b) && isWeaklyIncreasing (b :: rest)

/-- Direct inductive construction of `Int(n)` via RGS: each new element either joins
    the last interval (`lastOrZero p`) or starts a new interval (`lastOrZero p + 1`). -/
def intPartitions : Nat → List (List Nat)
  | 0 => [[]]
  | 1 => [[0]]
  | n + 2 =>
    (intPartitions (n + 1)).flatMap fun p =>
      [p ++ [lastOrZero p], p ++ [lastOrZero p + 1]]

theorem length_flatMap_pair {α β : Type} (f g : α → β) :
    ∀ l : List α, (l.flatMap (fun x => [f x, g x])).length = 2 * l.length
  | [] => rfl
  | _ :: xs => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
    rw [length_flatMap_pair f g xs]
    omega

/-- Positive universal theorem: for EVERY `m : Nat`, `|Int(m + 1)| = 2^m`
    (equivalently `|Int(n)| = 2^(n - 1)` for all `n ≥ 1`). -/
theorem intPartitions_card_pow2 (m : Nat) :
    (intPartitions (m + 1)).length = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp only [intPartitions]
    rw [length_flatMap_pair (fun p => p ++ [lastOrZero p]) (fun p => p ++ [lastOrZero p + 1]), ih]
    rw [Nat.pow_succ]
    omega

/-- Crossing detector on restricted growth strings: checks whether there exist
    `0 ≤ a < b < c < d < n` with `p[a] = p[c]`, `p[b] = p[d]`, and `p[a] ≠ p[b]`. -/
def hasCrossing (p : List Nat) : Bool :=
  let n := p.length
  (List.range n).any fun a =>
    (List.range n).any fun b =>
      (List.range n).any fun c =>
        (List.range n).any fun d =>
          decide (a < b) && decide (b < c) && decide (c < d) &&
          decide (p.getD a 0 = p.getD c 0) &&
          decide (p.getD b 0 = p.getD d 0) &&
          decide (p.getD a 0 ≠ p.getD b 0)

/-- Noncrossing partition predicate (`NC(n)`). -/
def isNoncrossing (p : List Nat) : Bool :=
  !hasCrossing p

/-- Irreducible noncrossing partition predicate (`NC_irr(n)`): noncrossing and
    `0` and `n - 1` belong to the same outer block (`0` in canonical RGS). -/
def isIrreducibleNC (p : List Nat) : Bool :=
  match p with
  | [] => false
  | _ => isNoncrossing p && decide (p.getD 0 0 = p.getD (p.length - 1) 0)

/-- All noncrossing partitions `NC(n)` of `{0, ..., n - 1}`. -/
def ncPartitions (n : Nat) : List (List Nat) :=
  (allRGS n).filter isNoncrossing

/-- All irreducible noncrossing partitions `NC_irr(n)` of `{0, ..., n - 1}`. -/
def ncIrrPartitions (n : Nat) : List (List Nat) :=
  (allRGS n).filter isIrreducibleNC

/-- Block size of label `b` in an RGS `p`. -/
def blockSize (p : List Nat) (b : Nat) : Nat :=
  (p.filter fun x => decide (x = b)).length

def listProdInt : List Int → Int
  | [] => 1
  | x :: xs => x * listProdInt xs

def listSumInt : List Int → Int
  | [] => 0
  | x :: xs => x + listSumInt xs

/-- Cumulant monomial weight `∏_{B ∈ π} c_{|B|}` of a partition `π`. -/
def partWeight (cum : Series) (p : List Nat) : Int :=
  match p with
  | [] => 1
  | _ =>
    listProdInt ((List.range (maxList p + 1)).map fun b => cum (blockSize p b))

/-- Combinatorial partition sum `∑_{π ∈ P} ∏_{B ∈ π} c_{|B|}`. -/
def partitionSum (parts : List (List Nat)) (cum : Series) : Int :=
  listSumInt (parts.map (partWeight cum))

/-- Consistency check: `intPartitions n` matches filtering `allRGS n` by `isWeaklyIncreasing`. -/
theorem intPartitions_eq_filter_1_to_4 :
    intPartitions 1 = (allRGS 1).filter isWeaklyIncreasing ∧
    intPartitions 2 = (allRGS 2).filter isWeaklyIncreasing ∧
    intPartitions 3 = (allRGS 3).filter isWeaklyIncreasing ∧
    intPartitions 4 = (allRGS 4).filter isWeaklyIncreasing := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Exact Catalan counts `|NC(n)| = 1, 2, 5, 14` for `n = 1, 2, 3, 4`. -/
theorem ncPartitions_counts :
    (ncPartitions 1).length = 1 ∧
    (ncPartitions 2).length = 2 ∧
    (ncPartitions 3).length = 5 ∧
    (ncPartitions 4).length = 14 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Exact shifted Catalan counts `|NC_irr(n)| = 1, 1, 2, 5` for `n = 1, 2, 3, 4`. -/
theorem ncIrrPartitions_counts :
    (ncIrrPartitions 1).length = 1 ∧
    (ncIrrPartitions 2).length = 1 ∧
    (ncIrrPartitions 3).length = 2 ∧
    (ncIrrPartitions 4).length = 5 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Low-order agreement at `n = 1, 2`: `|NC(1)| = |Int(1)| = 1` and `|NC(2)| = |Int(2)| = 2`. -/
theorem nc_vs_int_low_orders_pow2 :
    IsSignedPowTwoRatio ((intPartitions 1).length : Int) ((ncPartitions 1).length : Int) ∧
    IsSignedPowTwoRatio ((intPartitions 2).length : Int) ((ncPartitions 2).length : Int) := by
  exact ⟨Or.inl ⟨0, rfl⟩, Or.inl ⟨0, rfl⟩⟩

/-- Combinatorial Reading Disproof at `n = 3`:
    `|Int(3)| = 4 = 2^2`, whereas `|NC(3)| = C_3 = 5`, so `|NC(3)| / |Int(3)| = 5 / 4`
    is not any integer or rational power of two. -/
theorem nc_vs_int_order3_not_pow2 :
    ¬ IsRatPowTwoRatio ((intPartitions 3).length : Int) ((ncPartitions 3).length : Int) := by
  apply not_isRatPowTwoRatio_of_mod_five
  · exact Or.inr (Or.inr (Or.inl rfl))
  · rfl

/-- Irreducible noncrossing count `|NC_irr(4)| = 5` is not any power of two. -/
theorem ncIrr_order4_not_pow2 :
    ¬ IsRatPowTwoRatio 1 ((ncIrrPartitions 4).length : Int) := by
  apply not_isRatPowTwoRatio_of_mod_five
  · exact Or.inl rfl
  · rfl

end BooleanFreeConv
