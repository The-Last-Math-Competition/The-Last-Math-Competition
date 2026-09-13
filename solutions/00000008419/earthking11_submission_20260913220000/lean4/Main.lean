/-
  Refutation of conjecture `00000008419`: Lean 4 formalisation (core Lean only).

  Conjecture (as filed):

    "For a code with dual distance d^⊥ at least t+1, all minimal codewords form
     t-(n,w,λ) designs; the converse of the Assmus-Mattson theorem holds at
     weight 4, and the minimal failure of the converse occurs at d^⊥ = 5."

  We formalise the concrete witness that falsifies the first (main) clause: the
  binary [5,2,3] code

      C = {00000, 01101, 10011, 11110}   (coordinate 1 = leftmost entry),

  which has minimum distance d = 3 and dual distance d^⊥ = 2.  Its two
  minimum-weight codewords are

      01101  with support {2,3,5},
      10011  with support {1,4,5}.

  Taking t = 1 we have d^⊥ = 2 >= t+1 = 2, yet the two supports do NOT form a
  1-(5,3,λ) design: coordinate 5 lies in both blocks (multiplicity 2) while
  coordinates 1,2,3,4 lie in exactly one block each (multiplicity 1).

  Hence the implication "d^⊥ >= t+1  =>  minimum-weight codewords form a
  t-design" already fails at (d^⊥, t) = (2,1), and the assertion that the
  minimal failure occurs at d^⊥ = 5 is false.

  Everything is decided computationally: words are `List Bool`, XOR is a
  hand-written Boolean XOR (so the kernel reducer sees it), and `Finset` /
  Mathlib are not used.  There is no `sorry`.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc8419

/-! ## Boolean words and elementary operations -/

/-- Boolean XOR, written without `Bool.xor` so that it reduces definitionally. -/
def xorB (a b : Bool) : Bool := (a && !b) || (!a && b)

/-- Pointwise XOR of two Boolean words (truncated to the shorter list). -/
def xorList : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => xorB a b :: xorList as bs

/-- All Boolean lists of length `n`. -/
def boolListsOfLen : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (boolListsOfLen n).map (fun s => false :: s) ++
      (boolListsOfLen n).map (fun s => true :: s)

/-- All 32 Boolean words of length 5. -/
def allWords5 : List (List Bool) := boolListsOfLen 5

/-- Hamming weight: the number of `true` entries. -/
def weight (w : List Bool) : Nat := (w.filter id).length

/-- Inner product over `F_2`, returned as a `Bool` (the parity). -/
def dotP : List Bool → List Bool → Bool
  | [], _ => false
  | _, [] => false
  | a :: as, b :: bs => xorB (a && b) (dotP as bs)

/-! ## The binary [5,2,3] code C = {00000, 01101, 10011, 11110} -/

/-- First generator, `01101`, with support `{2,3,5}`. -/
def gA : List Bool := [false, true, true, false, true]

/-- Second generator, `10011`, with support `{1,4,5}`. -/
def gB : List Bool := [true, false, false, true, true]

/-- Their sum, `11110`, with support `{1,2,3,4}`. -/
def gAB : List Bool := xorList gA gB

/-- The zero word. -/
def zero5 : List Bool := [false, false, false, false, false]

/-- The code `C`, listed as its four elements. -/
def code : List (List Bool) := [zero5, gA, gB, gAB]

/-- Membership in `C`. -/
def inCode (w : List Bool) : Bool :=
  w == zero5 || w == gA || w == gB || w == gAB

/-- `y` is a codeword of the dual code `C^⊥`. -/
def isDual (y : List Bool) : Bool := code.all (fun c => !(dotP y c))

/-- The nonzero dual words. -/
def dualWords : List (List Bool) :=
  allWords5.filter (fun y => isDual y && (weight y != 0))

/-- The dual distance `d^⊥`: minimum weight of a nonzero dual word. -/
def dualDistance : Nat := (dualWords.map weight).foldl min 100

/-- The minimum distance `d`: minimum nonzero codeword weight. -/
def minWeight : Nat :=
  ((allWords5.filter (fun w => inCode w && (weight w != 0))).map weight).foldl min 100

/-- `w` is a minimum-weight codeword of `C`. -/
def isMinWeightWord (w : List Bool) : Bool :=
  inCode w && (weight w != 0) && (weight w == minWeight)

/-- The list of minimum-weight codewords of `C`. -/
def minWeightWords : List (List Bool) := allWords5.filter isMinWeightWord

/-! ## Supports and the `t`-design predicate -/

/-- The support of a word, as a predicate on the five coordinates. -/
def support5 (w : List Bool) : Fin 5 → Bool := fun i => w.getD i.val false

/-- The blocks of the putative design: supports of minimum-weight codewords. -/
def blocks : List (Fin 5 → Bool) := minWeightWords.map support5

/-- All sublists of a list (the power set, as a list of lists). -/
def powerset {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (powerset xs).map (fun s => x :: s) ++ powerset xs

/-- All `t`-subsets of the five coordinates. -/
def tSubsets (t : Nat) : List (List (Fin 5)) :=
  (powerset (List.finRange 5)).filter (fun s => s.length == t)

/-- Number of blocks containing every coordinate of the subset `s`. -/
def countBlocks (bs : List (Fin 5 → Bool)) (s : List (Fin 5)) : Nat :=
  (bs.filter (fun b => s.all b)).length

/-- The `t`-design predicate: every `t`-subset is contained in the same number
of blocks. -/
def isTDesign (t : Nat) (bs : List (Fin 5 → Bool)) : Bool :=
  match tSubsets t with
  | [] => true
  | s0 :: _ => (tSubsets t).all (fun s => countBlocks bs s == countBlocks bs s0)

/-! ## Verified facts about the code -/

/-- `gA + gB = 11110`. -/
theorem gAB_eq : gAB = [true, true, true, true, false] := by decide

/-- The four listed words are exactly the code: the span is closed and has the
two generators. -/
theorem code_closed : inCode gAB = true ∧ inCode zero5 = true := by decide

/-- The weights of the words of `C`. -/
theorem weights : weight zero5 = 0 ∧ weight gA = 3 ∧ weight gB = 3 ∧ weight gAB = 4 := by
  decide

/-- Minimum distance of `C`. -/
theorem minWeight_eq_three : minWeight = 3 := by decide

/-- There is no codeword of weight 1, 2 or 5: every codeword has weight 0, 3 or 4. -/
theorem no_codeword_of_other_weight :
    allWords5.all (fun w => !(inCode w) || weight w == 0 || weight w == 3 || weight w == 4)
      = true := by
  decide

/-- The two generators are minimum-weight codewords. -/
theorem gA_is_min : isMinWeightWord gA = true := by decide

theorem gB_is_min : isMinWeightWord gB = true := by decide

/-- There are exactly two minimum-weight codewords, and they are `gA` and `gB`. -/
theorem minWeightWords_spec :
    minWeightWords.length = 2 ∧
    minWeightWords.all (fun w => w == gA || w == gB) = true := by
  decide

/-- Dual distance of `C`. -/
theorem dualDistance_eq_two : dualDistance = 2 := by decide

/-- An explicit weight-2 dual word: `01100`, with support `{2,3}`. -/
theorem dual_word_of_weight_two : isDual [false, true, true, false, false] = true := by
  decide

/-- `C^⊥` has no word of weight 1, so `d^⊥ = 2` is established by exhibiting a
weight-2 dual word and ruling out weight 1. -/
theorem no_dual_word_of_weight_one :
    dualWords.all (fun y => weight y != 1) = true := by
  decide

/-- Support of `gA` is `{2,3,5}` (coordinates 1,2,4 in `Fin 5` notation). -/
theorem support_gA : (List.finRange 5).filter (fun i => support5 gA i) = [1, 2, 4] := by
  decide

/-- Support of `gB` is `{1,4,5}` (coordinates 0,3,4 in `Fin 5` notation). -/
theorem support_gB : (List.finRange 5).filter (fun i => support5 gB i) = [0, 3, 4] := by
  decide

/-- The putative design has two blocks (one per minimum-weight codeword). -/
theorem blocks_length : blocks.length = 2 := by decide

/-- Coordinate 5 (index 4) lies in both blocks. -/
theorem multiplicity_five : countBlocks blocks [4] = 2 := by decide

/-- Coordinates 1,2,3,4 (indices 0,1,2,3) lie in exactly one block each. -/
theorem multiplicity_one : countBlocks blocks [0] = 1 := by decide

theorem multiplicity_two : countBlocks blocks [1] = 1 := by decide

theorem multiplicity_three : countBlocks blocks [2] = 1 := by decide

theorem multiplicity_four : countBlocks blocks [3] = 1 := by decide

/-- The supports of the two minimum-weight codewords do NOT form a 1-design. -/
theorem isTDesign_one_false : isTDesign 1 blocks = false := by decide

/-- Negation form: they are not a 1-design. -/
theorem not_one_design : ¬ (isTDesign 1 blocks = true) := by decide

/-- The hypothesis of the conjecture holds for `t = 1`: `d^⊥ = 2 >= t+1 = 2`. -/
theorem hypothesis_holds : dualDistance ≥ 1 + 1 := by decide

/-- The refutation package.  For `t = 1` the conjecture's hypothesis
(`d^⊥ >= t+1`) holds, `d^⊥ = 2`, yet the minimum-weight codewords fail to form a
`1-(5,3,λ)` design: coordinate 5 has multiplicity 2 and the other coordinates
have multiplicity 1.  The file also records `d = 3` and the two supports. -/
theorem conjecture_00000008419_false :
    dualDistance = 2 ∧
    minWeight = 3 ∧
    isTDesign 1 blocks = false ∧
    countBlocks blocks [4] = 2 ∧
    countBlocks blocks [0] = 1 := by
  decide

end Tlmc8419
