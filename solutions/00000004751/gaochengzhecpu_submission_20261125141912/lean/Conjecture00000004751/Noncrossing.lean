/-
Copyright (c) 2026. All rights reserved.
 Formalization of Conjecture 00000004751:
 Module 1: Set Partitions, Noncrossing Lattice NC(n), Kreweras Complement,
 and Poset Möbius Inversion from First Principles in Core Lean 4.19.0.
-/

set_option maxRecDepth 200000

namespace Conjecture00000004751

/-- A block of a partition of `{0, ..., n-1}`, represented in canonical strictly increasing order. -/
abbrev Block := List Nat

/-- A set partition, represented as blocks sorted in strictly increasing order of minimum element. -/
abbrev Partition := List Block

/-- Checks whether a list of natural numbers is strictly increasing. -/
def isStrictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => (x < y) && isStrictlyIncreasing (y :: rest)

/-- Head of a non-empty block, or `0` for `[]`. -/
def blockHead : Block → Nat
  | [] => 0
  | x :: _ => x

/-- Checks whether block heads are strictly increasing. -/
def headsStrictlyIncreasing : Partition → Bool
  | [] => true
  | [_] => true
  | b1 :: b2 :: rest => (blockHead b1 < blockHead b2) && headsStrictlyIncreasing (b2 :: rest)

/-- Counts how many blocks contain element `x`. -/
def countOccurrences (x : Nat) (pi : Partition) : Nat :=
  pi.foldl (fun acc b => acc + (b.filter (fun y => y == x)).length) 0

/-- First-principles validity predicate for a canonical set partition of `{0, ..., n-1}`:
    every block is non-empty and strictly increasing, block minimums are strictly increasing,
    total size equals `n`, and every `i < n` occurs exactly once. -/
def isValidPartition (n : Nat) (pi : Partition) : Bool :=
  pi.all (fun b => !b.isEmpty && isStrictlyIncreasing b) &&
  headsStrictlyIncreasing pi &&
  (pi.foldl (fun acc b => acc + b.length) 0 == n) &&
  (List.range n).all (fun i => countOccurrences i pi == 1)

/-- Checks whether two blocks `b1` and `b2` have an alternating quadruple `a < b < c < d`
    with `a, c ∈ b1` and `b, d ∈ b2`. -/
def hasAlternatingQuad (b1 b2 : Block) : Bool :=
  b1.any (fun a =>
    b2.any (fun b =>
      (a < b) && b1.any (fun c =>
        (b < c) && b2.any (fun d => c < d))))

/-- Two blocks cross iff they alternate in either orientation. -/
def blocksCross (b1 b2 : Block) : Bool :=
  hasAlternatingQuad b1 b2 || hasAlternatingQuad b2 b1

/-- Checks pairwise noncrossing among all blocks in a partition. -/
def isNoncrossing : Partition → Bool
  | [] => true
  | b :: rest => rest.all (fun b' => !blocksCross b b') && isNoncrossing rest

/-- Full membership predicate in `NC(n)`. -/
def isNC (n : Nat) (pi : Partition) : Bool :=
  isValidPartition n pi && isNoncrossing pi

/-- Appends a new largest element `x` into an existing canonical partition in all ways:
    either as a new singleton block `[x]` at the end, or appended to one existing block. -/
def extendPartitionWith (x : Nat) : Partition → List Partition
  | [] => [[[x]]]
  | b :: rest =>
      ((b ++ [x]) :: rest) :: (extendPartitionWith x rest).map (fun p => b :: p)

/-- Generates all canonical set partitions of `{0, ..., n-1}`. -/
def allSetPartitions : Nat → List Partition
  | 0 => [[]]
  | n + 1 =>
      (allSetPartitions n).foldr (fun pi acc => extendPartitionWith n pi ++ acc) []

/-- Generates all canonical noncrossing partitions `NC(n)` of `{0, ..., n-1}`,
    pruning crossings incrementally at each step. -/
def allNC : Nat → List Partition
  | 0 => [[]]
  | n + 1 =>
      (allNC n).foldr
        (fun pi acc => (extendPartitionWith n pi).filter isNoncrossing ++ acc) []

/-- Incremental `allNC` agrees identically with filtering `allSetPartitions` at `n = 4` and `n = 6`. -/
theorem allNC_eq_filtered_setPartitions_4 :
    allNC 4 = (allSetPartitions 4).filter isNoncrossing := by decide

theorem allNC_eq_filtered_setPartitions_6 :
    allNC 6 = (allSetPartitions 6).filter isNoncrossing := by decide

/-- Dot product of two lists of natural numbers. -/
def dotProdNat : List Nat → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + dotProdNat xs ys

/-- Prefix table `[C_0, C_1, ..., C_n]` of Catalan numbers by pure structural recursion
    via Segner's convolution `C_{n+1} = ∑_{i=0}^n C_i C_{n-i}`. -/
def catalanPrefix : Nat → List Nat
  | 0 => [1]
  | n + 1 =>
      let prev := catalanPrefix n
      prev ++ [dotProdNat prev prev.reverse]

/-- Catalan numbers `C_n`, structurally recursive and kernel-reducible in `O(n^2)` steps. -/
def catalan (n : Nat) : Nat :=
  (catalanPrefix n).getLastD 1

theorem allNC_card_1 : (allNC 1).length = catalan 1 := rfl
theorem allNC_card_2 : (allNC 2).length = catalan 2 := rfl
theorem allNC_card_3 : (allNC 3).length = catalan 3 := rfl
theorem allNC_card_4 : (allNC 4).length = catalan 4 := rfl
theorem allNC_card_5 : (allNC 5).length = catalan 5 := rfl
theorem allNC_card_6 : (allNC 6).length = catalan 6 := rfl

/-- Refinement order `pi ≤ sigma`: every block of `pi` is contained in some block of `sigma`. -/
def subsetBlock (b1 b2 : Block) : Bool :=
  b1.all (fun x => b2.contains x)

def refines (pi sigma : Partition) : Bool :=
  pi.all (fun b1 => sigma.any (fun b2 => subsetBlock b1 b2))

/-- Insertion into a non-increasing list of natural numbers. -/
def insertDesc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≥ y then x :: y :: ys else y :: insertDesc x ys

/-- Block structure (integer partition of block sizes in non-increasing order) of `pi`. -/
def blockType (pi : Partition) : List Nat :=
  pi.foldl (fun acc b => insertDesc b.length acc) []

/-- Top partition `1_n = {{0, 1, ..., n-1}}` for `n ≥ 1`. -/
def topPartition (n : Nat) : Partition :=
  if n == 0 then [] else [List.range n]

/-- Bottom partition `0_n = {{0}, {1}, ..., {n-1}}`. -/
def botPartition (n : Nat) : Partition :=
  (List.range n).map (fun i => [i])

/-- Insertion of a partition into a list ordered by descending number of blocks
    (which is topological refinement order from smaller to larger elements in `NC(n)`). -/
def insertByBlocksDesc (p : Partition) : List Partition → List Partition
  | [] => [p]
  | q :: qs => if p.length ≥ q.length then p :: q :: qs else q :: insertByBlocksDesc p qs

def sortByBlocksDesc (ps : List Partition) : List Partition :=
  ps.foldl (fun acc p => insertByBlocksDesc p acc) []

/-- Upper interval `[pi, 1_n] = {tau ∈ NC(n) | pi ≤ tau}` sorted in refinement order. -/
def upperInterval (n : Nat) (pi : Partition) : List Partition :=
  sortByBlocksDesc ((allNC n).filter (fun tau => refines pi tau))

/-- Computes `mu(pi, sigma)` for all `sigma ∈ interval` directly from the defining
    incidence-algebra recursion `mu(pi, pi) = 1` and `∑_{pi ≤ tau ≤ sigma} mu(pi, tau) = 0`. -/
def mobiusRowFromInterval (pi : Partition) (interval : List Partition) : List (Partition × Int) :=
  interval.foldl
    (fun acc sigma =>
      let val : Int :=
        if sigma == pi then 1
        else
          - (acc.foldl (fun s pair =>
              if refines pair.1 sigma then s + pair.2 else s) 0)
      acc ++ [(sigma, val)])
    []

/-- Lookup in an association list `(Partition × Int)`. -/
def lookupVal (sigma : Partition) : List (Partition × Int) → Int
  | [] => 0
  | (p, v) :: rest => if p == sigma then v else lookupVal sigma rest

/-- Poset Möbius function `mu_{NC(n)}(pi, sigma)` computed from the upper interval of `pi`. -/
def mobiusNC (n : Nat) (pi sigma : Partition) : Int :=
  lookupVal sigma (mobiusRowFromInterval pi (upperInterval n pi))

/-- Independent verification predicate checking that `row` satisfies the defining poset
    Möbius equations `mu(pi, pi) = 1` and `∑_{pi ≤ tau ≤ sigma} mu(pi, tau) = 0` (`sigma ≠ pi`)
    at every element `sigma` of `interval`. -/
def checkMobiusRow (pi : Partition) (interval : List Partition) (row : List (Partition × Int)) : Bool :=
  (lookupVal pi row == 1) &&
  interval.all (fun sigma =>
    if sigma == pi then true
    else
      let sumInterval :=
        interval.foldl
          (fun s tau =>
            if refines pi tau && refines tau sigma then s + lookupVal tau row else s) 0
      sumInterval == 0)

/-- Every upper-interval Möbius row in `NC(4)` satisfies the exact poset Möbius equations. -/
theorem allNC4_mobius_equations_hold :
    (allNC 4).all (fun pi =>
      let iv := upperInterval 4 pi
      checkMobiusRow pi iv (mobiusRowFromInterval pi iv)) = true := by decide

/-- Kreweras complement `K(pi)` on `{0, ..., n-1}` defined via the inverse block-cycle action
    `i ↦ P_pi^{-1}((i + 1) mod n)`. -/
def prevInBlock (x : Nat) (b : Block) : Option Nat :=
  let rec findIdx (xs : List Nat) (idx : Nat) : Option Nat :=
    match xs with
    | [] => none
    | y :: ys => if y == x then some idx else findIdx ys (idx + 1)
  match findIdx b 0 with
  | none => none
  | some 0 => b.getLast?
  | some (k + 1) => b[k]?

def permPiInv (pi : Partition) (x : Nat) : Nat :=
  let rec go : Partition → Nat
    | [] => x
    | b :: bs =>
        match prevInBlock x b with
        | some v => v
        | none => go bs
  go pi

def krewerasStep (n : Nat) (pi : Partition) (i : Nat) : Nat :=
  if n == 0 then 0 else permPiInv pi ((i + 1) % n)

def insertNatAsc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x == y then y :: ys else if x < y then x :: y :: ys else y :: insertNatAsc x ys

def insertBlockAsc (b : Block) : Partition → Partition
  | [] => [b]
  | c :: cs => if blockHead b < blockHead c then b :: c :: cs else c :: insertBlockAsc b cs

def traceCycle (n : Nat) (pi : Partition) (start : Nat) : Block :=
  let rec loop (cur fuel : Nat) (acc : Block) : Block :=
    match fuel with
    | 0 => acc
    | f + 1 =>
        let acc' := insertNatAsc cur acc
        let nxt := krewerasStep n pi cur
        if nxt == start then acc' else loop nxt f acc'
  loop start n []

/-- Canonical Kreweras complement `K(pi) ∈ NC(n)`. -/
def kreweras (n : Nat) (pi : Partition) : Partition :=
  (List.range n).foldl
    (fun blocks i =>
      if blocks.any (fun b => b.contains i) then blocks
      else insertBlockAsc (traceCycle n pi i) blocks)
    []

/-- Signed Catalan product formula `∏_{W ∈ pi} (-1)^{|W|-1} C_{|W|-1}` for `mu_{NC}(0_n, pi)`. -/
def signedCatalanBlock (len : Nat) : Int :=
  if len == 0 then 1
  else
    let k := len - 1
    let sign : Int := if k % 2 == 0 then 1 else -1
    sign * Int.ofNat (catalan k)

def mobiusFromZeroFormula (pi : Partition) : Int :=
  pi.foldl (fun prod b => prod * signedCatalanBlock b.length) 1

/-- Nica–Speicher Kreweras formula for upper-interval Möbius inversion `mu_{NC}(pi, 1_n)`. -/
def mobiusToTopFormula (n : Nat) (pi : Partition) : Int :=
  mobiusFromZeroFormula (kreweras n pi)

/-- Exact verification that `kreweras` maps `NC(4)` into `NC(4)`, satisfies `|pi| + |K(pi)| = 5`,
    and matches poset Möbius inversion `mobiusNC 4 pi (topPartition 4)` for all 14 elements. -/
theorem kreweras_and_mobius_NC4_verified :
    (allNC 4).all (fun pi =>
      let kp := kreweras 4 pi
      isNC 4 kp &&
      (pi.length + kp.length == 5) &&
      (mobiusNC 4 pi (topPartition 4) == mobiusToTopFormula 4 pi)) = true := by decide

/-- Exact verification on `NC(6)` (all 132 elements) that `K(pi) ∈ NC(6)` and `|pi| + |K(pi)| = 7`. -/
theorem kreweras_NC6_verified :
    (allNC 6).all (fun pi =>
      let kp := kreweras 6 pi
      isNC 6 kp && (pi.length + kp.length == 7)) = true := by decide

/-! ### Explicit Counterexample Partitions in `NC(4)` and `NC(6)` -/

/-- Adjacent pair partition `{{0,1}, {2}, {3}} ∈ NC(4)` of block structure `[2, 1, 1]`. -/
def pi4_adj : Partition := [[0, 1], [2], [3]]

/-- Nested/straddling pair partition `{{0,2}, {1}, {3}} ∈ NC(4)` of block structure `[2, 1, 1]`. -/
def pi4_nest : Partition := [[0, 2], [1], [3]]

/-- Flat pair partition `{{0,1}, {2,3}, {4,5}} ∈ NC(6)` of uniform block structure `[2, 2, 2]`. -/
def pi6_flat : Partition := [[0, 1], [2, 3], [4, 5]]

/-- Nested rainbow pair partition `{{0,5}, {1,4}, {2,3}} ∈ NC(6)` of uniform block structure `[2, 2, 2]`. -/
def pi6_rain : Partition := [[0, 5], [1, 4], [2, 3]]

theorem pi4_counterexamples_valid_and_same_type :
    isNC 4 pi4_adj = true ∧
    isNC 4 pi4_nest = true ∧
    blockType pi4_adj = [2, 1, 1] ∧
    blockType pi4_nest = [2, 1, 1] := by decide

theorem pi4_mobius_disagree :
    mobiusNC 4 pi4_adj (topPartition 4) = 2 ∧
    mobiusNC 4 pi4_nest (topPartition 4) = 1 ∧
    blockType (kreweras 4 pi4_adj) = [3, 1] ∧
    blockType (kreweras 4 pi4_nest) = [2, 2] := by decide

theorem pi6_counterexamples_valid_and_mobius_checked :
    isNC 6 pi6_flat = true ∧
    isNC 6 pi6_rain = true ∧
    blockType pi6_flat = [2, 2, 2] ∧
    blockType pi6_rain = [2, 2, 2] ∧
    checkMobiusRow pi6_flat (upperInterval 6 pi6_flat)
      (mobiusRowFromInterval pi6_flat (upperInterval 6 pi6_flat)) = true ∧
    checkMobiusRow pi6_rain (upperInterval 6 pi6_rain)
      (mobiusRowFromInterval pi6_rain (upperInterval 6 pi6_rain)) = true := by decide

theorem pi6_mobius_and_kreweras_disagree :
    mobiusNC 6 pi6_flat (topPartition 6) = 2 ∧
    mobiusNC 6 pi6_rain (topPartition 6) = 1 ∧
    mobiusToTopFormula 6 pi6_flat = 2 ∧
    mobiusToTopFormula 6 pi6_rain = 1 ∧
    blockType (kreweras 6 pi6_flat) = [3, 1, 1, 1] ∧
    blockType (kreweras 6 pi6_rain) = [2, 2, 1, 1] := by decide

end Conjecture00000004751
