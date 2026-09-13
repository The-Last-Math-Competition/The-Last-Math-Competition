/-
  Disproof of conjecture `00000000418`.

  Conjecture (as filed):

    Definition: A Yamanouchi (lattice) word of weight λ is a word in which, in
    every prefix, the occurrence counts of each letter form a partition; a
    lattice word is one appearing as the reading word of a standard tableau.
    Conjecture: The proportion of lattice words of weight λ among Yamanouchi
    words is exactly f^λ/n! · K^{-1}_{λ,λ}, and this ratio attains its maximum
    1/2^{n−1} when λ is a rectangle.

  This file refutes the conjecture at `λ = (2,1)`, `n = 3`, under BOTH readings
  of "lattice word" that the conjecture itself supplies:

    (A) Reading (A), the conjecture's own synonym: "Yamanouchi (lattice)" makes
        the two terms identical, so the set of lattice words of weight (2,1) IS
        the set of Yamanouchi words of weight (2,1).  There are `2` of them
        (`112` and `121`; `211` fails the prefix condition), so the proportion
        is `2/2 = 1`.  The conjectured value is
        `f^(2,1) / (3! · K_(2,1),(2,1)) = 2 / (6 · 1) = 2/6`.
        Cross-multiplying, `2/2 = 2/6` would force `2·6 = 2·2`, i.e. `12 = 4`,
        which is false.  Moreover `2/2 = 1` exceeds the asserted maximum
        `1/2^{3-1} = 1/4`.

    (B) Reading (B), "reading word of a standard tableau": the entry reading of
        a standard tableau is a permutation of `{1,2,3}`, hence has weight
        `(1,1,1) ≠ (2,1)`.  So there are `0` lattice words of weight `(2,1)` and
        the proportion is `0/2 = 0 ≠ 2/6`.

  Core Lean only (`import Std`); no Mathlib, no `Finset`, no `Nat.factorial`,
  no `List.permutations`, no `sorry`.  All numerical facts are closed by
  `decide`.  Rational comparisons are done by cross-multiplication in `Nat`,
  never by `Rat` (whose operations `decide` cannot reduce).
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc418

/-! ## Basic counting helpers -/

/-- Number of occurrences of `t` in `l`. -/
def countOcc (l : List Nat) (t : Nat) : Nat :=
  (l.filter (fun x => x == t)).length

/-- Factorial, defined locally: `Nat.factorial` is not available in `import Std`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- All words of length `n` over the alphabet `{1, …, k}`, enumerated by nested
`List.range` maps. -/
def allWords (k : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (allWords k n).flatMap (fun w => (List.range k).map (fun a => w ++ [a + 1]))

/-- All `2^3 = 8` words of length `3` over the alphabet `{1,2}`. -/
def allWords3 : List (List Nat) := allWords 2 3

theorem allWords3_length : allWords3.length = 8 := by decide

/-! ## Reading (A): Yamanouchi words of weight `(2,1)` -/

/-- Yamanouchi predicate (weight is irrelevant): in every prefix the counts of
`1` and `2` are non-increasing, i.e. form a partition.  For the two-letter
alphabet this is exactly `#{1} ≥ #{2}` in every prefix. -/
def isYam (w : List Nat) : Bool :=
  (List.range (w.length + 1)).all
    (fun m => decide (countOcc (w.take m) 1 ≥ countOcc (w.take m) 2))

/-- Weight `(2,1)`: two `1`s and one `2`. -/
def hasWeight21 (w : List Nat) : Bool :=
  decide (countOcc w 1 = 2 ∧ countOcc w 2 = 1)

/-- The Yamanouchi words of weight `(2,1)`. -/
def yamWords21 : List (List Nat) :=
  allWords3.filter (fun w => isYam w && hasWeight21 w)

theorem word_112_isYam : isYam [1,1,2] = true := by decide
theorem word_121_isYam : isYam [1,2,1] = true := by decide
theorem word_211_not_yam : isYam [2,1,1] = false := by decide

/-- Exactly two Yamanouchi words of weight `(2,1)` exist, namely `112` and
`121`; the third word of that weight, `211`, fails already at its first
(non-empty) prefix. -/
theorem yamWords21_eq : yamWords21 = [[1,1,2],[1,2,1]] := by decide

theorem card_yamWords21 : yamWords21.length = 2 := by decide

/-- The number of Yamanouchi words of weight `(2,1)`. -/
def numYam21 : Nat := yamWords21.length

theorem numYam21_eq : numYam21 = 2 := by decide

/-! ## Standard tableaux of shape `(2,1)` and their reading words -/

/-- First standard Young tableau of shape `(2,1)`, as two rows. -/
def syt21a : List (List Nat) := [[1,2],[3]]

/-- Second standard Young tableau of shape `(2,1)`, as two rows. -/
def syt21b : List (List Nat) := [[1,3],[2]]

/-- The two standard Young tableaux of shape `(2,1)`. -/
def syts21 : List (List (List Nat)) := [syt21a, syt21b]

theorem card_syts21 : syts21.length = 2 := by decide

/-- Row index (1-based) of the cell containing `e`, or `0` if `e` is absent.
This is the standard bijection *standard tableaux of shape λ ↔ lattice
(Yamanouchi) words of weight λ*: the word `(row of 1, row of 2, …, row of n)`
is a Yamanouchi word of weight λ. -/
def rowOf (T : List (List Nat)) (e : Nat) : Nat :=
  (((List.range T.length).filter (fun i => (T.getD i []).contains e)).map
    (fun i => i + 1)).getD 0 0

/-- The lattice (Yamanouchi) reading word of a standard tableau: the sequence
of 1-based row indices of the cells containing `1, 2, 3`. -/
def latticeReading (T : List (List Nat)) : List Nat :=
  (List.range 3).map (fun e => rowOf T (e + 1))

theorem latticeReading_syt21a : latticeReading syt21a = [1,1,2] := by decide
theorem latticeReading_syt21b : latticeReading syt21b = [1,2,1] := by decide

/-- The lattice reading words of the standard tableaux of shape `(2,1)` are
exactly `112` and `121`. -/
def latticeReadings21 : List (List Nat) := syts21.map latticeReading

theorem latticeReadings21_eq : latticeReadings21 = [[1,1,2],[1,2,1]] := by decide

/-- Every Yamanouchi word of weight `(2,1)` is the lattice reading word of a
standard tableau of shape `(2,1)`: the two notions agree.  Hence, under reading
(A), the number of lattice words of weight `(2,1)` is `2`. -/
theorem yam_eq_latticeReadings : yamWords21 = latticeReadings21 := by decide

theorem every_yam_is_latticeReading :
    ∀ w, w ∈ yamWords21 → w ∈ latticeReadings21 := by
  intro w hw
  rw [yam_eq_latticeReadings] at hw
  exact hw

/-- Number of lattice words of weight `(2,1)` under reading (A), where
"lattice" is the conjecture's own synonym for "Yamanouchi". -/
def numLattice21_A : Nat := numYam21

theorem numLattice21_A_eq : numLattice21_A = 2 := by decide

/-! ## Reading (B): entry reading words of standard tableaux -/

/-- Entry reading word of a tableau: rows read bottom to top, each row left to
right.  Under reading (B) — "a lattice word is one appearing as the reading
word of a standard tableau" — this is the word at issue. -/
def entryReading (T : List (List Nat)) : List Nat := T.reverse.flatMap (fun row => row)

theorem entryReading_syt21a : entryReading syt21a = [3,1,2] := by decide
theorem entryReading_syt21b : entryReading syt21b = [2,1,3] := by decide

/-- Every entry reading word is a permutation: each of `1,2,3` occurs exactly
once, so its weight is `(1,1,1)` and never `(2,1)`. -/
theorem entryReading_weight_111 :
    (countOcc (entryReading syt21a) 1 = 1 ∧
      countOcc (entryReading syt21a) 2 = 1 ∧
      countOcc (entryReading syt21a) 3 = 1) ∧
    (countOcc (entryReading syt21b) 1 = 1 ∧
      countOcc (entryReading syt21b) 2 = 1 ∧
      countOcc (entryReading syt21b) 3 = 1) := by decide

/-- Number of lattice words of weight `(2,1)` under reading (B): none, because
every entry reading word has weight `(1,1,1)`. -/
def numLattice21_B : Nat :=
  ((syts21.map entryReading).filter (fun w => hasWeight21 w)).length

theorem numLattice21_B_eq : numLattice21_B = 0 := by decide

/-! ## Hook lengths, `f^(2,1)`, `n!`, `K_(2,1),(2,1)` -/

/-- Hook lengths of the three cells of `(2,1)`, read row by row: `3, 1, 1`. -/
def hookLengths21 : List Nat := [3,1,1]

/-- Product of the hook lengths of `(2,1)`: `3 · 1 · 1 = 3`. -/
def hookProduct21 : Nat := 3 * 1 * 1

theorem hookProduct21_eq : hookProduct21 = 3 := by decide

/-- Hook-length formula: `f^(2,1) = 3! / (3·1·1) = 6/3 = 2`. -/
def f21 : Nat := fact 3 / hookProduct21

theorem fact3_eq : fact 3 = 6 := by decide
theorem f21_eq : f21 = 2 := by decide

/-- The hook-length count `f^(2,1) = 2` agrees with the number of standard
tableaux of shape `(2,1)`. -/
theorem f21_eq_card_syts21 : f21 = syts21.length := by decide

/-- The three cells of shape `(2,1)` in row-major order `(0,0),(0,1),(1,0)`,
filled with entries from `{1,2}`.  Reuses `allWords`, which enumerates exactly
all `2^3 = 8` such fillings. -/
def allFillings21 : List (List Nat) := allWords 2 3

/-- `t` is a semistandard Young tableau of shape `(2,1)` and content `(2,1)`.
Row condition `(0,0) ≤ (0,1)`; column condition `(0,0) < (1,0)`; content two
`1`s and one `2`. -/
def isSSYT21_21 (t : List Nat) : Bool :=
  match t with
  | [a, b, c] => decide (a ≤ b ∧ a < c ∧ countOcc t 1 = 2 ∧ countOcc t 2 = 1)
  | _ => false

/-- The semistandard tableaux of shape and content `(2,1)`. -/
def ssyt21_21 : List (List Nat) := allFillings21.filter isSSYT21_21

theorem ssyt21_21_eq : ssyt21_21 = [[1,1,2]] := by decide

/-- `K_(2,1),(2,1) = 1`: the unique semistandard tableau of shape and content
`(2,1)` is the superstandard one.  This is the special case of the general
identity `K_{λ,λ} = 1`. -/
def K21 : Nat := ssyt21_21.length

theorem K21_eq : K21 = 1 := by decide

/-! ## The numeric contradiction

The conjectured proportion is `f^λ/(n!·K_{λ,λ})`; at `λ = (2,1)` this has
numerator `f21 = 2` and denominator `fact 3 * K21 = 6 * 1 = 6`.  The actual
proportions are `propNumA/propDenA` (reading (A)) and `propNumB/propDenB`
(reading (B)).  Fractions are compared by cross-multiplication in `Nat`. -/

/-- Numerator of the conjectured value at `λ = (2,1)`: `f^(2,1) = 2`. -/
def claimNum : Nat := f21

/-- Denominator of the conjectured value at `λ = (2,1)`: `n! · K_{λ,λ} = 6 · 1 = 6`. -/
def claimDen : Nat := fact 3 * K21

/-- Numerator of the actual proportion under reading (A): `2`. -/
def propNumA : Nat := numLattice21_A

/-- Denominator of the actual proportion under reading (A): `2`. -/
def propDenA : Nat := numYam21

/-- Numerator of the actual proportion under reading (B): `0`. -/
def propNumB : Nat := numLattice21_B

/-- Denominator of the actual proportion under reading (B): `2`. -/
def propDenB : Nat := numYam21

theorem claimNum_eq : claimNum = 2 := by decide
theorem claimDen_eq : claimDen = 6 := by decide
theorem propNumA_eq : propNumA = 2 := by decide
theorem propDenA_eq : propDenA = 2 := by decide
theorem propNumB_eq : propNumB = 0 := by decide
theorem propDenB_eq : propDenB = 2 := by decide

/-- Reading (A): the proportion `2/2` equals `1` (numerator equals denominator). -/
theorem proportionA_is_one : propNumA = propDenA := by decide

/-- The conjectured value `2/6` is not equal to `1`: `2 ≠ 6`. -/
theorem claim_not_one : claimNum ≠ claimDen := by decide

/-- **The contradiction (reading A).**  The proportion `2/2` differs from the
conjectured `2/6`: cross-multiplying, `2·6 ≠ 2·2`, i.e. `12 ≠ 4`. -/
theorem proportionA_ne_claim : propNumA * claimDen ≠ claimNum * propDenA := by decide

/-- The two cross products of reading (A): `2·6 = 12` and `2·2 = 4`. -/
theorem cross_values : propNumA * claimDen = 12 ∧ claimNum * propDenA = 4 := by decide

/-- `12 ≠ 4`, the cross-multiplied form of the reading-(A) contradiction. -/
theorem twelve_ne_four : (12 : Nat) ≠ 4 := by decide

/-- **The contradiction (reading B).**  The proportion `0/2` differs from the
conjectured `2/6`: cross-multiplying, `0·6 ≠ 2·2`, i.e. `0 ≠ 4`. -/
theorem proportionB_ne_claim : propNumB * claimDen ≠ claimNum * propDenB := by decide

/-! ## The asserted maximum `1/2^{n-1}` -/

/-- `1/4 < 1`, cross-multiplied: `1·1 < 4·1`, i.e. `1 < 4`. -/
theorem quarter_lt_one : (1 : Nat) * 1 < 4 * 1 := by decide

/-- At `n = 3` the asserted maximum is `1/2^{n-1} = 1/4`.  But the proportion
under reading (A) is `2/2`, which exceeds it: cross-multiplying,
`2·4 > 1·2`, i.e. `8 > 2`. -/
theorem proportionA_exceeds_max : propNumA * 4 > 1 * propDenA := by decide

/-! ## The "maximisers are rectangles" clause also fails -/

/-- `f^(3) = 1` (shape `(3)` is a rectangle of size `3`). -/
def f3 : Nat := 1

/-- `f^(1,1,1) = 1` (shape `(1,1,1)` is a rectangle of size `3`). -/
def f111 : Nat := 1

theorem f3_eq : f3 = 1 := by decide
theorem f111_eq : f111 = 1 := by decide

/-- At `n = 3` the maximum of `f^λ/n!` is attained at the non-rectangle
`(2,1)`: `f^(2,1)/3! = 2/6` exceeds the rectangle value `1/6` of `(3)` and
`(1,1,1)`.  Cross-multiplied: `2·6 > 1·6`, i.e. `12 > 6`. -/
theorem nonrectangle_beats_rectangles : f21 * 6 > f3 * 6 := by decide

/-- The rectangle value `1/6` is not the asserted maximum `1/4`
(`1·4 ≠ 1·6`, i.e. `4 ≠ 6`), so the maximum is not attained at a rectangle. -/
theorem rectangle_not_max : f3 * 4 ≠ 1 * 6 := by decide

/-- The asserted maximum `1/4` is not even the maximum of the conjectured
formula: `f^(2,1)/3! = 2/6` exceeds it, `2·4 > 1·6`, i.e. `8 > 6`. -/
theorem max_claim_wrong_for_formula : f21 * 4 > 1 * 6 := by decide

/-! ## The collected refutation -/

/-- Conjecture `00000000418` is FALSE at `λ = (2,1)`, `n = 3`, under both of
the readings of "lattice word" that the conjecture supplies. -/
theorem conjecture_00000000418_refuted :
    numYam21 = 2 ∧
    numLattice21_A = 2 ∧
    propNumA * claimDen ≠ claimNum * propDenA ∧
    numLattice21_B = 0 ∧
    propNumB * claimDen ≠ claimNum * propDenB ∧
    (1 : Nat) * 1 < 4 * 1 ∧
    propNumA * 4 > 1 * propDenA :=
  ⟨numYam21_eq, numLattice21_A_eq, proportionA_ne_claim,
    numLattice21_B_eq, proportionB_ne_claim, quarter_lt_one,
    proportionA_exceeds_max⟩

end Tlmc418
