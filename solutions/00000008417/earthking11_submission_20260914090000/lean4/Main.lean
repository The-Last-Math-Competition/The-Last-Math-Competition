/-
  Refutation certificate for conjecture `00000008417`, whose false conjunct is

      "the lower bound n_0(5,6) > 12 is given by a concrete divisibility
       obstruction".

  We exhibit a genuine S(5,6,12) — the small Witt design W_12 — as 132 six-element
  blocks on 12 points such that every 5-element subset lies in exactly one block.
  The design exists AT n = 12, and all six classical divisibility conditions hold
  at (t,k,n) = (5,6,12).  Hence any existence threshold satisfies n_0(5,6) ≤ 12,
  contradicting the filed lower bound n_0(5,6) > 12.

  Points are 0..11; a subset is a 12-bit Nat mask (bit i = point i).  Everything
  is core Lean: Nat bitmasks + List.  No Finset, no Mathlib, no `sorry`.
  (`Nat.popcount` and `Nat.digits` are absent from this core, so `popcount` is
  defined by hand over bits 0..11.)
-/

import Std

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Tlmc8417

/-! ## The design -/

/-- Number of set bits among bits 0..11 (all masks used here are < 2^12). -/
def popcount (n : Nat) : Nat :=
  (List.range 12).foldl (fun a i => a + (if Nat.testBit n i then 1 else 0)) 0

/-- The 132 blocks of the small Witt design W_12 = S(5,6,12), as 12-bit masks.
This is exactly the design produced by `reproduce.py` via exact cover (the two
lists are identical). -/
def blocks : List Nat := [
  63,
  207,
  243,
  252,
  343,
  365,
  378,
  414,
  427,
  437,
  473,
  486,
  603,
  622,
  629,
  669,
  679,
  698,
  726,
  745,
  783,
  822,
  825,
  860,
  867,
  915,
  940,
  965,
  970,
  1008,
  1117,
  1131,
  1142,
  1175,
  1198,
  1209,
  1242,
  1253,
  1307,
  1319,
  1340,
  1358,
  1393,
  1421,
  1458,
  1475,
  1492,
  1512,
  1566,
  1581,
  1587,
  1607,
  1656,
  1675,
  1716,
  1740,
  1745,
  1762,
  1813,
  1834,
  1865,
  1874,
  1892,
  1926,
  1944,
  1953,
  2142,
  2151,
  2169,
  2203,
  2221,
  2230,
  2261,
  2282,
  2333,
  2350,
  2355,
  2379,
  2420,
  2439,
  2488,
  2508,
  2514,
  2529,
  2583,
  2603,
  2620,
  2637,
  2674,
  2702,
  2737,
  2755,
  2776,
  2788,
  2842,
  2853,
  2886,
  2897,
  2920,
  2953,
  2964,
  2978,
  3087,
  3125,
  3130,
  3155,
  3180,
  3228,
  3235,
  3270,
  3273,
  3312,
  3350,
  3369,
  3397,
  3416,
  3426,
  3466,
  3473,
  3492,
  3609,
  3622,
  3658,
  3668,
  3681,
  3717,
  3730,
  3752,
  3843,
  3852,
  3888,
  4032
]

/-- All 5-subsets of 12 points, as 12-bit masks with popcount 5. -/
def fives : List Nat := (List.range 4096).filter (fun m => popcount m == 5)

/-- How many of the blocks contain the subset `m`. -/
def covered (m : Nat) : Nat := (blocks.filter (fun b => (m &&& b) == m)).length

/-! ## Structural facts about the witness -/

theorem blocks_all_popcount_six : blocks.all (fun b => popcount b == 6) = true := by
  decide

theorem blocks_nodup : blocks.Nodup := by decide

theorem blocks_length : blocks.length = 132 := by decide

theorem fives_all_popcount_five : fives.all (fun m => popcount m == 5) = true := by
  decide

theorem fives_length : fives.length = 792 := by decide

/-- Total incidences: 132 blocks × 6 points = 792 = number of 5-subsets. -/
theorem total_incidences : blocks.foldl (fun a b => a + popcount b) 0 = 792 := by
  decide

/-- **The existence certificate.** Every one of the 792 five-subsets is contained
in EXACTLY ONE of the 132 blocks: W_12 is a genuine 5-(12,6,1) design. -/
theorem every_five_in_exactly_one_block :
    fives.all (fun m => covered m == 1) = true := by decide

/-- Every five-subset is contained in at least one block (implied by the exact
count, recorded separately as a covering statement). -/
theorem every_five_covered : fives.all (fun m => 1 ≤ covered m) = true := by
  decide

/-! ## The six classical divisibility conditions at (5,6,12)

The i-th condition for an S(t,k,n) is  C(n-i,t-i) / C(k-i,t-i) ∈ Z  for
i = 0,…,t.  At (5,6,12) the six quotients are 132, 66, 30, 12, 4, 1 — every one
an integer, so there is *no* divisibility obstruction at n = 12.  Each condition
is stated as an exact product, leaving no divisibility implicit. -/

theorem div_i0 : 792 = 132 * 6 := by decide
theorem div_i1 : 330 = 66 * 5 := by decide
theorem div_i2 : 120 = 30 * 4 := by decide
theorem div_i3 : 36 = 12 * 3 := by decide
theorem div_i4 : 8 = 4 * 2 := by decide
theorem div_i5 : 1 = 1 * 1 := by decide

/-- All six divisibility conditions hold simultaneously at (5,6,12). -/
theorem divisibility_conditions_hold :
    (792 = 132 * 6) ∧ (330 = 66 * 5) ∧ (120 = 30 * 4) ∧
      (36 = 12 * 3) ∧ (8 = 4 * 2) ∧ (1 = 1 * 1) := by
  decide

/-! ## Prop-level packaging of the refutation -/

/-- `B` is a 5-(12,6,1) design: 132 distinct blocks of size 6, every 5-subset in
exactly one of them. -/
def IsDesign5612 (B : List Nat) : Prop :=
  B.Nodup ∧
    B.length = 132 ∧
    B.all (fun b => popcount b == 6) = true ∧
    fives.all (fun m => (B.filter (fun b => (m &&& b) == m)).length == 1) = true

/-- The explicit blocks form a 5-(12,6,1) design. -/
theorem witt_is_design : IsDesign5612 blocks :=
  ⟨blocks_nodup, blocks_length, blocks_all_popcount_six,
    every_five_in_exactly_one_block⟩

/-- **The refutation.** A 5-(12,6,1) design exists.  Therefore any existence
threshold satisfies `n_0(5,6) ≤ 12`, which contradicts the filed lower bound
`n_0(5,6) > 12`. -/
theorem exists_S5612 : ∃ B : List Nat, IsDesign5612 B :=
  ⟨blocks, witt_is_design⟩

/-- The design exists while all six divisibility conditions hold, so existence at
`n = 12` is not obstructed by divisibility. -/
theorem exists_and_divisible :
    (∃ B : List Nat, IsDesign5612 B) ∧ (792 = 132 * 6) :=
  ⟨exists_S5612, div_i0⟩

end Tlmc8417
