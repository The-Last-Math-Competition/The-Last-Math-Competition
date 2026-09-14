/-
  Disproof of conjecture `00000008434`.

  Conjecture (as filed):
    Definition: The intersection structure of a combinatorial geometry: the
    intersection spectrum of its blocks.
    Conjecture: The intersection spectrum is exactly the set of all integer
    values in the interval [s₀, s₁]; and s₀ = s₁ if and only if the design is
    symmetric.

  The first clause is FALSE.  Witness: AG(3,2), the unique 3-(8,4,1) Steiner
  quadruple system.  Its 14 affine planes, as 8-bit point masks, are
  [15,51,60,85,90,102,105,150,153,165,170,195,204,240].  Every one of the
  C(8,3) = 56 triples lies in exactly one block, so it is a genuine 3-(8,4,1)
  design.  Over the C(14,2) = 91 pairs of distinct blocks the intersection
  sizes are only 0 (7 times) and 2 (84 times), so the spectrum is {0,2}; but
  the interval [s₀,s₁] = [0,2] also contains 1, which never occurs.  Hence the
  spectrum is strictly smaller than the interval it is conjectured to fill.

  The second clause fails for 1-designs: the Pasch configuration is a
  1-(6,3,2) design in which every two blocks meet in exactly one point
  (s₀ = s₁ = 1), yet b = 4 ≠ 6 = v, so it is not symmetric.

  Core Lean only (`import Std`), no Mathlib, no `sorry`.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc8434

/-! ## Blocks as 8-bit masks -/

/-- Population count on 8-bit masks.  (`Nat.popcount` is not available in
`import Std`, so we define it by a structural fold over bits `0..8`.) -/
def pc (m : Nat) : Nat :=
  (List.range 9).foldl (fun a i => if m.testBit i then a + 1 else a) 0

/-- The 14 affine 2-planes of `F₂³`, as 8-bit point masks of the 8 points
`0,…,7` (point `i` ↔ bit `i`):
`B_{a,b} = {x ∈ F₂³ : a·x = b}` for `a ≠ 0` and `b ∈ {0,1}`. -/
def blocks : List Nat :=
  [15, 51, 60, 85, 90, 102, 105, 150, 153, 165, 170, 195, 204, 240]

/-- The intersection spectrum.  For a block `b`, collect the intersection
sizes `pc (b &&& c)` against all *later* blocks `c`, then recurse.  The
recursion is structural on the list, so it reduces in the kernel (a
well-founded definition would not). -/
def spec : List Nat → List Nat
  | [] => []
  | b :: bs => (bs.map (fun c => pc (b &&& c))) ++ spec bs

/-- `s₀`, the minimum of the spectrum.  `pc ≤ 8`, so seeding with `1000` is
safe. -/
def s0 : Nat := (spec blocks).foldl Nat.min 1000

/-- `s₁`, the maximum of the spectrum. -/
def s1 : Nat := (spec blocks).foldl Nat.max 0

/-- `true` iff the integer `i` occurs as the intersection size of some pair of
distinct blocks. -/
def inSpectrum (i : Nat) : Bool := (spec blocks).any (fun s => s == i)

/-- Clause 1 of the conjecture: the spectrum contains every integer value in
the interval `[s₀, s₁]`. -/
def IntervalSpectrum : Prop := ∀ i : Nat, s0 ≤ i → i ≤ s1 → inSpectrum i = true

/-- Boolean form of clause 1, evaluated over `i = s₀, s₀+1, …, s₁`. -/
def intervalFull : Bool :=
  (List.range (s1 - s0 + 1)).all (fun i => inSpectrum (s0 + i))

/-! ## The 3-(8,4,1) property -/

/-- All 3-subsets of the 8 points, as masks. -/
def triples : List Nat := (List.range 256).filter (fun m => pc m == 3)

/-- The number of blocks containing the point set `T`. -/
def countIn (T : Nat) : Nat := (blocks.filter (fun B => (T &&& B) == T)).length

theorem blocks_length : blocks.length = 14 := by decide

theorem blocks_size_four : blocks.all (fun b => pc b == 4) = true := by decide

/-- The 14 blocks are pairwise distinct. -/
theorem blocks_distinct :
    blocks.all (fun b => (blocks.filter (fun c => c == b)).length == 1) = true := by
  decide

theorem triples_length : triples.length = 56 := by decide

/-- Every 3-subset of the 8 points lies in exactly one block: AG(3,2) is a
genuine 3-(8,4,1) design (a Steiner quadruple system). -/
theorem each_triple_in_one_block :
    triples.all (fun T => countIn T == 1) = true := by decide

/-- The combined 3-(8,4,1) certificate. -/
theorem ag32_is_3_8_4_1 :
    blocks.length = 14 ∧ triples.length = 56 ∧
      blocks.all (fun b => pc b == 4) = true ∧
      triples.all (fun T => countIn T == 1) = true :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## The spectrum of AG(3,2) -/

theorem spectrum_length : (spec blocks).length = 91 := by decide

/-- Every pairwise intersection is 0 or 2. -/
theorem spectrum_values :
    (spec blocks).all (fun s => s == 0 || s == 2) = true := by decide

theorem spec_count_zero : ((spec blocks).filter (fun s => s == 0)).length = 7 := by
  decide

/-- The value `1` never occurs. -/
theorem spec_count_one : ((spec blocks).filter (fun s => s == 1)).length = 0 := by
  decide

theorem spec_count_two : ((spec blocks).filter (fun s => s == 2)).length = 84 := by
  decide

theorem s0_eq : s0 = 0 := by decide

theorem s1_eq : s1 = 2 := by decide

theorem one_absent : (spec blocks).all (fun s => s != 1) = true := by decide

/-- The interval `[s₀,s₁] = [0,2]` is NOT fully covered by the spectrum: the
Boolean sweep over `0,1,2` returns `false`. -/
theorem intervalFull_false : intervalFull = false := by decide

/-- A witness for the failure: `1` lies in `[s₀,s₁]` but not in the
spectrum. -/
theorem interval_missing_value :
    ∃ i : Nat, s0 ≤ i ∧ i ≤ s1 ∧ inSpectrum i = false :=
  ⟨1, by decide, by decide, by decide⟩

/-- Clause 1 of the conjecture, as a `Prop`, is **false**. -/
theorem intervalSpectrum_false : ¬ IntervalSpectrum := by
  intro h
  have h1 : inSpectrum 1 = true := h 1 (by decide) (by decide)
  have h2 : inSpectrum 1 = false := by decide
  rw [h2] at h1
  cases h1

/-- The refutation of clause 1, bundled with the exact values of `s₀` and
`s₁`. -/
theorem conjecture_first_clause_false :
    s0 = 0 ∧ s1 = 2 ∧ ¬ IntervalSpectrum :=
  ⟨by decide, by decide, intervalSpectrum_false⟩

/-! ## The second clause and 1-designs (Pasch) -/

/-- The Pasch configuration on the 6 points `1,…,6` (point `i` ↔ bit `i-1`):
`{1,2,3}, {1,4,5}, {2,4,6}, {3,5,6}`. -/
def pasch : List Nat := [7, 25, 42, 52]

/-- The six single-point masks of the Pasch configuration. -/
def paschPoints : List Nat := [1, 2, 4, 8, 16, 32]

/-- The number of Pasch blocks containing the point set `T`. -/
def paschCountIn (T : Nat) : Nat := (pasch.filter (fun B => (T &&& B) == T)).length

/-- `Symmetric` for a design with `bb` blocks on `v` points: `bb = v`.
Declared `abbrev` so that `decide` can unfold it when synthesising the
`Decidable` instance. -/
abbrev Symmetric (bb v : Nat) : Prop := bb = v

theorem pasch_length : pasch.length = 4 := by decide

theorem pasch_block_size : pasch.all (fun b => pc b == 3) = true := by decide

/-- Every pairwise intersection of Pasch blocks has size exactly 1. -/
theorem pasch_spectrum_all_one :
    (spec pasch).all (fun s => s == 1) = true := by decide

theorem pasch_spectrum_length : (spec pasch).length = 6 := by decide

/-- `s₀ = s₁` for the Pasch configuration. -/
theorem pasch_s0_eq_s1 :
    (spec pasch).foldl Nat.min 1000 = (spec pasch).foldl Nat.max 0 := by decide

/-- Each of the 6 points lies in exactly 2 Pasch blocks: a 1-(6,3,2)
design. -/
theorem pasch_is_1_design :
    paschPoints.all (fun P => paschCountIn P == 2) = true := by decide

/-- `b = 4 ≠ 6 = v`: the Pasch design is **not** symmetric. -/
theorem pasch_not_symmetric : ¬ Symmetric pasch.length 6 := by decide

/-- The second clause fails for 1-designs: `s₀ = s₁` yet the design is not
symmetric. -/
theorem second_clause_fails :
    (spec pasch).foldl Nat.min 1000 = (spec pasch).foldl Nat.max 0 ∧
      ¬ Symmetric pasch.length 6 :=
  ⟨by decide, by decide⟩

end Tlmc8434
