import Std

/-!
# Disproof of conjecture 00000002601 (Tarski fixed-point size)

The conjecture claims that the maximum number of fixed points of a monotone
self-map of an `n`-element finite lattice equals the length of a maximal chain,
is attained on distributive lattices, and drops strictly on non-distributive
lattices.

This file refutes the claim on the smallest non-trivial distributive lattice
`B₂ = {⊥, a, b, ⊤}` (the Boolean lattice on two atoms, `n = 4`).

The mathematical content is elementary:

* the identity map is monotone and fixes all `n` elements, so the maximum over
  all monotone self-maps is exactly `n` (the trivial upper bound);
* on `B₂` this maximum is `4`, while a maximal chain `⊥ < a < ⊤` has only
  `3` elements (and `2` edges);
* hence `max #fixed points ≠ maximal chain length` already on a distributive
  lattice, under either reading of "length" (elements or edges).

All proofs below are computational and use only core Lean (`import Std`); no
Mathlib, no `sorry`, no `axiom`, no `native_decide`.
-/

set_option maxRecDepth 100000

namespace Tlmc2601

/-- `B₂ = {⊥, a, b, ⊤}` encoded as `Fin 4`:
`0 = ⊥`, `1 = a`, `2 = b`, `3 = ⊤`. -/
abbrev B2 := Fin 4

/-- The order of `B₂`: `0` is the bottom, `3` is the top, and `1`, `2` are
incomparable.  Thus `x ≤ y` iff `x = y`, or `x = ⊥`, or `y = ⊤`. -/
def le (x y : Fin 4) : Prop := x = y ∨ x = 0 ∨ y = 3

instance instDecidableLe (x y : Fin 4) : Decidable (le x y) := by
  unfold le; infer_instance

/-- Boolean-valued version of `le`, used for computation. -/
def leB (x y : Fin 4) : Bool := decide (le x y)

/-- A self-map of `B₂` is monotone iff it is order-preserving. -/
def Monotone (f : Fin 4 → Fin 4) : Prop := ∀ x y, le x y → le (f x) (f y)

instance instDecidableMonotone (f : Fin 4 → Fin 4) : Decidable (Monotone f) := by
  unfold Monotone; infer_instance

/-- The identity map is monotone. -/
theorem identity_monotone : Monotone id := by decide

/-- The identity map fixes every element of `B₂`. -/
theorem identity_fixes_all : ∀ x : Fin 4, id x = x := by decide

/-- Number of fixed points of a self-map of `B₂`. -/
def fixedCount (f : Fin 4 → Fin 4) : Nat :=
  ((List.finRange 4).filter (fun x => decide (f x = x))).length

/-- The identity has exactly four fixed points. -/
theorem identity_fixed_count : fixedCount id = 4 := by decide

/-- Decidable (Bool-valued) monotonicity check. -/
def monotoneB (f : Fin 4 → Fin 4) : Bool :=
  (List.finRange 4).all fun x =>
    (List.finRange 4).all fun y =>
      !(leB x y) || leB (f x) (f y)

/-- The Bool-valued order check reflects the propositional order. -/
theorem leB_eq_true {x y : Fin 4} : leB x y = true ↔ le x y := by
  unfold leB
  rw [decide_eq_true_iff]

/-- The Bool-valued check agrees with the propositional predicate. -/
theorem monotoneB_iff (f : Fin 4 → Fin 4) : monotoneB f = true ↔ Monotone f := by
  unfold monotoneB Monotone
  rw [List.all_eq_true]
  constructor
  · intro h x y hxy
    have hx := h x (List.mem_finRange x)
    rw [List.all_eq_true] at hx
    have hy := hx y (List.mem_finRange y)
    have hxy' : leB x y = true := leB_eq_true.mpr hxy
    rw [hxy'] at hy
    simpa using leB_eq_true.mp hy
  · intro h
    intro x _
    apply List.all_eq_true.mpr
    intro y _
    by_cases hxy : le x y
    · have hxy' : leB x y = true := leB_eq_true.mpr hxy
      have hfy : leB (f x) (f y) = true := leB_eq_true.mpr (h x y hxy)
      simp [hxy', hfy]
    · have hxy' : leB x y = false := by
        cases hb : leB x y with
        | false => rfl
        | true => exact absurd (leB_eq_true.mp hb) hxy
      simp [hxy']

/-- A function `Fin 4 → Fin 4` encoded by a base-4 code `c ∈ [0, 256)`:
the `x`-th base-4 digit of `c` is the value at `x`. -/
def applyCode (c : Nat) (x : Fin 4) : Fin 4 :=
  ⟨(c / 4 ^ x.val) % 4, Nat.mod_lt _ (by decide)⟩

/-- The maximum number of fixed points among all monotone self-maps of `B₂`,
obtained by exhaustive search over all `4 ^ 4 = 256` functions. -/
def maxFixedPoints : Nat :=
  (List.range 256).foldl
    (fun best c =>
      if monotoneB (applyCode c) then max best (fixedCount (applyCode c)) else best)
    0

/-- The exhaustive maximum is `4`, the trivial upper bound `|B₂|`. -/
theorem maxFixedPoints_eq_four : maxFixedPoints = 4 := by decide

/-- The number of monotone self-maps of `B₂` is `36`. -/
def countMonotone : Nat :=
  ((List.range 256).filter (fun c => monotoneB (applyCode c))).length

theorem countMonotone_eq_36 : countMonotone = 36 := by decide

/-- All lists over `B₂` of length exactly `n` (for chain enumeration). -/
def seqsOfLen : Nat → List (List (Fin 4))
  | 0 => [[]]
  | n + 1 => List.flatMap (fun t => (List.finRange 4).map (fun a => t ++ [a])) (seqsOfLen n)

/-- All lists over `B₂` of length at most `4`. -/
def allSeqs : List (List (Fin 4)) :=
  List.flatMap seqsOfLen (List.range 5)

/-- A list is a chain when its entries are distinct and pairwise comparable. -/
def chainB (l : List (Fin 4)) : Bool :=
  decide l.Nodup && l.all (fun x => l.all (fun y => leB x y || leB y x))

/-- The maximum number of elements in a chain of `B₂`. -/
def maxChainLen : Nat :=
  ((allSeqs.filter chainB).map (fun l => l.length)).foldl max 0

/-- A maximal chain of `B₂` has `3` elements (`⊥ < a < ⊤`). -/
theorem maxChainLen_eq_three : maxChainLen = 3 := by decide

/-- Under the "length = number of edges" reading, the maximal chain has
`2` edges. -/
theorem maxChainEdges_eq_two : maxChainLen - 1 = 2 := by decide

/-- The chain `⊥ < a < ⊤` explicitly. -/
def witnessChain : List (Fin 4) := [0, 1, 3]

theorem witnessChain_is_chain : chainB witnessChain = true := by decide

/-- Main refutation: on the distributive lattice `B₂`,
`max #fixed points = 4`, `maximal chain length = 3` (elements) or `2` (edges),
and `4 > 3`.  Hence the maximum number of fixed points does **not** equal the
maximal chain length, already on a distributive lattice. -/
theorem conjecture_00000002601_false :
    maxFixedPoints = 4 ∧ maxChainLen = 3 ∧ maxFixedPoints > maxChainLen := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The same failure under the edges reading: `4 > 2`. -/
theorem conjecture_00000002601_false_edges :
    maxFixedPoints = 4 ∧ maxChainLen - 1 = 2 ∧ maxFixedPoints > maxChainLen - 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Tlmc2601
