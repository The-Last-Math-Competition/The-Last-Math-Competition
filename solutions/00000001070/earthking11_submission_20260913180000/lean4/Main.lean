/-
  Disproof of conjecture `00000001070`.

  Definition (as filed): the three-fold sumset `A + A + A`, i.e. repetitions of
  summands are allowed.  Conjecture: the smallest `|A|` with `3A = F_p` is
  `⌈(p+1)/3⌉ + 1` (the three-sum threshold).

  This file formalises a decisive counterexample at `p = 7`: the set
  `A = {0,1,3} ⊆ F_7` has `|A| = 3` distinct elements and satisfies
  `3A = F_7`, while the conjectured formula gives `⌈(7+1)/3⌉ + 1 = 4`.
  Hence the conjectured value is too large already at `p = 7`, so the
  conjecture is FALSE.

  The corrected general value is `⌈(p+2)/3⌉`: it is a lower bound by
  Cauchy–Davenport (`|3A| ≥ 3|A| − 2`) and it is attained by the interval
  `A = {0, 1, …, k−1}`, whose three-fold sum is `{0, 1, …, 3k−3}`.

  Core Lean only (`import Std`); no Mathlib, no `ZMod`, no `sorry`, no
  `axiom`, no `native_decide`.

  Formalisation note.  `Fintype`/`Finset` live in Mathlib and are deliberately
  avoided, so `decide` cannot be used directly on a quantifier `∀ y : Fin 7`
  (there is no `Fintype (Fin 7)` instance in core `Std`).  The universal
  statement `witness_threefold` is therefore obtained from the Boolean
  enumeration `witness_threefold_bool` (closed by `decide`) through the small
  soundness lemma `isThreefoldSum_sound`.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc1070

/-- `F_7`, the field with seven elements, is modelled as `Fin 7` with its
cyclic addition (addition modulo `7`). -/
abbrev F7 := Fin 7

/-- The list of all three-fold sums `a + b + c` with `a, b, c ∈ A`
(repetitions allowed), i.e. a concrete enumeration of the sumset `A + A + A`. -/
def tripleSums (A : List F7) : List F7 :=
  A.flatMap (fun a => A.flatMap (fun b => A.map (fun c => a + b + c)))

/-- Boolean test: `y` occurs among the three-fold sums of `A`. -/
def isThreefoldSum (A : List F7) (y : F7) : Bool :=
  A.any (fun a => A.any (fun b => A.any (fun c => a + b + c == y)))

/-- `y` is a three-fold sum of elements of the finite set `A` when there exist
`a, b, c ∈ A` with `a + b + c = y`.  Repetitions of summands are allowed, so
this is exactly membership in `A + A + A`. -/
def IsThreefoldSum (A : List F7) (y : F7) : Prop :=
  ∃ a b c : F7, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a + b + c = y

/-- Soundness of the Boolean test: if `isThreefoldSum A y` holds, then `y` is a
three-fold sum of elements of `A`. -/
theorem isThreefoldSum_sound {A : List F7} {y : F7} :
    isThreefoldSum A y = true → IsThreefoldSum A y := by
  intro h
  unfold isThreefoldSum IsThreefoldSum at *
  rw [List.any_eq_true] at h
  obtain ⟨a, ha, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨b, hb, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨c, hc, h⟩ := h
  exact ⟨a, b, c, ha, hb, hc, by simpa [beq_iff_eq] using h⟩

/-- **The witness covers all of `F_7`** (Boolean form).  Every residue
`y ∈ {0,…,6}` is a sum `a + b + c` of three elements of `A = {0,1,3}`
(repetitions allowed): the `27` triples of `A` hit all `7` residues. -/
theorem witness_threefold_bool :
    (List.finRange 7).all (fun y => isThreefoldSum [0, 1, 3] y) = true := by
  decide

/-- **The witness covers all of `F_7`.**  Every residue `y : Fin 7` is a sum
`a + b + c` of three elements of `A = {0,1,3}` (repetitions allowed). -/
theorem witness_threefold :
    ∀ y : F7, IsThreefoldSum ([0, 1, 3] : List F7) y := by
  intro y
  exact isThreefoldSum_sound
    ((List.all_eq_true.1 witness_threefold_bool) y (List.mem_finRange y))

/-- The witness `{0,1,3}` has exactly `3` distinct elements, so `|A| = 3`. -/
theorem witness_size : ([0, 1, 3] : List F7).eraseDups.length = 3 := by decide

/-- Explicit `3A` for the witness: the `3 × 3 × 3 = 27` three-fold sums already
cover all seven residues. -/
theorem witness_threefold_set :
    (List.finRange 7).all (fun y => (tripleSums [0, 1, 3]).contains y) = true := by
  decide

/-- All two-element subsets of `F_7`, listed as increasing pairs. -/
def allPairs : List (List F7) :=
  (List.finRange 7).flatMap (fun a =>
    (List.finRange 7).flatMap (fun b =>
      if a.val < b.val then [[a, b]] else []))

/-- **No two-element subset suffices.**  Every one of the `C(7,2) = 21`
two-element subsets of `F_7` fails to have three-fold sum equal to `F_7`.
This is the `|A| = 2` case of the Cauchy–Davenport lower bound. -/
theorem no_two_elements :
    allPairs.all (fun A => !((List.finRange 7).all (fun y => isThreefoldSum A y))) = true := by
  decide

/-- The conjectured formula at `p = 7`: `⌈(7+1)/3⌉ + 1 = 4`, encoded with
natural-number division as `(7 + 1 + 2) / 3 + 1 = 4`. -/
theorem formula_at_seven : (7 + 1 + 2) / 3 + 1 = 4 := by decide

/-- The corrected general value at `p = 7`: `⌈(7+2)/3⌉ = 3`, encoded as
`(7 + 2 + 2) / 3 = 3`. -/
theorem corrected_at_seven : (7 + 2 + 2) / 3 = 3 := by decide

/-- At `p = 7` the corrected value `⌈(7+2)/3⌉ = 3` equals the size of the
witness, i.e. the corrected formula is tight here. -/
theorem corrected_matches_witness :
    (7 + 2 + 2) / 3 = ([0, 1, 3] : List F7).eraseDups.length := by decide

/-- The witness size `3` is strictly smaller than the formula's value `4`, so
the conjecture overestimates the threshold at `p = 7`. -/
theorem formula_too_large :
    (7 + 1 + 2) / 3 + 1 ≠ ([0, 1, 3] : List F7).eraseDups.length := by decide

/-- **Disproof of conjecture `00000001070`.**  Conjunction of the essential
facts: the three-element set `{0,1,3}` has three-fold sum all of `F_7`, its
size is `3`, the conjectured formula evaluates to `4` at `p = 7`, and
`4 ≠ 3`.  Therefore the smallest `|A|` with `3A = F_p` is *not*
`⌈(p+1)/3⌉ + 1`. -/
theorem conjecture_00000001070_false :
    (∀ y : F7, IsThreefoldSum ([0, 1, 3] : List F7) y) ∧
    ([0, 1, 3] : List F7).eraseDups.length = 3 ∧
    (7 + 1 + 2) / 3 + 1 = 4 ∧
    (7 + 1 + 2) / 3 + 1 ≠ ([0, 1, 3] : List F7).eraseDups.length :=
  ⟨witness_threefold, witness_size, formula_at_seven, formula_too_large⟩

end Tlmc1070
