/-
  Disproof of conjecture `00000002192`.

  Conjecture (as filed):
    Definition: the dimension of a poset is the minimal number of linear
    extensions whose intersection is the poset.
    Conjecture: the maximal dimension of height-2 posets is ⌈log₂ log₂ n⌉,
    the bound following from the deep nesting of standard examples.

  The conjecture is FALSE.  The file never defines `n`; under the natural
  reading `n = |P|` the claim already fails on the smallest non-trivial
  standard example.  The standard example `S_2` on the four elements
  `{0,1,2,3}` with `0 < 3` and `1 < 2` has height 2 and dimension exactly 2,
  while `⌈log₂ log₂ 4⌉ = 1`.  Two linear extensions whose intersection is
  `S_2` are exhibited, and no single linear extension can realise `S_2`.

  Core Lean only (`import Std`), no Mathlib, no `sorry`.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc2192

abbrev E := Fin 4

/-- The standard example `S_2` on the four elements `0,1,2,3`: the elements
`0,1` are minimal, `2,3` are maximal, and the only strict relations are
`0 < 3` and `1 < 2` (so `0 ≮ 2`, `1 ≮ 3`). -/
def ltS2 (x y : E) : Prop := (x = 0 ∧ y = 3) ∨ (x = 1 ∧ y = 2)

/-- Decidability of `ltS2`, used by `decide` on concrete elements. -/
instance decidableLtS2 (x y : E) : Decidable (ltS2 x y) := by
  unfold ltS2
  infer_instance

/-- A linear extension of `S_2`, presented as a list of all four elements in
increasing order: no repetitions, length `4`, and every relation of `S_2` is
respected.  (An `abbrev` so that `decide` can unfold it.) -/
abbrev IsLinExt (L : List E) : Prop :=
  L.Nodup ∧ L.length = 4 ∧ ∀ x y : E, ltS2 x y → L.idxOf x < L.idxOf y

/-- Pointwise intersection of a list of linear extensions: `x` precedes `y`
in the intersection iff it precedes `y` in every member. -/
abbrev Intersection (Ls : List (List E)) (x y : E) : Prop :=
  ∀ L ∈ Ls, L.idxOf x < L.idxOf y

/-- `Ls` is a realizer of `S_2`: every member is a linear extension and the
intersection is exactly `ltS2`. -/
abbrev IsRealizer (Ls : List (List E)) : Prop :=
  (∀ L ∈ Ls, IsLinExt L) ∧ ∀ x y : E, Intersection Ls x y ↔ ltS2 x y

/-- The poset `S_2` has dimension at most `d`: there is a realizer of `d`
linear extensions. -/
def DimLe (d : Nat) : Prop := ∃ Ls : List (List E), Ls.length = d ∧ IsRealizer Ls

/-- The poset `S_2` has dimension exactly `d`. -/
def DimEq (d : Nat) : Prop := DimLe d ∧ ∀ e : Nat, DimLe e → d ≤ e

/-- `S_2` has height 2: some `2`-chain exists and there is no `3`-chain. -/
abbrev HeightTwo : Prop :=
  (∃ x y : E, ltS2 x y) ∧ ¬ (∃ x y z : E, ltS2 x y ∧ ltS2 y z)

/-! ## Basic facts about `ltS2` -/

theorem ltS2_irrefl : ∀ x : E, ¬ ltS2 x x := by decide

theorem ltS2_asymm : ∀ x y : E, ltS2 x y → ¬ ltS2 y x := by decide

theorem ltS2_03 : ltS2 0 3 := by decide

theorem ltS2_12 : ltS2 1 2 := by decide

theorem not_ltS2_01 : ¬ ltS2 (0 : E) 1 := by decide

theorem not_ltS2_10 : ¬ ltS2 (1 : E) 0 := by decide

/-- `S_2` has no chain of three elements: the only relations are the disjoint
pairs `0 < 3` and `1 < 2`. -/
theorem no_three_chain : ¬ (∃ x y z : E, ltS2 x y ∧ ltS2 y z) := by decide

theorem height_two : HeightTwo :=
  ⟨⟨0, 3, ltS2_03⟩, no_three_chain⟩

/-! ## Two linear extensions realizing `S_2` -/

/-- The first linear extension: `0 < 3 < 1 < 2`. -/
def L1 : List E := [0, 3, 1, 2]

/-- The second linear extension: `1 < 2 < 0 < 3`. -/
def L2 : List E := [1, 2, 0, 3]

theorem isLinExt_L1 : IsLinExt L1 := by decide

theorem isLinExt_L2 : IsLinExt L2 := by decide

/-- The intersection of `L1` and `L2` is exactly `ltS2`. -/
theorem inter_L1_L2 : ∀ x y : E, Intersection [L1, L2] x y ↔ ltS2 x y := by
  decide

/-! ## No single linear extension realizes `S_2` -/

/-- Unfolding a singleton intersection. -/
theorem inter_singleton (L : List E) (x y : E) :
    Intersection [L] x y ↔ L.idxOf x < L.idxOf y := by
  simp [Intersection]

/-- **Key lower bound.** No single linear extension realises `S_2`: a single
extension is total, so it must order `0` and `1`; but `ltS2 0 1` and
`ltS2 1 0` are both false, so either order contradicts a realizer. -/
theorem no_single (L : List E) (h : IsLinExt L) :
    ¬ (∀ x y : E, Intersection [L] x y ↔ ltS2 x y) := by
  intro hreal
  obtain ⟨hnd, hlen, _⟩ := h
  have hreal' : ∀ x y : E, ltS2 x y ↔ L.idxOf x < L.idxOf y := by
    intro x y
    exact (hreal x y).symm.trans (inter_singleton L x y)
  have h03 : L.idxOf (0 : E) < L.idxOf (3 : E) := (hreal' 0 3).mp ltS2_03
  have h12 : L.idxOf (1 : E) < L.idxOf (2 : E) := (hreal' 1 2).mp ltS2_12
  have hle3 : L.idxOf (3 : E) ≤ L.length := List.idxOf_le_length
  have hle2 : L.idxOf (2 : E) ≤ L.length := List.idxOf_le_length
  have h0lt : L.idxOf (0 : E) < L.length := by omega
  have h1lt : L.idxOf (1 : E) < L.length := by omega
  have h01 : ¬ (L.idxOf (0 : E) < L.idxOf (1 : E)) := by
    intro hc
    exact absurd ((hreal' 0 1).mpr hc) not_ltS2_01
  have h10 : ¬ (L.idxOf (1 : E) < L.idxOf (0 : E)) := by
    intro hc
    exact absurd ((hreal' 1 0).mpr hc) not_ltS2_10
  have heq : L.idxOf (0 : E) = L.idxOf (1 : E) := by omega
  have e0 : L[L.idxOf (0 : E)]? = some (0 : E) := by
    rw [List.getElem?_eq_getElem h0lt, List.getElem_idxOf h0lt]
  have e1 : L[L.idxOf (1 : E)]? = some (1 : E) := by
    rw [List.getElem?_eq_getElem h1lt, List.getElem_idxOf h1lt]
  have heq2 : L[L.idxOf (0 : E)]? = L[L.idxOf (1 : E)]? := by rw [heq]
  have hsome : (some (0 : E) : Option E) = some 1 := by
    rw [← e0, heq2, e1]
  exact absurd (Option.some.inj hsome) (by decide)

theorem not_dim_le_one : ¬ DimLe 1 := by
  rintro ⟨Ls, hlen, hreal⟩
  obtain ⟨L, rfl⟩ : ∃ L : List E, Ls = [L] := by
    cases Ls with
    | nil => simp at hlen
    | cons a t =>
        cases t with
        | nil => exact ⟨a, rfl⟩
        | cons b t => simp at hlen
  exact no_single L (hreal.1 L (by simp)) hreal.2

theorem not_dim_le_zero : ¬ DimLe 0 := by
  rintro ⟨Ls, hlen, hreal⟩
  have hnil : Ls = [] := List.length_eq_zero_iff.mp hlen
  subst hnil
  have h := hreal.2 0 0
  simp [Intersection] at h
  exact absurd h (by decide)

/-! ## The dimension is exactly 2 -/

theorem dim_le_two : DimLe 2 :=
  ⟨[L1, L2], by decide, by
    constructor
    · intro L hL
      simp at hL
      rcases hL with rfl | rfl
      · exact isLinExt_L1
      · exact isLinExt_L2
    · exact inter_L1_L2⟩

theorem dim_eq_two : DimEq 2 := by
  constructor
  · exact dim_le_two
  · intro e he
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · subst h0
      exact absurd he not_dim_le_zero
    · have hcases : e = 1 ∨ 2 ≤ e := by omega
      rcases hcases with h1 | h2
      · subst h1
        exact absurd he not_dim_le_one
      · exact h2

/-! ## The conjectured value and the contradiction -/

/-- The integer reading of the conjectured bound at `n = 4`: with `n` the
number of elements, `⌈log₂ log₂ 4⌉ = 1`, here computed as the exact
integer iterated logarithm `Nat.log2 (Nat.log2 4)`. -/
theorem formula_at_four : Nat.log2 (Nat.log2 4) = 1 := by decide

/-- **The conjecture is false.**  `S_2` is a height-2 poset on `n = 4`
elements whose dimension is exactly `2`, whereas the conjectured value
`⌈log₂ log₂ 4⌉ = 1` is strictly smaller; hence the maximal dimension of
height-2 posets is not given by that formula. -/
theorem conjecture_00000002192_false :
    HeightTwo ∧ DimEq 2 ∧ Nat.log2 (Nat.log2 4) = 1 ∧ 2 ≠ 1 :=
  ⟨height_two, dim_eq_two, formula_at_four, by decide⟩

end Tlmc2192
