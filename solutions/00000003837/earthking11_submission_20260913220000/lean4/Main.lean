/-
  Disproof of conjecture `00000003837` ("star fixed point parity").

  Conjecture as filed:

    Definition: the star involution * is the crystal involution reversing all
    simple arrow directions, always existing in finite type.
    Conjecture: the number of *-fixed points in B(λ) is always odd, and when
    λ = -w₀λ the number of *-fixed points is at least 3.

  Counterexample: type A₁, λ = ω₁.  B(ω₁) is the two-element sl₂ crystal with
  weights +1, -1 and a single arrow.  In type A₁ the longest element w₀ = s₁
  acts on the weight lattice by -1, so -w₀ acts as the identity: λ = -w₀λ holds
  for EVERY λ, in particular for λ = ω₁.  The star involution reverses the
  unique arrow, hence must swap the two elements, so it has 0 fixed points.
  This is even, contradicting "always odd", and 0 < 3, contradicting the
  "at least 3" clause.

  Everything below is core Lean (`import Std`, no Mathlib, no `sorry`).

  The convention-independent statement proved here is: for EVERY involution σ
  of B(ω₁) the number of fixed points is even (0 or 2).  So no choice of an
  arrow-reversing involution can rescue the parity claim.  We also show that the
  arrow-reversing requirement pins the star down uniquely (it must be the swap),
  and that no weight-preserving arrow reversal exists, so the weight condition
  cannot be used to dodge the example.
-/

import Std

namespace StarParity837

/-! ## The crystal `B(ω₁)` of type `A₁` -/

/-- The crystal `B(ω₁)` of `sl₂` (type `A₁`): two elements of weights +1, -1. -/
abbrev B1 : Type := Fin 2

/-- Every element of `Fin 2` is `0` or `1`. -/
theorem B1_eq_zero_or_one (x : B1) : x = 0 ∨ x = 1 := by
  have h : x.val = 0 ∨ x.val = 1 := by omega
  rcases h with h | h
  · left; exact Fin.ext h
  · right; exact Fin.ext h

/-- `f₁` (lowering) on `B(ω₁)`: defined only at the top element. -/
def f1 (j : B1) : Option B1 :=
  if h : j.val + 1 < 2 then some ⟨j.val + 1, h⟩ else none

/-- `e₁` (raising) on `B(ω₁)`: defined only at the bottom element. -/
def e1 (j : B1) : Option B1 :=
  if h : 0 < j.val then some ⟨j.val - 1, by omega⟩ else none

/-- Weight of a crystal element (units of `ω₁`): `+1` at `0`, `-1` at `1`. -/
def wt (j : B1) : Int := 1 - 2 * (j.val : Int)

/-- The star involution on `B(ω₁)`: reverses the unique arrow, i.e. swaps. -/
def star (j : B1) : B1 := ⟨1 - j.val, by omega⟩

/-- Honest fixed-point count over the underlying finite list of elements. -/
def fixedCount (σ : B1 → B1) : Nat :=
  ((List.finRange 2).filter (fun x => σ x = x)).length

/-! ## The crystal `B(ω₁)` is a single arrow on two elements -/

/-- `B(ω₁)` has exactly two elements. -/
theorem B1_card : (List.finRange 2).length = 2 := by decide

/-- `B(ω₁)` is one arrow: `f₁ 0 = 1`, `f₁ 1 = none`. -/
theorem f1_top : f1 0 = some 1 ∧ f1 1 = none := by decide

/-- Dually `e₁ 1 = 0`, `e₁ 0 = none`. -/
theorem e1_bottom : e1 1 = some 0 ∧ e1 0 = none := by decide

/-! ## The star involution -/

/-- `*` is an involution (`*² = id`). -/
theorem star_involutive : ∀ j : B1, star (star j) = j := by decide

/-- `*` reverses the lowering arrow: `f₁ (star j) = star (e₁ j)`. -/
theorem star_reverses_f : ∀ j : B1, f1 (star j) = (e1 j).map star := by decide

/-- `*` reverses the raising arrow: `e₁ (star j) = star (f₁ j)`. -/
theorem star_reverses_e : ∀ j : B1, e1 (star j) = (f1 j).map star := by decide

/-- `*` negates weights (the correct weight condition in type `A₁`). -/
theorem wt_star : ∀ j : B1, wt (star j) = - wt j := by decide

/-- The star involution is concretely the swap `0 ↔ 1`. -/
theorem star_apply : star 0 = 1 ∧ star 1 = 0 := by decide

/-! ## The refutation at `λ = ω₁` -/

/-- The star involution on `B(ω₁)` has no fixed point at all. -/
theorem star_fixedCount : fixedCount star = 0 := by decide

/-- Hence the number of fixed points is even, contradicting "always odd". -/
theorem star_even : fixedCount star % 2 = 0 := by decide

/-- And it is strictly less than 3, contradicting "at least 3". -/
theorem star_lt_three : fixedCount star < 3 := by decide

/-- The disproof of conjecture `00000003837`: at `λ = ω₁` (where `λ = -w₀λ`
holds) the star involution has `0` fixed points, which is even and `< 3`. -/
theorem conjecture_00000003837_false :
    fixedCount star = 0 ∧ fixedCount star % 2 = 0 ∧ fixedCount star < 3 :=
  ⟨star_fixedCount, star_even, star_lt_three⟩

/-- The two failing components of the conjecture, packaged. -/
theorem star_conjecture_false :
    fixedCount star % 2 = 0 ∧ fixedCount star < 3 :=
  ⟨star_even, star_lt_three⟩

/-! ## Robustness: no involution can rescue the claim -/

/-- Closed form for the fixed-point count over the two-element crystal. -/
theorem fixedCount_eq (σ : B1 → B1) :
    fixedCount σ = (if σ 0 = 0 then 1 else 0) + (if σ 1 = 1 then 1 else 0) := by
  simp only [fixedCount]
  simp [List.finRange]
  split <;> split <;> simp_all

/-- Every involution of `B(ω₁)` has an even number of fixed points.  This is the
two-element instance of the elementary parity lemma: non-fixed points of an
involution pair up in 2-cycles. -/
theorem involution_fixedCount_even (σ : B1 → B1) (hσ : ∀ x, σ (σ x) = x) :
    fixedCount σ % 2 = 0 := by
  rw [fixedCount_eq]
  rcases B1_eq_zero_or_one (σ 0) with h0 | h0 <;>
    rcases B1_eq_zero_or_one (σ 1) with h1 | h1
  · exfalso; have h := hσ 1; rw [h1, h0] at h; cases h
  · rw [h0, h1]; decide
  · rw [h0, h1]; decide
  · exfalso; have h := hσ 0; rw [h0, h1] at h; cases h

/-- Every involution of `B(ω₁)` has at most two fixed points (in particular
fewer than three). -/
theorem involution_fixedCount_lt_three (σ : B1 → B1) (_hσ : ∀ x, σ (σ x) = x) :
    fixedCount σ < 3 := by
  rw [fixedCount_eq]
  rcases B1_eq_zero_or_one (σ 0) with h0 | h0 <;>
    rcases B1_eq_zero_or_one (σ 1) with h1 | h1 <;> rw [h0, h1] <;> decide

/-- The arrow-reversing involution of `B(ω₁)` is unique, so any faithful
convention for the star involution agrees with the swap `star` formalised
here. -/
theorem arrow_reversing_involution_eq_star (σ : B1 → B1)
    (hσ : ∀ x, σ (σ x) = x)
    (hf : ∀ j : B1, f1 (σ j) = (e1 j).map σ) : σ = star := by
  funext j
  rcases B1_eq_zero_or_one (σ 0) with h0 | h0
  · exfalso
    have h := hf 0
    rw [h0] at h
    cases h
  · rcases B1_eq_zero_or_one j with rfl | rfl
    · rw [h0]; decide
    · have h1 : σ 1 = 0 := by have h := hσ 0; rw [h0] at h; exact h
      rw [h1]; decide

/-- There is no weight-preserving arrow-reversing involution of `B(ω₁)`: a
faithful star must negate weights in type `A₁`, so the weight convention cannot
be tweaked to produce a fixed point. -/
theorem no_weight_preserving_arrow_reversal :
    ¬ ∃ σ : B1 → B1, (∀ x, σ (σ x) = x) ∧ (∀ j : B1, wt (σ j) = wt j)
      ∧ (∀ j : B1, f1 (σ j) = (e1 j).map σ) := by
  rintro ⟨σ, hσ, hw, hf⟩
  have h_eq : σ = star := arrow_reversing_involution_eq_star σ hσ hf
  have h : wt (star 0) = wt (0 : B1) := by rw [← h_eq]; exact hw 0
  cases h

end StarParity837
