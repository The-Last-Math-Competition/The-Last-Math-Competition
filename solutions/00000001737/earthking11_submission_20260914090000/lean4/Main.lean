/-
  Disproof of conjecture `00000001737`: formalisation.

  Conjecture (as filed):
    "The maximal possible number of S-integral points of P¹ ∖ {0,1,∞} with S of
     two primes is 12."

  This file is a LOWER-BOUND WITNESS.  Take S = {2,3}.  The 21 rationals
      -8, -3, -2, -1, -1/2, -1/3, -1/8, 1/9, 1/4, 1/3, 1/2, 2/3, 3/4,
      8/9, 9/8, 4/3, 3/2, 2, 3, 4, 9
  are pairwise distinct S-integral points of P¹ ∖ {0,1,∞}: for each of them
  both x and 1 - x are S-units (no prime other than 2, 3 divides a numerator
  or denominator).  Hence the maximum is at least 21 > 12, so the conjecture
  as stated is false.  (The exact maximum is *not* computed here: that requires
  the S-unit theorem / linear forms in logarithms.  A lower bound of 21 already
  suffices to refute an upper bound of 12.)

  Core Lean only (`import Std`).  No Mathlib, no `Rat`, no `Finset`.

  Why not `Rat`?  `decide` cannot reduce `Rat` (its normalisation is opaque),
  so every rational is encoded as a pair `(p : Int, q : Nat)` with `q > 0`,
  meaning `p / q`, and all comparisons use cross-multiplication
  `p₁ * q₂ = p₂ * q₁`, a closed `Int` identity that `decide` can reduce.
  `Finset` is absent from `import Std`, so `List` is used throughout.
  Because Decidable synthesis does not unfold a `def`-wrapped `Prop`, the
  integrality predicate is `Bool`-valued and the theorems are stated as
  `... = true`.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc1737

/-! ## `(2,3)`-smooth naturals

`n` is `(2,3)`-smooth (the numerator/denominator behaviour of an S-unit for
`S = {2,3}`) if `n = 2^a * 3^b` for some `a b : Nat`.  We encode this as a
*decidable* Boolean search so that `decide` can verify concrete instances; the
lemma `isSmooth_sound` below turns a successful check back into the honest
existential statement, which is what makes the encoding faithful. -/

/-- Decidable check: is `n = 2^a * 3^b` for some `a, b ≤ n`? -/
def IsSmooth (n : Nat) : Bool :=
  (List.range (n + 1)).any fun a =>
    (List.range (n + 1)).any fun b => n == 2 ^ a * 3 ^ b

/-- **Soundness of the check**: a successful `IsSmooth` really exhibits
exponents, so the Boolean predicate is not merely an approximation of
smoothness but equivalent to it on hits. -/
theorem isSmooth_sound {n : Nat} (h : IsSmooth n = true) :
    ∃ a b : Nat, n = 2 ^ a * 3 ^ b := by
  unfold IsSmooth at h
  rw [List.any_eq_true] at h
  obtain ⟨a, _ha, hb⟩ := h
  rw [List.any_eq_true] at hb
  obtain ⟨b, _hb, hb'⟩ := hb
  exact ⟨a, b, by simpa using hb'⟩

/-- Concrete sanity checks for the smoothness test (also exercise `decide`). -/
theorem isSmooth_one : IsSmooth 1 = true := by decide
theorem isSmooth_two : IsSmooth 2 = true := by decide
theorem isSmooth_three : IsSmooth 3 = true := by decide
theorem isSmooth_four : IsSmooth 4 = true := by decide
theorem isSmooth_eight : IsSmooth 8 = true := by decide
theorem isSmooth_nine : IsSmooth 9 = true := by decide
theorem isSmooth_five : IsSmooth 5 = false := by decide
theorem isSmooth_seven : IsSmooth 7 = false := by decide

/-- Soundness on `5` and `7`: the check really excludes non-`{2,3}`-smooth
numbers.  Stated contrapositively so no unbounded search is needed at runtime. -/
theorem not_isSmooth_five : ¬ IsSmooth 5 = true := by decide
theorem not_isSmooth_seven : ¬ IsSmooth 7 = true := by decide

/-! ## Rationals as integer pairs, and the integrality predicates -/

/-- Boolean check that `p/q` is an S-unit of `Z[1/2,1/3]`: `q > 0`, `p ≠ 0`,
and `|p|`, `q` are both `(2,3)`-smooth.  (The sign of `p` is free: units of
`Z[1/2,1/3]` are `±2^a 3^b`.) -/
def SUnitRatB (p : Int) (q : Nat) : Bool :=
  decide (0 < q) && decide (p ≠ 0) && IsSmooth p.natAbs && IsSmooth q

/-- Boolean check that `p/q` is an S-integral point of `P¹ ∖ {0,1,∞}`:
`p/q` is an S-unit, `p/q ≠ 1`, and `1 - p/q = (q - p)/q` is an S-unit. -/
def SIntegralB (p : Int) (q : Nat) : Bool :=
  SUnitRatB p q && decide (p ≠ (q : Int)) && IsSmooth ((q : Int) - p).natAbs

/-- `SIntegral p q`: `p/q` is an S-integral point of `P¹ ∖ {0,1,∞}`. -/
def SIntegral (p : Int) (q : Nat) : Prop := SIntegralB p q = true

/-- **Faithfulness of the Boolean check**: passing `SIntegralB` really means
that `p/q` is a unit of `Z[1/2,1/3]` and that `1 - p/q` is again such a unit —
i.e. exactly the S-integrality of `p/q` on `P¹ ∖ {0,1,∞}`.  This is the
definitional bridge between the executable test and the mathematical
statement. -/
theorem sIntegral_sound {p : Int} {q : Nat} (h : SIntegral p q) :
    0 < q ∧ p ≠ 0 ∧
    (∃ a b : Nat, p.natAbs = 2 ^ a * 3 ^ b) ∧
    (∃ a b : Nat, q = 2 ^ a * 3 ^ b) ∧
    p ≠ (q : Int) ∧
    (∃ a b : Nat, ((q : Int) - p).natAbs = 2 ^ a * 3 ^ b) := by
  have h' : (SUnitRatB p q = true ∧ p ≠ (q : Int)) ∧
      IsSmooth ((q : Int) - p).natAbs = true := by
    simpa [SIntegral, SIntegralB, Bool.and_eq_true] using h
  obtain ⟨⟨hunit, hne⟩, hcomp⟩ := h'
  have hunit' : ((0 < q ∧ p ≠ 0) ∧ IsSmooth p.natAbs = true) ∧
      IsSmooth q = true := by
    simpa [SUnitRatB, Bool.and_eq_true] using hunit
  obtain ⟨⟨⟨hq, hp⟩, hpabs⟩, hqabs⟩ := hunit'
  exact ⟨hq, hp, isSmooth_sound hpabs, isSmooth_sound hqabs, hne,
    isSmooth_sound hcomp⟩

/-! ## The 21 witnesses -/

/-- The 21 S-integral points of `P¹ ∖ {0,1,∞}` for `S = {2,3}`, as pairs
`(numerator, positive denominator)` in lowest terms. -/
def pts : List (Int × Nat) :=
  [ (-8, 1), (-3, 1), (-2, 1), (-1, 1), (-1, 2), (-1, 3), (-1, 8),
    (1, 9), (1, 4), (1, 3), (1, 2), (2, 3), (3, 4), (8, 9), (9, 8),
    (4, 3), (3, 2), (2, 1), (3, 1), (4, 1), (9, 1) ]

/-- `x` and `y` are textually different list entries with different values.
Cross-multiplication `x.1 * y.2 ≠ y.1 * x.2` is a closed `Int` identity, which
`decide` can reduce (unlike an equality of `Rat`s). -/
def distinctB (x y : Int × Nat) : Bool :=
  if x = y then true else decide (x.1 * (y.2 : Int) ≠ y.1 * (x.2 : Int))

/-- Boolean check that all listed rationals are S-integral. -/
def integralAll : Bool := pts.all fun x => SIntegralB x.1 x.2

/-- Boolean check that the listed rationals are pairwise distinct. -/
def distinctAll : Bool := pts.all fun x => pts.all fun y => distinctB x y

theorem integralAll_eq : integralAll = true := by decide
theorem distinctAll_eq : distinctAll = true := by decide

/-- Every listed rational is an S-integral point of `P¹ ∖ {0,1,∞}`. -/
theorem all_integral : ∀ x ∈ pts, SIntegral x.1 x.2 := by
  intro x hx
  exact (List.all_eq_true.mp integralAll_eq) x hx

/-- The listed rationals are pairwise distinct as rationals. -/
theorem all_distinct :
    ∀ x ∈ pts, ∀ y ∈ pts, x ≠ y → x.1 * (y.2 : Int) ≠ y.1 * (x.2 : Int) := by
  intro x hx y hy hxy
  have h1 := (List.all_eq_true.mp distinctAll_eq) x hx
  have h2 := (List.all_eq_true.mp h1) y hy
  by_cases hxy' : x = y
  · exact absurd hxy' hxy
  · unfold distinctB at h2
    rw [if_neg hxy'] at h2
    exact of_decide_eq_true h2

/-! ## The refutation -/

/-- There are exactly 21 listed witnesses. -/
theorem pts_length : pts.length = 21 := by decide

/-- **The conjecture's numerical claim fails.**  `12 < 21`, i.e. the number of
witnesses strictly exceeds the conjectured maximum `12`. -/
theorem twelve_lt_length : (12 : Nat) < pts.length := by decide

/-- **Conjecture `00000001737` is false.**  There are 21 pairwise-distinct
S-integral points of `P¹ ∖ {0,1,∞}` for `S = {2,3}`, so the maximum is at least
21, in particular strictly greater than 12. -/
theorem conjecture_00000001737_false :
    pts.length = 21 ∧
    (∀ x ∈ pts, SIntegral x.1 x.2) ∧
    (∀ x ∈ pts, ∀ y ∈ pts, x ≠ y → x.1 * (y.2 : Int) ≠ y.1 * (x.2 : Int)) ∧
    (12 : Nat) < pts.length :=
  ⟨by decide, all_integral, all_distinct, by decide⟩

/-- Packaged lower-bound form: there exists a set of more than 12 pairwise
distinct S-integral points of `P¹ ∖ {0,1,∞}` for `S = {2,3}`.  This is the
precise content of the refutation; it is a lower-bound witness, not an exact
count. -/
theorem more_than_twelve_points :
    ∃ n : Nat, 12 < n ∧
      ∃ pts : List (Int × Nat),
        pts.length = n ∧
        (∀ x ∈ pts, SIntegral x.1 x.2) ∧
        (∀ x ∈ pts, ∀ y ∈ pts, x ≠ y → x.1 * (y.2 : Int) ≠ y.1 * (x.2 : Int)) :=
  ⟨21, by decide, pts, pts_length, all_integral, all_distinct⟩

/-- The negation of the conjecture's count bound, stated as a `Prop`: it is
*not* the case that every set of S-integral points has at most 12 elements.
Instantiated by the 21 witnesses above. -/
theorem not_max_le_twelve :
    ¬ (∀ pts : List (Int × Nat),
        (∀ x ∈ pts, SIntegral x.1 x.2) →
        (∀ x ∈ pts, ∀ y ∈ pts, x ≠ y →
            x.1 * (y.2 : Int) ≠ y.1 * (x.2 : Int)) →
        pts.length ≤ 12) := by
  intro h
  have h12 := h pts all_integral all_distinct
  have hlen : pts.length = 21 := pts_length
  omega

end Tlmc1737
