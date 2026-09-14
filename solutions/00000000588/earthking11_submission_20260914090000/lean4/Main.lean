/-
  Disproof of conjecture `00000000588`.

  Conjecture (as filed):
    Definition: the type `t(S)` is the number of maximal Apéry elements.
    Conjecture: `t(⟨n, n+1, …, 2n-1⟩) = ⌈n/2⌉`.

  The conjecture is FALSE.  The counterexample is `n = 4`, `S = ⟨4,5,6,7⟩`.

  Since `4,5,6,7` are all generators and every `m ≥ 4` lies in `S`
  (`m ∈ [4,7]` is a generator; `m ≥ 8` gives `m = 4 + (m-4)`), we have
  `S = {0} ∪ [4,∞)`.  Hence the Apéry set with respect to the multiplicity `4` is

      Ap(S,4) = { s ∈ S : s - 4 ∉ S } = {0, 5, 6, 7} ,

  because `5-4 = 6-4 = 7-4` are `1,2,3 ∉ S`.  Under the Apéry order
  `x ≤_S y  ⟺  y - x ∈ S` the three elements `5,6,7` are pairwise
  incomparable (`6-5 = 7-6 = 1 ∉ S`, `7-5 = 2 ∉ S`), while `0` is not maximal
  (`0 ≤_S 5`).  So

      t(S) = 3   whereas   ⌈4/2⌉ = 2 .

  The true closed form is `t(⟨n,…,2n-1⟩) = n - 1`; it agrees with the
  conjecture only at `n = 2,3` (the instances `n = 3` and `n = 5` are also
  formalised below: `t(3) = 2 = ⌈3/2⌉` holds, `t(5) = 4 ≠ 3 = ⌈5/2⌉` fails).

  Core Lean only --- this file has **no imports at all** --- and no `sorry`.
-/

namespace Tlmc588

/-! ## The counterexample `n = 4`: `S = ⟨4,5,6,7⟩` -/

/-- `x` is a nonnegative integer combination of the generators `4,5,6,7`. -/
def inS (x : Nat) : Prop := ∃ a b c d : Nat, x = 4 * a + 5 * b + 6 * c + 7 * d

/-- The Apéry set of `S = ⟨4,5,6,7⟩` with respect to the multiplicity `4`. -/
def inAp (x : Nat) : Prop := x = 0 ∨ x = 5 ∨ x = 6 ∨ x = 7

/-- Apéry order, strict part: `x <_S y` iff `x < y` and `y - x ∈ S`. -/
def ltS (x y : Nat) : Prop := x < y ∧ inS (y - x)

/-- `x` is a maximal element of the Apéry set. -/
def isMax (x : Nat) : Prop := inAp x ∧ ∀ y, inAp y → ¬ ltS x y

/-- The list of maximal Apéry elements. -/
def maximals : List Nat := [5, 6, 7]

/-- `1,2,3` are gaps of `S`: they are not nonnegative combinations of `4,5,6,7`. -/
theorem not_inS_1 : ¬ inS 1 := by
  rintro ⟨a, b, c, d, h⟩; omega
theorem not_inS_2 : ¬ inS 2 := by
  rintro ⟨a, b, c, d, h⟩; omega
theorem not_inS_3 : ¬ inS 3 := by
  rintro ⟨a, b, c, d, h⟩; omega

theorem inS_0 : inS 0 := ⟨0, 0, 0, 0, rfl⟩
theorem inS_5 : inS 5 := ⟨0, 1, 0, 0, rfl⟩
theorem inS_6 : inS 6 := ⟨0, 0, 1, 0, rfl⟩
theorem inS_7 : inS 7 := ⟨0, 0, 0, 1, rfl⟩

/-- `0` is not maximal: `0 <_S 5`. -/
theorem not_isMax_0 : ¬ isMax 0 := by
  intro h
  have h5 : ltS 0 5 := ⟨by omega, inS_5⟩
  exact h.2 5 (Or.inr (Or.inl rfl)) h5

/-- `5` is maximal in the Apéry set. -/
theorem isMax_5 : isMax 5 := by
  refine ⟨Or.inr (Or.inl rfl), ?_⟩
  intro y hy hlt
  rcases hy with rfl | rfl | rfl | rfl
  · simp only [ltS] at hlt; omega
  · simp only [ltS] at hlt; omega
  · exact not_inS_1 hlt.2
  · exact not_inS_2 hlt.2

/-- `6` is maximal in the Apéry set. -/
theorem isMax_6 : isMax 6 := by
  refine ⟨Or.inr (Or.inr (Or.inl rfl)), ?_⟩
  intro y hy hlt
  rcases hy with rfl | rfl | rfl | rfl
  · simp only [ltS] at hlt; omega
  · simp only [ltS] at hlt; omega
  · simp only [ltS] at hlt; omega
  · exact not_inS_1 hlt.2

/-- `7` is maximal in the Apéry set. -/
theorem isMax_7 : isMax 7 := by
  refine ⟨Or.inr (Or.inr (Or.inr rfl)), ?_⟩
  intro y hy hlt
  rcases hy with rfl | rfl | rfl | rfl <;> (simp only [ltS] at hlt; omega)

/-- The type `t(S)`: the number of maximal Apéry elements, computed as the
length of the list of maximal elements. -/
def t : Nat := maximals.length

/-- The maximal Apéry elements are exactly `{5,6,7}`. -/
theorem maximals_correct :
    (∀ x, x ∈ maximals → isMax x) ∧ (∀ x, isMax x → x ∈ maximals) := by
  constructor
  · intro x hx
    have hx' : x = 5 ∨ x = 6 ∨ x = 7 := by
      simpa [maximals] using hx
    rcases hx' with rfl | rfl | rfl
    · exact isMax_5
    · exact isMax_6
    · exact isMax_7
  · intro x hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exact absurd hx not_isMax_0
    · decide
    · decide
    · decide

/-- The computed type is `3`. -/
theorem t_eq_3 : t = 3 := rfl

/-- The conjectured value `⌈4/2⌉ = 2`, and `3 ≠ 2`. -/
theorem t_ne_two : t ≠ 2 := by decide

/-- **Counterexample at `n = 4`.** `t(⟨4,5,6,7⟩) = 3` while `⌈4/2⌉ = 2`. -/
theorem counterexample_n4 : t = 3 ∧ t ≠ 2 := ⟨t_eq_3, t_ne_two⟩

/-! ## `n = 3`: the conjecture happens to hold (`t = 2 = ⌈3/2⌉`) -/

def inS3 (x : Nat) : Prop := ∃ a b c : Nat, x = 3 * a + 4 * b + 5 * c

/-- `Ap(⟨3,4,5⟩, 3) = {0,4,5}`. -/
def inAp3 (x : Nat) : Prop := x = 0 ∨ x = 4 ∨ x = 5

def ltS3 (x y : Nat) : Prop := x < y ∧ inS3 (y - x)
def isMax3 (x : Nat) : Prop := inAp3 x ∧ ∀ y, inAp3 y → ¬ ltS3 x y
def maximals3 : List Nat := [4, 5]

theorem not_inS3_1 : ¬ inS3 1 := by
  rintro ⟨a, b, c, h⟩; omega
theorem not_inS3_2 : ¬ inS3 2 := by
  rintro ⟨a, b, c, h⟩; omega

theorem not_isMax3_0 : ¬ isMax3 0 := by
  intro h
  have h4 : ltS3 0 4 := ⟨by omega, ⟨0, 1, 0, rfl⟩⟩
  exact h.2 4 (Or.inr (Or.inl rfl)) h4

theorem isMax3_4 : isMax3 4 := by
  refine ⟨Or.inr (Or.inl rfl), ?_⟩
  intro y hy hlt
  rcases hy with rfl | rfl | rfl
  · simp only [ltS3] at hlt; omega
  · simp only [ltS3] at hlt; omega
  · exact not_inS3_1 hlt.2

theorem isMax3_5 : isMax3 5 := by
  refine ⟨Or.inr (Or.inr rfl), ?_⟩
  intro y hy hlt
  rcases hy with rfl | rfl | rfl <;> (simp only [ltS3] at hlt; omega)

def t3 : Nat := maximals3.length

theorem maximals3_correct :
    (∀ x, x ∈ maximals3 → isMax3 x) ∧ (∀ x, isMax3 x → x ∈ maximals3) := by
  constructor
  · intro x hx
    have hx' : x = 4 ∨ x = 5 := by simpa [maximals3] using hx
    rcases hx' with rfl | rfl
    · exact isMax3_4
    · exact isMax3_5
  · intro x hx
    rcases hx.1 with rfl | rfl | rfl
    · exact absurd hx not_isMax3_0
    · decide
    · decide

theorem t3_eq_two : t3 = 2 := rfl

/-- At `n = 3` the conjecture is correct: `t = 2 = ⌈3/2⌉`. -/
theorem conjecture_holds_n3 : t3 = 2 := t3_eq_two

/-! ## `n = 5`: the conjecture fails again (`t = 4 ≠ 3 = ⌈5/2⌉`) -/

def inS5 (x : Nat) : Prop := ∃ a b c d e : Nat, x = 5 * a + 6 * b + 7 * c + 8 * d + 9 * e

/-- `Ap(⟨5,6,7,8,9⟩, 5) = {0,6,7,8,9}`. -/
def inAp5 (x : Nat) : Prop := x = 0 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9

def ltS5 (x y : Nat) : Prop := x < y ∧ inS5 (y - x)
def isMax5 (x : Nat) : Prop := inAp5 x ∧ ∀ y, inAp5 y → ¬ ltS5 x y
def maximals5 : List Nat := [6, 7, 8, 9]

theorem not_inS5_1 : ¬ inS5 1 := by
  rintro ⟨a, b, c, d, e, h⟩; omega
theorem not_inS5_2 : ¬ inS5 2 := by
  rintro ⟨a, b, c, d, e, h⟩; omega
theorem not_inS5_3 : ¬ inS5 3 := by
  rintro ⟨a, b, c, d, e, h⟩; omega
theorem not_inS5_4 : ¬ inS5 4 := by
  rintro ⟨a, b, c, d, e, h⟩; omega

theorem not_isMax5_0 : ¬ isMax5 0 := by
  intro h
  have h6 : ltS5 0 6 := ⟨by omega, ⟨0, 1, 0, 0, 0, rfl⟩⟩
  exact h.2 6 (Or.inr (Or.inl rfl)) h6

theorem isMax5_6 : isMax5 6 := by
  refine ⟨Or.inr (Or.inl rfl), ?_⟩
  intro y hy hlt
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · simp only [ltS5] at hlt; omega
  · simp only [ltS5] at hlt; omega
  · exact not_inS5_1 hlt.2
  · exact not_inS5_2 hlt.2
  · exact not_inS5_3 hlt.2

theorem isMax5_7 : isMax5 7 := by
  refine ⟨Or.inr (Or.inr (Or.inl rfl)), ?_⟩
  intro y hy hlt
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · simp only [ltS5] at hlt; omega
  · simp only [ltS5] at hlt; omega
  · simp only [ltS5] at hlt; omega
  · exact not_inS5_1 hlt.2
  · exact not_inS5_2 hlt.2

theorem isMax5_8 : isMax5 8 := by
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
  intro y hy hlt
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · simp only [ltS5] at hlt; omega
  · simp only [ltS5] at hlt; omega
  · simp only [ltS5] at hlt; omega
  · simp only [ltS5] at hlt; omega
  · exact not_inS5_1 hlt.2

theorem isMax5_9 : isMax5 9 := by
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), ?_⟩
  intro y hy hlt
  rcases hy with rfl | rfl | rfl | rfl | rfl <;> (simp only [ltS5] at hlt; omega)

def t5 : Nat := maximals5.length

theorem maximals5_correct :
    (∀ x, x ∈ maximals5 → isMax5 x) ∧ (∀ x, isMax5 x → x ∈ maximals5) := by
  constructor
  · intro x hx
    have hx' : x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 := by simpa [maximals5] using hx
    rcases hx' with rfl | rfl | rfl | rfl
    · exact isMax5_6
    · exact isMax5_7
    · exact isMax5_8
    · exact isMax5_9
  · intro x hx
    rcases hx.1 with rfl | rfl | rfl | rfl | rfl
    · exact absurd hx not_isMax5_0
    · decide
    · decide
    · decide
    · decide

theorem t5_eq_four : t5 = 4 := rfl
theorem t5_ne_three : t5 ≠ 3 := by decide

/-- At `n = 5` the conjecture fails again: `t = 4` but `⌈5/2⌉ = 3`. -/
theorem counterexample_n5 : t5 = 4 ∧ t5 ≠ 3 := ⟨t5_eq_four, t5_ne_three⟩

end Tlmc588
