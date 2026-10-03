import Mathlib

/-!
# Conjecture 00000007780: four common preperiodic points of `z² − 1` and `z²`

A point `x` is *preperiodic* for a map `F` if its forward orbit is finite, i.e. some iterate
`F^[m] x` is periodic. Conjecture 00000007780 claims that for every quadratic polynomial `f`
and every power map `z ↦ z^d`, acting on `P¹(Q̄)`, the set of points preperiodic for both
maps has at most `2·v(d)` elements, `v(d)` being the number of prime factors of `d`; and
that if `f` is neither Chebyshev nor monomial, this set has at most `3` elements.

Take `f(z) = z² − 1` and `d = 2`, so `2·v(2) = 2`. The four points `0, 1, −1, ∞` are
preperiodic for both maps:

* under `f`: `0 ↦ −1 ↦ 0`, `1 ↦ 0`, and `∞` is fixed;
* under `z²`: `0`, `1` and `∞` are fixed, and `−1 ↦ 1`.

So the common preperiodic set has at least `4 > 2` elements, refuting the first claim.
Moreover `f` is neither monomial nor Chebyshev (it is not affinely conjugate to `z²` or to
`±(2z² − 1)`), and `4 > 3`, refuting the second claim as well.

`P¹(Q̄)` is modelled as `Option Q̄` with `none = ∞`; a polynomial map acts on it by fixing `∞`.
-/

namespace Submission00000007780

/-- An algebraic closure `Q̄` of `ℚ`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- The projective line `P¹(Q̄) = Q̄ ∪ {∞}`, with `none` playing the role of `∞`. -/
abbrev P1 := Option Qbar

/-- A polynomial map `g : Q̄ → Q̄` (of positive degree) extended to `P¹(Q̄)` by `∞ ↦ ∞`. -/
def onP1 (g : Qbar → Qbar) : P1 → P1 := Option.map g

/-- `x` is preperiodic for `F`: some iterate `F^[m] x` is periodic (Mathlib's
`Function.IsPeriodicPt`), i.e. the forward orbit of `x` is finite. -/
def IsPreperiodic {X : Type*} (F : X → X) (x : X) : Prop :=
  ∃ m n : ℕ, 0 < n ∧ Function.IsPeriodicPt F n (F^[m] x)

/-- The quadratic polynomial map `z ↦ a z² + b z + c` (with `a ≠ 0` when quadratic). -/
noncomputable def quad (a b c : Qbar) (z : Qbar) : Qbar := a * z ^ 2 + b * z + c

/-- The power map `z ↦ z^d`. -/
noncomputable def powMap (d : ℕ) (z : Qbar) : Qbar := z ^ d

/-- The common preperiodic set of `f = quad a b c` and `z ↦ z^d` on `P¹(Q̄)`. -/
def commonPrep (a b c : Qbar) (d : ℕ) : Set P1 :=
  {x | IsPreperiodic (onP1 (quad a b c)) x ∧ IsPreperiodic (onP1 (powMap d)) x}

/-- `f` is monomial: affinely conjugate to `z ↦ z²`, i.e. `φ ∘ f = (·)² ∘ φ` for some affine
`φ(z) = α z + β` with `α ≠ 0`. -/
def IsMonomial (a b c : Qbar) : Prop :=
  ∃ α β : Qbar, α ≠ 0 ∧ ∀ z, α * quad a b c z + β = (α * z + β) ^ 2

/-- `f` is Chebyshev: affinely conjugate to `T₂(z) = 2z² − 1` or to `−T₂`. -/
def IsChebyshev (a b c : Qbar) : Prop :=
  ∃ α β : Qbar, α ≠ 0 ∧ ((∀ z, α * quad a b c z + β = 2 * (α * z + β) ^ 2 - 1) ∨
    (∀ z, α * quad a b c z + β = -(2 * (α * z + β) ^ 2 - 1)))

/-- First claim, with `v(d) = ω(d)` the number of distinct prime factors: for every quadratic
polynomial `f` and every `d ≥ 2`, the common preperiodic set has at most `2·ω(d)` points. -/
def Claim1 : Prop :=
  ∀ a b c : Qbar, a ≠ 0 → ∀ d : ℕ, 2 ≤ d → (commonPrep a b c d).encard ≤
    2 * (ArithmeticFunction.cardDistinctFactors d : ℕ∞)

/-- First claim, with `v(d) = Ω(d)` the number of prime factors counted with multiplicity. -/
def Claim1' : Prop :=
  ∀ a b c : Qbar, a ≠ 0 → ∀ d : ℕ, 2 ≤ d → (commonPrep a b c d).encard ≤
    2 * (ArithmeticFunction.cardFactors d : ℕ∞)

/-- Second claim (its counting part): if `f` is neither Chebyshev nor monomial, the common
preperiodic set has at most `3` points. -/
def Claim2 : Prop :=
  ∀ a b c : Qbar, a ≠ 0 → ¬ IsChebyshev a b c → ¬ IsMonomial a b c →
    ∀ d : ℕ, 2 ≤ d → (commonPrep a b c d).encard ≤ 3

/-! ### `f(z) = z² − 1` and `z²` -/

/-- `f(z) = 1·z² + 0·z + (−1)`. -/
noncomputable abbrev f : Qbar → Qbar := quad 1 0 (-1)

theorem f_apply (z : Qbar) : f z = z ^ 2 - 1 := by
  simp [quad]
  ring

theorem preperiodic_infty (g : Qbar → Qbar) : IsPreperiodic (onP1 g) none :=
  ⟨0, 1, one_pos, by simp [Function.IsPeriodicPt, Function.IsFixedPt, onP1]⟩

theorem iterate_onP1 (g : Qbar → Qbar) (k : ℕ) (y : Qbar) :
    (onP1 g)^[k] (some y) = some (g^[k] y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, onP1, Option.map_some, ← ih]

/-- `some x` is preperiodic for `onP1 g` as soon as `g^[n] (g^[m] x) = g^[m] x` with `n > 0`. -/
theorem preperiodic_some (g : Qbar → Qbar) (x : Qbar) (m n : ℕ) (hn : 0 < n)
    (h : g^[n] (g^[m] x) = g^[m] x) : IsPreperiodic (onP1 g) (some x) :=
  ⟨m, n, hn, by simp only [Function.IsPeriodicPt, Function.IsFixedPt, iterate_onP1, h]⟩

theorem one_ne_neg_one : (1 : Qbar) ≠ -1 := by
  intro h
  have : (2 : Qbar) = 0 := by linear_combination h
  exact two_ne_zero this

/-- The four common preperiodic points `0, 1, −1, ∞`. -/
theorem subset_commonPrep :
    ({some 0, some 1, some (-1), none} : Set P1) ⊆ commonPrep 1 0 (-1) 2 := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · -- `0 ↦ −1 ↦ 0` under `f`, and `0` is fixed by `z²`
    exact ⟨preperiodic_some _ _ 0 2 two_pos (by norm_num [quad]),
      preperiodic_some _ _ 0 1 one_pos (by norm_num [powMap])⟩
  · -- `1 ↦ 0`, then `0 ↦ −1 ↦ 0` under `f`; `1` is fixed by `z²`
    exact ⟨preperiodic_some _ _ 1 2 two_pos (by norm_num [quad]),
      preperiodic_some _ _ 0 1 one_pos (by norm_num [powMap])⟩
  · -- `−1 ↦ 0 ↦ −1` under `f`; `−1 ↦ 1 ↦ 1` under `z²`
    exact ⟨preperiodic_some _ _ 0 2 two_pos (by norm_num [quad]),
      preperiodic_some _ _ 1 1 one_pos (by norm_num [powMap])⟩
  · exact ⟨preperiodic_infty _, preperiodic_infty _⟩

/-- The four points are distinct, so the common preperiodic set has at least `4` points. -/
theorem four_le_encard : 4 ≤ (commonPrep 1 0 (-1) 2).encard := by
  have hcard : ({some 0, some 1, some (-1), none} : Set P1).encard = 4 := by
    rw [Set.encard_insert_of_notMem, Set.encard_insert_of_notMem, Set.encard_insert_of_notMem,
      Set.encard_singleton]
    · norm_num
    all_goals simp [one_ne_neg_one]
  rw [← hcard]
  exact Set.encard_le_encard subset_commonPrep

/-- From `k * α * β = 0` with `k ≠ 0` and `α ≠ 0`, conclude `β = 0`. -/
theorem eq_zero_of_mul {k α β : Qbar} (hk : k ≠ 0) (hα : α ≠ 0) (h : k * α * β = 0) :
    β = 0 :=
  (mul_eq_zero.1 h).resolve_left (mul_ne_zero hk hα)

/-- `z² − 1` is not monomial. -/
theorem not_isMonomial : ¬ IsMonomial 1 0 (-1) := by
  rintro ⟨α, β, hα, h⟩
  have h1 := h 1
  have hm1 := h (-1)
  simp only [quad] at h1 hm1
  have hβ : β = 0 := eq_zero_of_mul (k := 4) (by norm_num) hα (by linear_combination hm1 - h1)
  subst hβ
  exact hα (pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination -h1))

/-- `z² − 1` is not Chebyshev. -/
theorem not_isChebyshev : ¬ IsChebyshev 1 0 (-1) := by
  rintro ⟨α, β, hα, h | h⟩
  · have h0 := h 0
    have h1 := h 1
    have hm1 := h (-1)
    simp only [quad] at h0 h1 hm1
    have hβ : β = 0 := eq_zero_of_mul (by norm_num) hα (k := 8) (by linear_combination hm1 - h1)
    subst hβ
    have hα1 : α = 1 := by linear_combination -h0
    subst hα1
    exact one_ne_zero (by linear_combination -h1 : (1 : Qbar) = 0)
  · have h0 := h 0
    have h1 := h 1
    have hm1 := h (-1)
    simp only [quad] at h0 h1 hm1
    have hβ : β = 0 := eq_zero_of_mul (by norm_num) hα (k := 8) (by linear_combination h1 - hm1)
    subst hβ
    have hα1 : α = -1 := by linear_combination -h0
    subst hα1
    exact one_ne_zero (by linear_combination h1 : (1 : Qbar) = 0)

/-- **The first claim fails** (with `v(d) = ω(d)`): `2·ω(2) = 2 < 4`. -/
theorem not_claim1 : ¬ Claim1 := by
  intro h
  have h2 := h 1 0 (-1) one_ne_zero 2 le_rfl
  rw [ArithmeticFunction.cardDistinctFactors_apply_prime Nat.prime_two] at h2
  have := four_le_encard.trans h2
  norm_num at this

/-- **The first claim fails** (with `v(d) = Ω(d)`): `2·Ω(2) = 2 < 4`. -/
theorem not_claim1' : ¬ Claim1' := by
  intro h
  have h2 := h 1 0 (-1) one_ne_zero 2 le_rfl
  rw [ArithmeticFunction.cardFactors_apply_prime Nat.prime_two] at h2
  have := four_le_encard.trans h2
  norm_num at this

/-- **The second claim fails**: `z² − 1` is neither Chebyshev nor monomial, yet the common
preperiodic set with `z²` has `4 > 3` points. -/
theorem not_claim2 : ¬ Claim2 := by
  intro h
  have h3 := h 1 0 (-1) one_ne_zero not_isChebyshev not_isMonomial 2 le_rfl
  have := four_le_encard.trans h3
  norm_num at this

/-- **Conjecture 00000007780 is false**: both of its claims fail. -/
theorem conjecture_00000007780_false : ¬ (Claim1 ∨ Claim1') ∧ ¬ Claim2 :=
  ⟨fun h => h.elim not_claim1 not_claim1', not_claim2⟩

end Submission00000007780

#print axioms Submission00000007780.conjecture_00000007780_false
