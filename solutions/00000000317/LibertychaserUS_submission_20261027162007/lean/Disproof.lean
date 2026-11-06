import Mathlib

/-!
# Disproof of Conjecture 00000000317 (The Last Math Competition)

The conjecture claims (i) Freiman's constant `c_F` belongs to the Lagrange spectrum `L`
but not to the Markov spectrum `M`, and (ii) among the first 20 partial quotients of `c_F`
the digit 1 appears exactly 8 times.

We refute the conjunction through clause (ii), which is a finite exact computation:
the regular continued fraction of `c_F` begins
`[4; 1, 1, 8, 2, 14, 2, 2, 1, 12, 117, 1, 1, 7, 16, 35, 6, 2, 7, 2, 1, ...]`,
so the digit 1 occurs 5 times among `a_0, …, a_19` and
6 times among `a_1, …, a_20` — never 8.
Clause (i) is left as an abstract proposition: it is false too (`L ⊆ M` is a theorem),
but the refutation of the conjunction does not need it, so the spectra are not formalised.

All partial quotients are obtained by the standard Gauss-map recursion, with every tail
kept exactly in the form `(p + r·√462)/s` with explicit integers.
-/

open Real

namespace Freiman

/-- Freiman's constant `c_F`, the right end point of the maximal gap `(2√2, c_F)` of the
Markov spectrum, in its standard closed form (Freiman 1975):
`c_F = (2221564096 + 283748·√462) / 491993569 ≈ 4.5278295661…`. -/
noncomputable def freimanConstant : ℝ :=
  (2221564096 + 283748 * Real.sqrt 462) / 491993569

/-- The Gauss-map orbit of a real number `x`: `cfState x 0 = x` and
`cfState x (n+1) = 1 / fract (cfState x n)`. This is the standard recursion producing the
regular continued fraction of `x`: `cfState x n` is the `n`-th complete quotient. -/
noncomputable def cfState (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => 1 / Int.fract (cfState x n)

/-- The `n`-th partial quotient `a_n` of the regular continued fraction
`x = [a_0; a_1, a_2, …]`, defined as the integer part of the `n`-th complete quotient. -/
noncomputable def pq (x : ℝ) (n : ℕ) : ℤ := ⌊cfState x n⌋

theorem cfState_zero (x : ℝ) : cfState x 0 = x := rfl

theorem cfState_succ (x : ℝ) (n : ℕ) : cfState x (n + 1) = 1 / Int.fract (cfState x n) := rfl

/-! ### Arithmetic of `√462` -/

theorem sq_sqrt462 : Real.sqrt 462 ^ 2 = 462 := Real.sq_sqrt (by norm_num)

/-- Lower rational bound on `√462`, obtained from `5373546315051^2 < 462 · 250000000000^2`. -/
theorem sqrt462_gt : (5373546315051 : ℝ) / 250000000000 < Real.sqrt 462 :=
  (Real.lt_sqrt (by norm_num)).2 (by norm_num)

/-- Upper rational bound on `√462`, obtained from `462 · 200000000000^2 < 4298837052041^2`. -/
theorem sqrt462_lt : Real.sqrt 462 < (4298837052041 : ℝ) / 200000000000 :=
  (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-! ### Generic lemmas for one step of the Gauss map on `(p + r√462)/s` -/

/-- Floor of a number of the form `(p + r√462)/s`, given rational bracketing. -/
theorem floor_of_bounds (p r s : ℝ) (a : ℤ) (hs : 0 < s)
    (h₁ : (a : ℝ) * s ≤ p + r * Real.sqrt 462)
    (h₂ : p + r * Real.sqrt 462 < ((a : ℝ) + 1) * s) :
    ⌊(p + r * Real.sqrt 462) / s⌋ = a := by
  rw [Int.floor_eq_iff, le_div_iff₀ hs, div_lt_iff₀ hs]
  exact ⟨h₁, h₂⟩

/-- One Gauss-map step. If the `n`-th complete quotient is `(p + r√462)/s` with integer part
`a`, then the next one is `(P + R√462)/S`, where `g·P = s(p − a s)`, `g·R = −s r`,
`g·S = (p − a s)² − 462 r²` for some non-zero common factor `g` (used to cancel a gcd). -/
theorem gauss_step (x : ℝ) (n : ℕ) (p r s P R S g : ℝ) (a : ℤ)
    (hx : cfState x n = (p + r * Real.sqrt 462) / s) (hs : s ≠ 0)
    (ha : ⌊cfState x n⌋ = a) (hg : g ≠ 0) (hS : S ≠ 0)
    (hP : g * P = s * (p - a * s)) (hR : g * R = -(s * r))
    (hSS : g * S = (p - a * s) ^ 2 - 462 * r ^ 2) :
    cfState x (n + 1) = (P + R * Real.sqrt 462) / S := by
  have hq := sq_sqrt462
  set q := Real.sqrt 462 with hqdef
  rw [cfState_succ, Int.fract, ha, hx]
  have hfr : (p + r * q) / s - (a : ℝ) = ((p - a * s) + r * q) / s := by
    field_simp
    ring
  rw [hfr]
  have hne : (p - a * s) + r * q ≠ 0 := by
    intro h0
    apply hS
    apply mul_left_cancel₀ hg
    rw [hSS, mul_zero]
    have : ((p - a * s) + r * q) * ((p - a * s) - r * q) = 0 := by rw [h0, zero_mul]
    linear_combination this + r ^ 2 * hq
  rw [one_div_div, div_eq_div_iff hne hS]
  apply mul_left_cancel₀ hg
  linear_combination s * hSS - ((p - a * s) + r * q) * hP - q * ((p - a * s) + r * q) * hR
    + s * r ^ 2 * hq

/-! ### The orbit of Freiman's constant, step by step -/

theorem state_0 : cfState freimanConstant 0 = (2221564096 + 283748 * Real.sqrt 462) / 491993569 := rfl

theorem pq_0 : pq freimanConstant 0 = 4 := by
  unfold pq
  rw [state_0]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_1 : cfState freimanConstant 1 = (63397455 + (-70937) * Real.sqrt 462) / 32658252 :=
  gauss_step freimanConstant 0 _ _ _ _ _ _ 1967974276 _ state_0 (by norm_num) pq_0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_1 : pq freimanConstant 1 = 1 := by
  unfold pq
  rw [state_1]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_2 : cfState freimanConstant 2 = (122956812 + 283748 * Real.sqrt 462) / 115446937 :=
  gauss_step freimanConstant 1 _ _ _ _ _ _ 8164563 _ state_1 (by norm_num) pq_1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_2 : pq freimanConstant 2 = 1 := by
  unfold pq
  rw [state_2]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_3 : cfState freimanConstant 3 = (7509875 + (-283748) * Real.sqrt 462) / 166321 :=
  gauss_step freimanConstant 2 _ _ _ _ _ _ 115446937 _ state_2 (by norm_num) pq_2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_3 : pq freimanConstant 3 = 8 := by
  unfold pq
  rw [state_3]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_4 : cfState freimanConstant 4 = (6179307 + 283748 * Real.sqrt 462) / 5933481 :=
  gauss_step freimanConstant 3 _ _ _ _ _ _ 166321 _ state_3 (by norm_num) pq_3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_4 : pq freimanConstant 4 = 2 := by
  unfold pq
  rw [state_4]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_5 : cfState freimanConstant 5 = (5687655 + 283748 * Real.sqrt 462) / 816983 :=
  gauss_step freimanConstant 4 _ _ _ _ _ _ (-5933481) _ state_4 (by norm_num) pq_4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_5 : pq freimanConstant 5 = 14 := by
  unfold pq
  rw [state_5]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_6 : cfState freimanConstant 6 = (5750107 + 283748 * Real.sqrt 462) / 5059153 :=
  gauss_step freimanConstant 5 _ _ _ _ _ _ (-816983) _ state_5 (by norm_num) pq_5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_6 : pq freimanConstant 6 = 2 := by
  unfold pq
  rw [state_6]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_7 : cfState freimanConstant 7 = (4368199 + 283748 * Real.sqrt 462) / 3580799 :=
  gauss_step freimanConstant 6 _ _ _ _ _ _ (-5059153) _ state_6 (by norm_num) pq_6
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_7 : pq freimanConstant 7 = 2 := by
  unfold pq
  rw [state_7]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_8 : cfState freimanConstant 8 = (2793399 + 283748 * Real.sqrt 462) / 8208753 :=
  gauss_step freimanConstant 7 _ _ _ _ _ _ (-3580799) _ state_7 (by norm_num) pq_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_8 : pq freimanConstant 8 = 1 := by
  unfold pq
  rw [state_8]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_9 : cfState freimanConstant 9 = (2707677 + 141874 * Real.sqrt 462) / 479422 :=
  gauss_step freimanConstant 8 _ _ _ _ _ _ (-16417506) _ state_8 (by norm_num) pq_8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_9 : pq freimanConstant 9 = 12 := by
  unfold pq
  rw [state_9]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_10 : cfState freimanConstant 10 = (6090774 + 283748 * Real.sqrt 462) / 103713 :=
  gauss_step freimanConstant 9 _ _ _ _ _ _ (-239711) _ state_9 (by norm_num) pq_9
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_10 : pq freimanConstant 10 = 117 := by
  unfold pq
  rw [state_10]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_11 : cfState freimanConstant 11 = (6043647 + 283748 * Real.sqrt 462) / 6472703 :=
  gauss_step freimanConstant 10 _ _ _ _ _ _ (-103713) _ state_10 (by norm_num) pq_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_11 : pq freimanConstant 11 = 1 := by
  unfold pq
  rw [state_11]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_12 : cfState freimanConstant 12 = (107264 + 70937 * Real.sqrt 462) / 1429576 :=
  gauss_step freimanConstant 11 _ _ _ _ _ _ (-25890812) _ state_11 (by norm_num) pq_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_12 : pq freimanConstant 12 = 1 := by
  unfold pq
  rw [state_12]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_13 : cfState freimanConstant 13 = (5289248 + 283748 * Real.sqrt 462) / 1612511 :=
  gauss_step freimanConstant 12 _ _ _ _ _ _ (-357394) _ state_12 (by norm_num) pq_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_13 : pq freimanConstant 13 = 7 := by
  unfold pq
  rw [state_13]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_14 : cfState freimanConstant 14 = (5998329 + 283748 * Real.sqrt 462) / 754737 :=
  gauss_step freimanConstant 13 _ _ _ _ _ _ (-1612511) _ state_13 (by norm_num) pq_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_14 : pq freimanConstant 14 = 16 := by
  unfold pq
  rw [state_14]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_15 : cfState freimanConstant 15 = (6077463 + 283748 * Real.sqrt 462) / 346367 :=
  gauss_step freimanConstant 14 _ _ _ _ _ _ (-754737) _ state_14 (by norm_num) pq_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_15 : pq freimanConstant 15 = 35 := by
  unfold pq
  rw [state_15]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_16 : cfState freimanConstant 16 = (3022691 + 141874 * Real.sqrt 462) / 938786 :=
  gauss_step freimanConstant 15 _ _ _ _ _ _ (-692734) _ state_15 (by norm_num) pq_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_16 : pq freimanConstant 16 = 6 := by
  unfold pq
  rw [state_16]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_17 : cfState freimanConstant 17 = (5220050 + 283748 * Real.sqrt 462) / 5298359 :=
  gauss_step freimanConstant 16 _ _ _ _ _ _ (-469393) _ state_16 (by norm_num) pq_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_17 : pq freimanConstant 17 = 2 := by
  unfold pq
  rw [state_17]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_18 : cfState freimanConstant 18 = (1344167 + 70937 * Real.sqrt 462) / 391084 :=
  gauss_step freimanConstant 17 _ _ _ _ _ _ (-21193436) _ state_17 (by norm_num) pq_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_18 : pq freimanConstant 18 = 7 := by
  unfold pq
  rw [state_18]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_19 : cfState freimanConstant 19 = (5573684 + 283748 * Real.sqrt 462) / 3919247 :=
  gauss_step freimanConstant 18 _ _ _ _ _ _ (-97771) _ state_18 (by norm_num) pq_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_19 : pq freimanConstant 19 = 2 := by
  unfold pq
  rw [state_19]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

theorem state_20 : cfState freimanConstant 20 = (1132405 + 141874 * Real.sqrt 462) / 4091042 :=
  gauss_step freimanConstant 19 _ _ _ _ _ _ (-7838494) _ state_19 (by norm_num) pq_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem pq_20 : pq freimanConstant 20 = 1 := by
  unfold pq
  rw [state_20]
  have hL := sqrt462_gt
  have hU := sqrt462_lt
  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

/-! ### Counting the digit 1 -/

/-- Among the first 20 partial quotients `a_0, …, a_19` of Freiman's constant, the digit 1
occurs exactly 5 times (at indices 1, 2, 8, 11, 12). -/
theorem count_ones_first20 :
    ((Finset.range 20).filter (fun n => pq freimanConstant n = 1)).card = 5 := by
  simp only [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_zero,
    pq_0, pq_1, pq_2, pq_3, pq_4, pq_5, pq_6, pq_7, pq_8, pq_9, pq_10, pq_11, pq_12, pq_13, pq_14, pq_15, pq_16, pq_17, pq_18, pq_19]
  norm_num

/-- Variant indexing: among `a_1, …, a_20` the digit 1 occurs exactly 6 times. -/
theorem count_ones_1_to_20 :
    ((Finset.range 20).filter (fun n => pq freimanConstant (n + 1) = 1)).card = 6 := by
  simp only [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [pq_1, pq_2, pq_3, pq_4, pq_5, pq_6, pq_7, pq_8, pq_9, pq_10, pq_11, pq_12, pq_13, pq_14, pq_15, pq_16, pq_17, pq_18, pq_19, pq_20]

/-! ### Main theorems -/

/-- **Conjecture 00000000317 is false.** The first clause ("`c_F ∈ L` and `c_F ∉ M`") is
abstracted as an arbitrary proposition `InLNotM`: the refutation of the conjunction does not
depend on it, because the second clause ("the digit 1 appears exactly 8 times among the first
20 partial quotients of `c_F`") is false — the digit 1 appears exactly 5 times. -/
theorem conjecture_00000000317_fails (InLNotM : Prop) :
    ¬ (InLNotM ∧ ((Finset.range 20).filter (fun n => pq freimanConstant n = 1)).card = 8) := by
  rintro ⟨-, h⟩
  rw [count_ones_first20] at h
  norm_num at h

/-- Same conclusion if "the first 20 partial quotients" is read as `a_1, …, a_20`
(the digit 1 then appears exactly 6 times, still not 8). -/
theorem conjecture_00000000317_fails' (InLNotM : Prop) :
    ¬ (InLNotM ∧ ((Finset.range 20).filter (fun n => pq freimanConstant (n + 1) = 1)).card = 8) := by
  rintro ⟨-, h⟩
  rw [count_ones_1_to_20] at h
  norm_num at h

end Freiman

#print axioms Freiman.count_ones_first20
#print axioms Freiman.count_ones_1_to_20
#print axioms Freiman.conjecture_00000000317_fails
#print axioms Freiman.conjecture_00000000317_fails'
